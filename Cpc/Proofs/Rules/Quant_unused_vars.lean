import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def qterm (Q x F : Term) : Term :=
  Term.Apply (Term.Apply Q x) F

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def qexists (x F : Term) : Term :=
  qterm (Term.UOp UserOp.exists) x F

private def qforall (x F : Term) : Term :=
  qterm (Term.UOp UserOp.forall) x F

private theorem eo_to_smt_exists_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qexists x F) =
      __eo_to_smt_exists x (__eo_to_smt F) := by
  unfold qexists qterm
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem eo_to_smt_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qforall x F) =
      SmtTerm.not (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) := by
  unfold qforall qterm
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem eo_to_smt_quantifiers_skolemize_non_forall_none
    (F n : Term)
    (hNotForall : ¬ ∃ binders body, F = qforall binders body) :
    __eo_to_smt
        (Term.UOp2 UserOp2._at_quantifiers_skolemize F n) =
      SmtTerm.None := by
  cases F <;> try rfl
  case Apply f body =>
    cases f <;> try rfl
    case Apply q binders =>
      cases q <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        case «forall» =>
          exact False.elim (hNotForall ⟨binders, body, rfl⟩)

private theorem eo_to_smt_quantifiers_skolemize_invalid_nat_none
    (binders body n : Term)
    (hNat : __eo_to_smt_nat_is_valid n = false) :
    __eo_to_smt
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (qforall binders body) n) =
      SmtTerm.None := by
  change
    native_ite (__eo_to_smt_nat_is_valid n)
        (__eo_to_smt_quantifiers_skolemize
          (__eo_to_smt_exists binders (SmtTerm.not (__eo_to_smt body)))
          (__eo_to_smt_nat n))
        SmtTerm.None =
      SmtTerm.None
  simp [hNat, native_ite]

private theorem eo_to_smt_quantifiers_skolemize_non_exists_none
    (F : SmtTerm) (n : native_Nat)
    (hNotExists : ¬ ∃ s T body, F = SmtTerm.exists s T body) :
    __eo_to_smt_quantifiers_skolemize F n = SmtTerm.None := by
  cases F <;> try rfl
  case «exists» s T body =>
    exact False.elim (hNotExists ⟨s, T, body, rfl⟩)

private theorem eo_to_smt_quantifiers_skolemize_forall_non_exists_none
    (binders body n : Term)
    (hNat : __eo_to_smt_nat_is_valid n = true)
    (hNotExists :
      ¬ ∃ s T F,
        __eo_to_smt_exists binders (SmtTerm.not (__eo_to_smt body)) =
          SmtTerm.exists s T F) :
    __eo_to_smt
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (qforall binders body) n) =
      SmtTerm.None := by
  change
    native_ite (__eo_to_smt_nat_is_valid n)
        (__eo_to_smt_quantifiers_skolemize
          (__eo_to_smt_exists binders (SmtTerm.not (__eo_to_smt body)))
          (__eo_to_smt_nat n))
        SmtTerm.None =
      SmtTerm.None
  simp [hNat, native_ite,
    eo_to_smt_quantifiers_skolemize_non_exists_none
      (__eo_to_smt_exists binders (SmtTerm.not (__eo_to_smt body)))
      (__eo_to_smt_nat n) hNotExists]

private theorem eo_to_smt_re_unfold_pos_component_invalid_nat_none
    (s r n : Term)
    (hNat : __eo_to_smt_nat_is_valid n = false) :
    __eo_to_smt
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r n) =
      SmtTerm.None := by
  change
    native_ite (__eo_to_smt_nat_is_valid n)
        (__eo_to_smt_re_unfold_pos_component
          (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat n))
        SmtTerm.None =
      SmtTerm.None
  simp [hNat, native_ite]

private theorem eo_to_smt_re_unfold_pos_component_non_concat_none
    (s r n : Term)
    (hNat : __eo_to_smt_nat_is_valid n = true)
    (hNotConcat : ¬ ∃ r1 r2, __eo_to_smt r = SmtTerm.re_concat r1 r2) :
    __eo_to_smt
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r n) =
      SmtTerm.None := by
  have hCore :
      __eo_to_smt_re_unfold_pos_component
          (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat n) =
        SmtTerm.None := by
    cases hR : __eo_to_smt r <;> try rfl
    case re_concat r1 r2 =>
      exact False.elim (hNotConcat ⟨r1, r2, hR⟩)
  change
    native_ite (__eo_to_smt_nat_is_valid n)
        (__eo_to_smt_re_unfold_pos_component
          (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat n))
        SmtTerm.None =
      SmtTerm.None
  simp [hNat, native_ite, hCore]

private theorem smtx_typeof_none_ne_bool :
    __smtx_typeof SmtTerm.None ≠ SmtType.Bool :=
  TranslationProofs.smtx_typeof_none_ne_bool

private theorem smtx_typeof_not_arg_of_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  cases h : __smtx_typeof t <;>
    simp [h, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_not_bool_of_arg_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  cases h : __smtx_typeof t <;>
    simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢

private theorem qexists_non_nil_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None ->
    x ≠ Term.__eo_List_nil := by
  intro hNN hx
  subst x
  apply hNN
  unfold qexists qterm
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_non_nil_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    x ≠ Term.__eo_List_nil := by
  intro hNN hx
  subst x
  apply hNN
  unfold qforall qterm
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem smtx_typeof_eo_to_smt_exists_bool_of_non_nil_non_none
    (xs : Term) (body : SmtTerm)
    (hNN : __smtx_typeof (__eo_to_smt_exists xs body) ≠ SmtType.None)
    (hNonNil : xs ≠ Term.__eo_List_nil) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  induction xs, body using __eo_to_smt_exists.induct with
  | case1 F =>
      exact False.elim (hNonNil rfl)
  | case2 s T xs F ih =>
      change
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs F)) =
          SmtType.Bool
      rw [smtx_typeof_exists_term_eq]
      by_cases hTail :
          __smtx_typeof (__eo_to_smt_exists xs F) = SmtType.Bool
      · simp [hTail, native_ite, native_Teq]
        by_cases hGuard :
            __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool =
              SmtType.None
        · have hNone :
              __smtx_typeof
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists xs F)) =
                SmtType.None := by
            rw [smtx_typeof_exists_term_eq]
            simp [hTail, hGuard, native_ite, native_Teq]
          exact False.elim (hNN hNone)
        · exact smtx_typeof_guard_wf_of_non_none
            (__eo_to_smt_type T) SmtType.Bool hGuard
      · have hNone :
            __smtx_typeof
                (SmtTerm.exists s (__eo_to_smt_type T)
                  (__eo_to_smt_exists xs F)) =
              SmtType.None := by
          rw [smtx_typeof_exists_term_eq]
          cases hTy : __smtx_typeof (__eo_to_smt_exists xs F) <;>
            simp [native_ite, native_Teq]
          · exact False.elim (hTail hTy)
        exact False.elim (hNN hNone)
  | case3 xs F hNotNil hNotConsVar =>
      have hNone :
          __smtx_typeof (__eo_to_smt_exists xs F) = SmtType.None := by
        cases xs with
        | Apply f a =>
            cases f with
            | Apply g y =>
                cases g with
                | __eo_List_cons =>
                    cases y with
                    | Var name T =>
                        cases name with
                        | String s =>
                            exact False.elim (hNotConsVar s T a rfl)
                        | _ =>
                            simp [__eo_to_smt_exists,
                              TranslationProofs.smtx_typeof_none]
                    | _ =>
                        simp [__eo_to_smt_exists,
                          TranslationProofs.smtx_typeof_none]
                | _ =>
                    simp [__eo_to_smt_exists,
                      TranslationProofs.smtx_typeof_none]
            | _ =>
                simp [__eo_to_smt_exists,
                  TranslationProofs.smtx_typeof_none]
        | __eo_List_nil =>
            exact False.elim (hNotNil rfl)
        | _ =>
            simp [__eo_to_smt_exists,
              TranslationProofs.smtx_typeof_none]
      exact False.elim (hNN hNone)

private theorem qexists_typeof_bool_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool := by
  intro hNN
  have hx : x ≠ Term.__eo_List_nil :=
    qexists_non_nil_of_non_none x F hNN
  rw [eo_to_smt_exists_eq x F hx] at hNN ⊢
  exact smtx_typeof_eo_to_smt_exists_bool_of_non_nil_non_none
    x (__eo_to_smt F) hNN hx

private theorem qforall_typeof_bool_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
  intro hNN
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F hNN
  rw [eo_to_smt_forall_eq x F hx] at hNN ⊢
  exact smtx_typeof_not_bool_of_arg_bool _
    (smtx_typeof_not_arg_of_non_none _ hNN)

private theorem qterm_typeof_bool_of_quant_non_none
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNN : __smtx_typeof (__eo_to_smt (qterm Q x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool := by
  rcases hQ with hForall | hExists
  · subst Q
    exact qforall_typeof_bool_of_non_none x F hNN
  · subst Q
    exact qexists_typeof_bool_of_non_none x F hNN

private theorem qexists_body_typeof_bool_of_typeof_bool
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
  intro hTy
  have hx : x ≠ Term.__eo_List_nil :=
    qexists_non_nil_of_non_none x F (by rw [hTy]; simp)
  rw [eo_to_smt_exists_eq x F hx] at hTy
  exact TranslationProofs.eo_to_smt_exists_body_bool_of_bool
    x (__eo_to_smt F) hTy

private theorem qforall_body_typeof_bool_of_typeof_bool
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
  intro hTy
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F (by rw [hTy]; simp)
  have hExists :
      __smtx_typeof
          (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool := by
    rw [eo_to_smt_forall_eq x F hx] at hTy
    exact smtx_typeof_not_arg_of_bool _ hTy
  have hNotBody :
      __smtx_typeof (SmtTerm.not (__eo_to_smt F)) = SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool
      x (SmtTerm.not (__eo_to_smt F)) hExists
  exact smtx_typeof_not_arg_of_bool _ hNotBody

private theorem qterm_body_typeof_bool_of_quant_typeof_bool
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
  rcases hQ with hForall | hExists
  · subst Q
    exact qforall_body_typeof_bool_of_typeof_bool x F hTy
  · subst Q
    exact qexists_body_typeof_bool_of_typeof_bool x F hTy

private theorem smtx_typeof_eo_to_smt_list_cons_none
    (x ys : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply Term.__eo_List_cons x) ys)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
          (__eo_to_smt ys)) =
      SmtType.None
  exact TranslationProofs.typeof_apply_apply_none_head_eq
    (__eo_to_smt x) (__eo_to_smt ys)

private theorem smtx_typeof_apply_none_head (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) =
      SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_apply]

private theorem smtx_typeof_apply_arg_none
    (f x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  intro hx
  by_cases hNone : __smtx_typeof (SmtTerm.Apply f x) = SmtType.None
  · exact hNone
  · exfalso
    by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
    · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
      have hArg : __smtx_typeof x = SmtType.Datatype s d :=
        dt_sel_arg_datatype_of_non_none (s := s) (d := d) (i := i)
          (j := j) (x := x) hNone
      rw [hx] at hArg
      cases hArg
    · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
      · rcases hTesterWitness with ⟨s, d, i, rfl⟩
        have hArg : __smtx_typeof x = SmtType.Datatype s d :=
          dt_tester_arg_datatype_of_non_none (s := s) (d := d) (i := i)
            (x := x) hNone
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
          exact hNone
        rcases typeof_apply_non_none_cases hApply with
          ⟨A, _B, _hHead, hArg, hA, _hB⟩
        rw [hx] at hArg
        exact hA hArg.symm

private theorem smtx_typeof_apply_head_none_of_non_datatype_head
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hf : __smtx_typeof f = SmtType.None) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  have hGeneric : generic_apply_type f x :=
    generic_apply_type_of_non_datatype_head hSel hTester
  rw [hGeneric, hf]
  simp [__smtx_typeof_apply]

private theorem smtx_typeof_apply_head_non_none_of_generic_non_none
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  have hGeneric : generic_apply_type f x :=
    generic_apply_type_of_non_datatype_head hSel hTester
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
        SmtType.None := by
    unfold generic_apply_type at hGeneric
    rw [← hGeneric]
    exact hNN
  rcases typeof_apply_non_none_cases hApply with
    ⟨A, B, hHead, _hArg, _hA, _hB⟩
  rcases hHead with hFun | hDtc
  · rw [hFun]
    simp
  · rw [hDtc]
    simp

private theorem smtx_typeof_apply_apply_arg_none
    (f x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply f x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_apply_arg_none f x hx

private theorem smtx_typeof_eo_to_smt_apply_apply_generic_head_none
    (q binders a : Term)
    (hToSmt :
      __eo_to_smt (Term.Apply (Term.Apply q binders) a) =
        SmtTerm.Apply
          (SmtTerm.Apply (__eo_to_smt q) (__eo_to_smt binders))
          (__eo_to_smt a))
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rw [hToSmt]
  exact smtx_typeof_apply_apply_arg_none
    (__eo_to_smt q) (__eo_to_smt binders) (__eo_to_smt a)
    hBindersNone

private theorem smtx_typeof_or_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.or x y) = SmtType.None := by
  intro hx
  rw [typeof_or_eq, hx]
  rfl

private theorem smtx_typeof_and_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.and x y) = SmtType.None := by
  intro hx
  rw [typeof_and_eq, hx]
  rfl

private theorem smtx_typeof_imp_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.imp x y) = SmtType.None := by
  intro hx
  rw [typeof_imp_eq, hx]
  rfl

private theorem smtx_typeof_xor_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.xor x y) = SmtType.None := by
  intro hx
  rw [typeof_xor_eq, hx]
  rfl

private theorem smtx_typeof_eq_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.eq x y) = SmtType.None := by
  intro hx
  rw [typeof_eq_eq, hx]
  unfold __smtx_typeof_eq __smtx_typeof_guard
  simp [native_ite, native_Teq]

private theorem smtx_typeof_or_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.or x y) = SmtType.None := by
  intro hy
  rw [typeof_or_eq, hy]
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_and_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.and x y) = SmtType.None := by
  intro hy
  rw [typeof_and_eq, hy]
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_imp_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.imp x y) = SmtType.None := by
  intro hy
  rw [typeof_imp_eq, hy]
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_xor_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.xor x y) = SmtType.None := by
  intro hy
  rw [typeof_xor_eq, hy]
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_eq_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.eq x y) = SmtType.None := by
  intro hy
  rw [typeof_eq_eq, hy]
  unfold __smtx_typeof_eq __smtx_typeof_guard
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_plus_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.plus x y) = SmtType.None := by
  intro hx
  rw [typeof_plus_eq, hx]
  rfl

private theorem smtx_typeof_neg_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.neg x y) = SmtType.None := by
  intro hx
  rw [typeof_neg_eq, hx]
  rfl

private theorem smtx_typeof_mult_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.mult x y) = SmtType.None := by
  intro hx
  rw [typeof_mult_eq, hx]
  rfl

private theorem smtx_typeof_lt_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.lt x y) = SmtType.None := by
  intro hx
  rw [typeof_lt_eq, hx]
  rfl

private theorem smtx_typeof_leq_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.leq x y) = SmtType.None := by
  intro hx
  rw [typeof_leq_eq, hx]
  rfl

private theorem smtx_typeof_gt_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.gt x y) = SmtType.None := by
  intro hx
  rw [typeof_gt_eq, hx]
  rfl

private theorem smtx_typeof_geq_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.geq x y) = SmtType.None := by
  intro hx
  rw [typeof_geq_eq, hx]
  rfl

private theorem smtx_typeof_div_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.div x y) = SmtType.None := by
  intro hx
  rw [typeof_div_eq, hx]
  rfl

private theorem smtx_typeof_mod_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.mod x y) = SmtType.None := by
  intro hx
  rw [typeof_mod_eq, hx]
  rfl

private theorem smtx_typeof_multmult_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.multmult x y) = SmtType.None := by
  intro hx
  rw [typeof_multmult_eq, hx]
  rfl

private theorem smtx_typeof_divisible_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.divisible x y) = SmtType.None := by
  intro hx
  rw [typeof_divisible_eq, hx]
  rfl

private theorem smtx_typeof_div_total_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.div_total x y) = SmtType.None := by
  intro hx
  rw [typeof_div_total_eq, hx]
  rfl

private theorem smtx_typeof_mod_total_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.mod_total x y) = SmtType.None := by
  intro hx
  rw [typeof_mod_total_eq, hx]
  rfl

private theorem smtx_typeof_multmult_total_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.multmult_total x y) = SmtType.None := by
  intro hx
  rw [typeof_multmult_total_eq, hx]
  rfl

private theorem smtx_typeof_qdiv_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.qdiv x y) = SmtType.None := by
  intro hx
  rw [typeof_qdiv_eq, hx]
  rfl

private theorem smtx_typeof_qdiv_total_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.qdiv_total x y) = SmtType.None := by
  intro hx
  rw [typeof_qdiv_total_eq, hx]
  rfl

private theorem smtx_typeof_select_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.select x y) = SmtType.None := by
  intro hx
  rw [typeof_select_eq, hx]
  rfl

private theorem smtx_typeof_concat_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.concat x y) = SmtType.None := by
  intro hx
  rw [typeof_concat_eq, hx]
  rfl

private theorem smtx_typeof_plus_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.plus x y) = SmtType.None := by
  intro hy
  rw [typeof_plus_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_neg_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.neg x y) = SmtType.None := by
  intro hy
  rw [typeof_neg_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_mult_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.mult x y) = SmtType.None := by
  intro hy
  rw [typeof_mult_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_lt_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.lt x y) = SmtType.None := by
  intro hy
  rw [typeof_lt_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_leq_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.leq x y) = SmtType.None := by
  intro hy
  rw [typeof_leq_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_gt_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.gt x y) = SmtType.None := by
  intro hy
  rw [typeof_gt_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_geq_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.geq x y) = SmtType.None := by
  intro hy
  rw [typeof_geq_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_div_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.div x y) = SmtType.None := by
  intro hy
  rw [typeof_div_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_mod_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.mod x y) = SmtType.None := by
  intro hy
  rw [typeof_mod_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_multmult_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.multmult x y) = SmtType.None := by
  intro hy
  rw [typeof_multmult_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_divisible_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.divisible x y) = SmtType.None := by
  intro hy
  rw [typeof_divisible_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_div_total_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.div_total x y) = SmtType.None := by
  intro hy
  rw [typeof_div_total_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_mod_total_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.mod_total x y) = SmtType.None := by
  intro hy
  rw [typeof_mod_total_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_multmult_total_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.multmult_total x y) = SmtType.None := by
  intro hy
  rw [typeof_multmult_total_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_qdiv_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.qdiv x y) = SmtType.None := by
  intro hy
  rw [typeof_qdiv_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_qdiv_total_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.qdiv_total x y) = SmtType.None := by
  intro hy
  rw [typeof_qdiv_total_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_select_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.select x y) = SmtType.None := by
  intro hy
  rw [typeof_select_eq, hy]
  cases hX : __smtx_typeof x with
  | Map A B =>
      by_cases hA : A = SmtType.None
      · have hxNN : term_has_non_none_type x := by
          unfold term_has_non_none_type
          rw [hX]
          simp
        have hNoNone := term_type_has_no_none_components_of_non_none x hxNN
        have hNoNoneAB :
            type_has_no_none_components A ∧
              type_has_no_none_components B := by
          simpa [hX, type_has_no_none_components] using hNoNone
        exact False.elim
          ((type_has_no_none_components_non_none hNoNoneAB.1) hA)
      · simp [__smtx_typeof_select, native_ite, native_Teq, hA]
  | _ =>
      simp [__smtx_typeof_select]

private theorem smtx_typeof_concat_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.concat x y) = SmtType.None := by
  intro hy
  rw [typeof_concat_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_eo_to_smt_apply_apply_binary_arith_second_head_none
    (q binders a : Term)
    (hArith :
      ∃ z : Term,
        q = Term.Apply (Term.UOp UserOp.plus) z ∨
          q = Term.Apply (Term.UOp UserOp.neg) z ∨
          q = Term.Apply (Term.UOp UserOp.mult) z ∨
          q = Term.Apply (Term.UOp UserOp.lt) z ∨
          q = Term.Apply (Term.UOp UserOp.leq) z ∨
          q = Term.Apply (Term.UOp UserOp.gt) z ∨
          q = Term.Apply (Term.UOp UserOp.geq) z ∨
          q = Term.Apply (Term.UOp UserOp.div) z ∨
          q = Term.Apply (Term.UOp UserOp.mod) z ∨
          q = Term.Apply (Term.UOp UserOp.multmult) z ∨
          q = Term.Apply (Term.UOp UserOp.divisible) z ∨
          q = Term.Apply (Term.UOp UserOp.div_total) z ∨
          q = Term.Apply (Term.UOp UserOp.mod_total) z ∨
          q = Term.Apply (Term.UOp UserOp.multmult_total) z ∨
          q = Term.Apply (Term.UOp UserOp.qdiv) z ∨
          q = Term.Apply (Term.UOp UserOp.qdiv_total) z ∨
          q = Term.Apply (Term.UOp UserOp.select) z ∨
          q = Term.Apply (Term.UOp UserOp.concat) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  have hApplyHeadNone :
      ∀ head : SmtTerm,
        (∀ s d i j, head ≠ SmtTerm.DtSel s d i j) ->
        (∀ s d i, head ≠ SmtTerm.DtTester s d i) ->
        __smtx_typeof head = SmtType.None ->
        __smtx_typeof (SmtTerm.Apply head (__eo_to_smt a)) =
          SmtType.None := by
    intro head hSel hTester hHead
    exact smtx_typeof_apply_head_none_of_non_datatype_head
      head (__eo_to_smt a) hSel hTester hHead
  rcases hArith with
    ⟨z, hPlus | hNeg | hMult | hLt | hLeq | hGt | hGeq | hDiv |
      hMod | hMultmult | hDivisible | hDivTotal | hModTotal |
      hMultmultTotal | hQdiv | hQdivTotal | hSelect | hConcat⟩
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
          (SmtTerm.plus (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_plus_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.neg (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_neg_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.mult (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_mult_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.lt (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_lt_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.leq (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_leq_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.gt (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_gt_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.geq (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_geq_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.div (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_div_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.mod (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_mod_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.multmult (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_multmult_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.divisible (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_divisible_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.div_total (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_div_total_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.mod_total (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_mod_total_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.multmult_total (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_multmult_total_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.qdiv (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_qdiv_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.qdiv_total (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_qdiv_total_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.select (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_select_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.concat (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_concat_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)

private theorem smtx_typeof_str_concat_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_concat x y) = SmtType.None := by
  intro hx
  rw [typeof_str_concat_eq, hx]
  rfl

private theorem smtx_typeof_str_contains_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_contains x y) = SmtType.None := by
  intro hx
  rw [typeof_str_contains_eq, hx]
  rfl

private theorem smtx_typeof_str_at_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_at x y) = SmtType.None := by
  intro hx
  rw [typeof_str_at_eq, hx]
  rfl

private theorem smtx_typeof_str_prefixof_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_prefixof x y) = SmtType.None := by
  intro hx
  rw [typeof_str_prefixof_eq, hx]
  rfl

private theorem smtx_typeof_str_suffixof_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_suffixof x y) = SmtType.None := by
  intro hx
  rw [typeof_str_suffixof_eq, hx]
  rfl

private theorem smtx_typeof_str_lt_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_lt x y) = SmtType.None := by
  intro hx
  rw [typeof_str_lt_eq, hx]
  rfl

private theorem smtx_typeof_str_leq_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_leq x y) = SmtType.None := by
  intro hx
  rw [typeof_str_leq_eq, hx]
  rfl

private theorem smtx_typeof_re_range_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.re_range x y) = SmtType.None := by
  intro hx
  rw [typeof_re_range_eq, hx]
  rfl

private theorem smtx_typeof_re_concat_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.re_concat x y) = SmtType.None := by
  intro hx
  rw [typeof_re_concat_eq, hx]
  rfl

private theorem smtx_typeof_re_inter_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.re_inter x y) = SmtType.None := by
  intro hx
  rw [typeof_re_inter_eq, hx]
  rfl

private theorem smtx_typeof_re_union_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.re_union x y) = SmtType.None := by
  intro hx
  rw [typeof_re_union_eq, hx]
  rfl

private theorem smtx_typeof_re_diff_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.re_diff x y) = SmtType.None := by
  intro hx
  rw [typeof_re_diff_eq, hx]
  rfl

private theorem smtx_typeof_str_in_re_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_in_re x y) = SmtType.None := by
  intro hx
  rw [typeof_str_in_re_eq, hx]
  rfl

private theorem smtx_typeof_seq_nth_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.seq_nth x y) = SmtType.None := by
  intro hx
  rw [typeof_seq_nth_eq, hx]
  rfl

private theorem smtx_typeof_set_union_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.set_union x y) = SmtType.None := by
  intro hx
  rw [typeof_set_union_eq, hx]
  rfl

private theorem smtx_typeof_set_inter_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.set_inter x y) = SmtType.None := by
  intro hx
  rw [typeof_set_inter_eq, hx]
  rfl

private theorem smtx_typeof_set_minus_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.set_minus x y) = SmtType.None := by
  intro hx
  rw [typeof_set_minus_eq, hx]
  rfl

private theorem smtx_typeof_set_subset_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.set_subset x y) = SmtType.None := by
  intro hx
  rw [typeof_set_subset_eq, hx]
  rfl

private theorem smtx_typeof_set_member_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.set_member x y) = SmtType.None := by
  intro hx
  rw [typeof_set_member_eq, hx]
  cases hY : __smtx_typeof y with
  | Set A =>
      by_cases hA : A = SmtType.None
      · have hyNN : term_has_non_none_type y := by
          unfold term_has_non_none_type
          rw [hY]
          simp
        have hNoNone := term_type_has_no_none_components_of_non_none y hyNN
        have hNoNoneA : type_has_no_none_components A := by
          simpa [hY, type_has_no_none_components] using hNoNone
        exact False.elim ((type_has_no_none_components_non_none hNoNoneA) hA)
      · have hANone : SmtType.None ≠ A := fun h => hA h.symm
        simp [__smtx_typeof_set_member, native_ite, native_Teq,
          hANone]
  | _ =>
      simp [__smtx_typeof_set_member]

private theorem smtx_typeof_str_concat_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_concat x y) = SmtType.None := by
  intro hy
  rw [typeof_str_concat_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_str_contains_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_contains x y) = SmtType.None := by
  intro hy
  rw [typeof_str_contains_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_str_at_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_at x y) = SmtType.None := by
  intro hy
  rw [typeof_str_at_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_str_prefixof_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_prefixof x y) = SmtType.None := by
  intro hy
  rw [typeof_str_prefixof_eq, hy]
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_str_suffixof_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_suffixof x y) = SmtType.None := by
  intro hy
  rw [typeof_str_suffixof_eq, hy]
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_str_lt_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_lt x y) = SmtType.None := by
  intro hy
  rw [typeof_str_lt_eq, hy]
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_str_leq_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_leq x y) = SmtType.None := by
  intro hy
  rw [typeof_str_leq_eq, hy]
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_re_range_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.re_range x y) = SmtType.None := by
  intro hy
  rw [typeof_re_range_eq, hy]
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_re_concat_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.re_concat x y) = SmtType.None := by
  intro hy
  rw [typeof_re_concat_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_re_inter_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.re_inter x y) = SmtType.None := by
  intro hy
  rw [typeof_re_inter_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_re_union_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.re_union x y) = SmtType.None := by
  intro hy
  rw [typeof_re_union_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_re_diff_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.re_diff x y) = SmtType.None := by
  intro hy
  rw [typeof_re_diff_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_str_in_re_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_in_re x y) = SmtType.None := by
  intro hy
  rw [typeof_str_in_re_eq, hy]
  cases __smtx_typeof x <;> simp [native_ite, native_Teq]

private theorem smtx_typeof_seq_nth_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.seq_nth x y) = SmtType.None := by
  intro hy
  rw [typeof_seq_nth_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_set_union_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.set_union x y) = SmtType.None := by
  intro hy
  rw [typeof_set_union_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_set_inter_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.set_inter x y) = SmtType.None := by
  intro hy
  rw [typeof_set_inter_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_set_minus_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.set_minus x y) = SmtType.None := by
  intro hy
  rw [typeof_set_minus_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_set_subset_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.set_subset x y) = SmtType.None := by
  intro hy
  rw [typeof_set_subset_eq, hy]
  cases __smtx_typeof x <;> rfl

private theorem smtx_typeof_set_member_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.set_member x y) = SmtType.None := by
  intro hy
  rw [typeof_set_member_eq, hy]
  rfl

private theorem smtx_typeof_eo_to_smt_apply_apply_binary_seq_set_second_head_none
    (q binders a : Term)
    (hBinary :
      ∃ z : Term,
        q = Term.Apply (Term.UOp UserOp.str_concat) z ∨
          q = Term.Apply (Term.UOp UserOp.str_contains) z ∨
          q = Term.Apply (Term.UOp UserOp.str_at) z ∨
          q = Term.Apply (Term.UOp UserOp.str_prefixof) z ∨
          q = Term.Apply (Term.UOp UserOp.str_suffixof) z ∨
          q = Term.Apply (Term.UOp UserOp.str_lt) z ∨
          q = Term.Apply (Term.UOp UserOp.str_leq) z ∨
          q = Term.Apply (Term.UOp UserOp.re_range) z ∨
          q = Term.Apply (Term.UOp UserOp.re_concat) z ∨
          q = Term.Apply (Term.UOp UserOp.re_inter) z ∨
          q = Term.Apply (Term.UOp UserOp.re_union) z ∨
          q = Term.Apply (Term.UOp UserOp.re_diff) z ∨
          q = Term.Apply (Term.UOp UserOp.str_in_re) z ∨
          q = Term.Apply (Term.UOp UserOp.seq_nth) z ∨
          q = Term.Apply (Term.UOp UserOp.set_union) z ∨
          q = Term.Apply (Term.UOp UserOp.set_inter) z ∨
          q = Term.Apply (Term.UOp UserOp.set_minus) z ∨
          q = Term.Apply (Term.UOp UserOp.set_member) z ∨
          q = Term.Apply (Term.UOp UserOp.set_subset) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  have hApplyHeadNone :
      ∀ head : SmtTerm,
        (∀ s d i j, head ≠ SmtTerm.DtSel s d i j) ->
        (∀ s d i, head ≠ SmtTerm.DtTester s d i) ->
        __smtx_typeof head = SmtType.None ->
        __smtx_typeof (SmtTerm.Apply head (__eo_to_smt a)) =
          SmtType.None := by
    intro head hSel hTester hHead
    exact smtx_typeof_apply_head_none_of_non_datatype_head
      head (__eo_to_smt a) hSel hTester hHead
  rcases hBinary with
    ⟨z, hStrConcat | hStrContains | hStrAt | hStrPrefixof |
      hStrSuffixof | hStrLt | hStrLeq | hReRange | hReConcat |
      hReInter | hReUnion | hReDiff | hStrInRe | hSeqNth |
      hSetUnion | hSetInter | hSetMinus | hSetMember | hSetSubset⟩
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_concat (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_str_concat_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_contains (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_str_contains_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_at (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_str_at_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_prefixof (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_str_prefixof_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_suffixof (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_str_suffixof_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_lt (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_str_lt_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_leq (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_str_leq_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.re_range (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_re_range_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.re_concat (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_re_concat_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.re_inter (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_re_inter_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.re_union (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_re_union_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.re_diff (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_re_diff_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_in_re (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_str_in_re_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.seq_nth (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_seq_nth_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.set_union (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_set_union_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.set_inter (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_set_inter_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.set_minus (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_set_minus_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.set_member (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_set_member_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.set_subset (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_set_subset_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)

private theorem smtx_typeof_set_singleton_arg_none
    (x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.set_singleton x) = SmtType.None := by
  intro hx
  rw [smtx_typeof_set_singleton_term_eq, hx]
  simp [__smtx_typeof_guard_wf, __smtx_type_wf,
    __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and, native_ite]

private theorem smtx_typeof_apply_set_singleton_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.set_singleton x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_set_singleton_arg_none x hx

private theorem smtx_typeof_apply_to_real_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.to_real x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_to_real_eq, hx]
    rfl

private theorem smtx_typeof_apply_to_int_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.to_int x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_to_int_eq, hx]
    rfl

private theorem smtx_typeof_apply_is_int_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.is_int x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_is_int_eq, hx]
    rfl

private theorem smtx_typeof_apply_abs_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.abs x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_abs_eq, hx]
    rfl

private theorem smtx_typeof_apply_uneg_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.uneg x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_uneg_eq, hx]
    rfl

private theorem smtx_typeof_apply_int_pow2_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.int_pow2 x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_int_pow2_eq, hx]
    rfl

private theorem smtx_typeof_apply_int_log2_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.int_log2 x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_int_log2_eq, hx]
    rfl

private theorem smtx_typeof_apply_int_ispow2_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.and (SmtTerm.geq x (SmtTerm.Numeral 0))
            (SmtTerm.eq x (SmtTerm.int_pow2 (SmtTerm.int_log2 x))))
          y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_and_first_arg_none
      (SmtTerm.geq x (SmtTerm.Numeral 0))
      (SmtTerm.eq x (SmtTerm.int_pow2 (SmtTerm.int_log2 x)))
      (smtx_typeof_geq_first_arg_none x (SmtTerm.Numeral 0) hx)

private theorem smtx_typeof_apply_int_div_by_zero_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof
        (SmtTerm.Apply (SmtTerm.div x (SmtTerm.Numeral 0)) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_div_first_arg_none x (SmtTerm.Numeral 0) hx

private theorem smtx_typeof_apply_mod_by_zero_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof
        (SmtTerm.Apply (SmtTerm.mod x (SmtTerm.Numeral 0)) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_mod_first_arg_none x (SmtTerm.Numeral 0) hx

private theorem smtx_typeof_apply_qdiv_by_zero_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.qdiv x
            (SmtTerm.Rational (native_mk_rational 0 1)))
          y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_qdiv_first_arg_none x
      (SmtTerm.Rational (native_mk_rational 0 1)) hx

private theorem smtx_typeof_apply_str_len_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_len x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_str_len_eq, hx]
    rfl

private theorem smtx_typeof_apply_str_rev_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_rev x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_str_rev_eq, hx]
    rfl

private theorem smtx_typeof_apply_str_to_lower_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_to_lower x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_str_to_lower_eq, hx]
    rfl

private theorem smtx_typeof_apply_str_to_upper_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_to_upper x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_str_to_upper_eq, hx]
    rfl

private theorem smtx_typeof_apply_str_to_code_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_to_code x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_str_to_code_eq, hx]
    rfl

private theorem smtx_typeof_apply_str_from_code_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_from_code x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_str_from_code_eq, hx]
    rfl

private theorem smtx_typeof_apply_str_is_digit_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_is_digit x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_str_is_digit_eq, hx]
    rfl

private theorem smtx_typeof_apply_str_to_int_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_to_int x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_str_to_int_eq, hx]
    rfl

private theorem smtx_typeof_apply_str_from_int_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_from_int x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_str_from_int_eq, hx]
    rfl

private theorem smtx_typeof_apply_str_to_re_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_to_re x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_str_to_re_eq, hx]
    rfl

private theorem smtx_typeof_apply_re_mult_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.re_mult x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_re_mult_eq, hx]
    rfl

private theorem smtx_typeof_apply_re_plus_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.re_plus x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_re_plus_eq, hx]
    rfl

private theorem smtx_typeof_apply_re_opt_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.re_opt x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_re_opt_eq, hx]
    rfl

private theorem smtx_typeof_apply_re_comp_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.re_comp x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [typeof_re_comp_eq, hx]
    rfl

private theorem smtx_typeof_seq_unit_arg_none
    (x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.seq_unit x) = SmtType.None := by
  intro hx
  rw [smtx_typeof_seq_unit_term_eq, hx]
  simp [__smtx_typeof_guard_wf, __smtx_type_wf,
    __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and, native_ite]

private theorem smtx_typeof_apply_seq_unit_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.seq_unit x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_seq_unit_arg_none x hx

private theorem smtx_typeof_apply_ubv_to_int_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.ubv_to_int x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [smtx_typeof_ubv_to_int_term_eq, hx]
    rfl

private theorem smtx_typeof_sbv_to_int_term_eq_local
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.sbv_to_int x) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof x) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_apply_sbv_to_int_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.sbv_to_int x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [smtx_typeof_sbv_to_int_term_eq_local, hx]
    rfl

private theorem smtx_typeof_set_choose_arg_none
    (x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof
        (SmtTerm.map_diff x
          (SmtTerm.set_empty
            (__eo_to_smt_set_elem_type (__smtx_typeof x)))) =
      SmtType.None := by
  intro hx
  rw [typeof_map_diff_eq, hx]
  simp [__smtx_typeof_map_diff]

private theorem smtx_typeof_apply_set_choose_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.map_diff x
            (SmtTerm.set_empty
              (__eo_to_smt_set_elem_type (__smtx_typeof x))))
          y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_set_choose_arg_none x hx

private theorem smtx_typeof_apply_set_is_empty_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.eq x (SmtTerm.set_empty (__smtx_typeof x)))
          y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_eq_first_arg_none x
      (SmtTerm.set_empty (__smtx_typeof x)) hx

private theorem smtx_typeof_apply_set_is_singleton_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.eq x
            (SmtTerm.set_singleton
              (SmtTerm.map_diff x
                (SmtTerm.set_empty
                  (__eo_to_smt_set_elem_type (__smtx_typeof x))))))
          y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_eq_first_arg_none x
      (SmtTerm.set_singleton
        (SmtTerm.map_diff x
          (SmtTerm.set_empty
            (__eo_to_smt_set_elem_type (__smtx_typeof x))))) hx

private theorem smtx_typeof_bvnot_arg_none
    (x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvnot x) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_apply_bvnot_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.bvnot x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_bvnot_arg_none x hx

private theorem smtx_typeof_bvneg_arg_none
    (x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvneg x) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_apply_bvneg_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.bvneg x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_bvneg_arg_none x hx

private theorem smtx_typeof_bvnego_arg_none
    (x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvnego x) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_apply_bvnego_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.bvnego x) y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_bvnego_arg_none x hx

private theorem smtx_typeof_bvcomp_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvcomp x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bv_op_2_type_second_none
    (T : SmtType) :
    __smtx_typeof_bv_op_2 T SmtType.None = SmtType.None := by
  cases T <;> rfl

private theorem smtx_typeof_bv_op_2_ret_type_second_none
    (T R : SmtType) :
    __smtx_typeof_bv_op_2_ret T SmtType.None R = SmtType.None := by
  cases T <;> rfl

private theorem smtx_typeof_bvcomp_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvcomp x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) (SmtType.BitVec 1)

private theorem smtx_typeof_bvand_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvand x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvand_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvand x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvor_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvor x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvor_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvor x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvnand_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvnand x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvnand_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvnand x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvnor_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvnor x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvnor_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvnor x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvxor_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvxor x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvxor_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvxor x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvxnor_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvxnor x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvxnor_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvxnor x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_eo_to_smt_apply_apply_bv_bitwise_second_head_none
    (q binders a : Term)
    (hBv :
      ∃ z : Term,
        q = Term.Apply (Term.UOp UserOp.bvand) z ∨
          q = Term.Apply (Term.UOp UserOp.bvor) z ∨
          q = Term.Apply (Term.UOp UserOp.bvnand) z ∨
          q = Term.Apply (Term.UOp UserOp.bvnor) z ∨
          q = Term.Apply (Term.UOp UserOp.bvxor) z ∨
          q = Term.Apply (Term.UOp UserOp.bvxnor) z ∨
          q = Term.Apply (Term.UOp UserOp.bvcomp) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  have hApplyHeadNone :
      ∀ head : SmtTerm,
        (∀ s d i j, head ≠ SmtTerm.DtSel s d i j) ->
        (∀ s d i, head ≠ SmtTerm.DtTester s d i) ->
        __smtx_typeof head = SmtType.None ->
        __smtx_typeof (SmtTerm.Apply head (__eo_to_smt a)) =
          SmtType.None := by
    intro head hSel hTester hHead
    exact smtx_typeof_apply_head_none_of_non_datatype_head
      head (__eo_to_smt a) hSel hTester hHead
  rcases hBv with
    ⟨z, hBvand | hBvor | hBvnand | hBvnor | hBvxor |
      hBvxnor | hBvcomp⟩
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.bvand (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvand_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.bvor (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvor_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.bvnand (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvnand_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.bvnor (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvnor_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.bvxor (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvxor_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.bvxnor (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvxnor_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.bvcomp (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvcomp_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)

private theorem smtx_typeof_bvadd_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvadd x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvmul_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvmul x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvudiv_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvudiv x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvurem_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvurem x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvsub_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsub x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvsdiv_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsdiv x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvsrem_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsrem x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvsmod_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsmod x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvadd_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvadd x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvmul_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvmul x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvudiv_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvudiv x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvurem_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvurem x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvsub_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsub x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvsdiv_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsdiv x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvsrem_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsrem x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvsmod_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsmod x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvshl_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvshl x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvlshr_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvlshr x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvashr_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvashr x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvshl_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvshl x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvlshr_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvlshr x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_bvashr_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvashr x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_type_second_none (__smtx_typeof x)

private theorem smtx_typeof_eo_to_smt_apply_apply_bv_arith_shift_second_head_none
    (q binders a : Term)
    (hBv :
      ∃ z : Term,
        q = Term.Apply (Term.UOp UserOp.bvadd) z ∨
          q = Term.Apply (Term.UOp UserOp.bvmul) z ∨
          q = Term.Apply (Term.UOp UserOp.bvudiv) z ∨
          q = Term.Apply (Term.UOp UserOp.bvurem) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsub) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsdiv) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsrem) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsmod) z ∨
          q = Term.Apply (Term.UOp UserOp.bvshl) z ∨
          q = Term.Apply (Term.UOp UserOp.bvlshr) z ∨
          q = Term.Apply (Term.UOp UserOp.bvashr) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  have hApplyHeadNone :
      ∀ head : SmtTerm,
        (∀ s d i j, head ≠ SmtTerm.DtSel s d i j) ->
        (∀ s d i, head ≠ SmtTerm.DtTester s d i) ->
        __smtx_typeof head = SmtType.None ->
        __smtx_typeof (SmtTerm.Apply head (__eo_to_smt a)) =
          SmtType.None := by
    intro head hSel hTester hHead
    exact smtx_typeof_apply_head_none_of_non_datatype_head
      head (__eo_to_smt a) hSel hTester hHead
  rcases hBv with
    ⟨z, hBvadd | hBvmul | hBvudiv | hBvurem | hBvsub |
      hBvsdiv | hBvsrem | hBvsmod | hBvshl | hBvlshr | hBvashr⟩
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvadd (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvadd_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvmul (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvmul_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvudiv (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvudiv_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvurem (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvurem_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvsub (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvsub_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvsdiv (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvsdiv_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvsrem (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvsrem_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvsmod (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvsmod_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvshl (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvshl_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvlshr (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvlshr_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvashr (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvashr_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)

private theorem smtx_typeof_eo_to_smt_apply_apply_bv_shift_head_none
    (q binders a : Term)
    (hShift :
      q = Term.UOp UserOp.bvshl ∨
        q = Term.UOp UserOp.bvlshr ∨
        q = Term.UOp UserOp.bvashr)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hShift with hBvshl | hBvlshr | hBvashr
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvshl (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvshl_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvlshr (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvlshr_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvashr (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvashr_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone

private theorem smtx_typeof_bvult_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvult x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvule_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvule x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvugt_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvugt x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvuge_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvuge x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvslt_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvslt x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvsle_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsle x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvsgt_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsgt x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvsge_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsge x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvult_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvult x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvule_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvule x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvugt_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvugt x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvuge_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvuge x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvslt_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvslt x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvsle_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsle x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvsgt_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsgt x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvsge_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsge x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_eo_to_smt_apply_apply_bv_compare_second_head_none
    (q binders a : Term)
    (hCompare :
      ∃ z : Term,
        q = Term.Apply (Term.UOp UserOp.bvult) z ∨
          q = Term.Apply (Term.UOp UserOp.bvule) z ∨
          q = Term.Apply (Term.UOp UserOp.bvugt) z ∨
          q = Term.Apply (Term.UOp UserOp.bvuge) z ∨
          q = Term.Apply (Term.UOp UserOp.bvslt) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsle) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsgt) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsge) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  have hApplyHeadNone :
      ∀ head : SmtTerm,
        (∀ s d i j, head ≠ SmtTerm.DtSel s d i j) ->
        (∀ s d i, head ≠ SmtTerm.DtTester s d i) ->
        __smtx_typeof head = SmtType.None ->
        __smtx_typeof (SmtTerm.Apply head (__eo_to_smt a)) =
          SmtType.None := by
    intro head hSel hTester hHead
    exact smtx_typeof_apply_head_none_of_non_datatype_head
      head (__eo_to_smt a) hSel hTester hHead
  rcases hCompare with
    ⟨z, hBvult | hBvule | hBvugt | hBvuge |
      hBvslt | hBvsle | hBvsgt | hBvsge⟩
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvult (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvult_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvule (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvule_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvugt (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvugt_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvuge (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvuge_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvslt (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvslt_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvsle (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvsle_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvsgt (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvsgt_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvsge (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvsge_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)

private theorem smtx_typeof_eo_to_smt_apply_apply_bv_compare_head_none
    (q binders a : Term)
    (hCompare :
      q = Term.UOp UserOp.bvult ∨
        q = Term.UOp UserOp.bvule ∨
        q = Term.UOp UserOp.bvugt ∨
        q = Term.UOp UserOp.bvuge ∨
        q = Term.UOp UserOp.bvslt ∨
        q = Term.UOp UserOp.bvsle ∨
        q = Term.UOp UserOp.bvsgt ∨
        q = Term.UOp UserOp.bvsge)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hCompare with
    hBvult | hBvule | hBvugt | hBvuge |
    hBvslt | hBvsle | hBvsgt | hBvsge
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvult (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvult_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvule (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvule_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvugt (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvugt_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvuge (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvuge_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvslt (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvslt_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvsle (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvsle_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvsgt (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvsgt_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvsge (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvsge_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone

private theorem smtx_typeof_bvuaddo_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvuaddo x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvsaddo_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsaddo x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvumulo_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvumulo x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvsmulo_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsmulo x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvusubo_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvusubo x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvssubo_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvssubo x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvsdivo_first_arg_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsdivo x y) = SmtType.None := by
  intro hx
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hx]
  rfl

private theorem smtx_typeof_bvuaddo_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvuaddo x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvsaddo_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsaddo x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvumulo_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvumulo x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvsmulo_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsmulo x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvusubo_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvusubo x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvssubo_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvssubo x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_bvsdivo_second_arg_none
    (x y : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.bvsdivo x y) = SmtType.None := by
  intro hy
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hy]
  exact smtx_typeof_bv_op_2_ret_type_second_none
    (__smtx_typeof x) SmtType.Bool

private theorem smtx_typeof_eo_to_smt_apply_apply_bv_overflow_second_head_none
    (q binders a : Term)
    (hOverflow :
      ∃ z : Term,
        q = Term.Apply (Term.UOp UserOp.bvuaddo) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsaddo) z ∨
          q = Term.Apply (Term.UOp UserOp.bvumulo) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsmulo) z ∨
          q = Term.Apply (Term.UOp UserOp.bvusubo) z ∨
          q = Term.Apply (Term.UOp UserOp.bvssubo) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsdivo) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  have hApplyHeadNone :
      ∀ head : SmtTerm,
        (∀ s d i j, head ≠ SmtTerm.DtSel s d i j) ->
        (∀ s d i, head ≠ SmtTerm.DtTester s d i) ->
        __smtx_typeof head = SmtType.None ->
        __smtx_typeof (SmtTerm.Apply head (__eo_to_smt a)) =
          SmtType.None := by
    intro head hSel hTester hHead
    exact smtx_typeof_apply_head_none_of_non_datatype_head
      head (__eo_to_smt a) hSel hTester hHead
  rcases hOverflow with
    ⟨z, hBvuaddo | hBvsaddo | hBvumulo | hBvsmulo |
      hBvusubo | hBvssubo | hBvsdivo⟩
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvuaddo (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvuaddo_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvsaddo (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvsaddo_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvumulo (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvumulo_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvsmulo (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvsmulo_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvusubo (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvusubo_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvssubo (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvssubo_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)
  · subst q
    change __smtx_typeof
        (SmtTerm.Apply (SmtTerm.bvsdivo (__eo_to_smt z)
          (__eo_to_smt binders)) (__eo_to_smt a)) = SmtType.None
    exact hApplyHeadNone _ (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (smtx_typeof_bvsdivo_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone)

private theorem smtx_typeof_eo_to_smt_apply_apply_bv_overflow_head_none
    (q binders a : Term)
    (hOverflow :
      q = Term.UOp UserOp.bvuaddo ∨
        q = Term.UOp UserOp.bvsaddo ∨
        q = Term.UOp UserOp.bvumulo ∨
        q = Term.UOp UserOp.bvsmulo ∨
        q = Term.UOp UserOp.bvusubo ∨
        q = Term.UOp UserOp.bvssubo ∨
        q = Term.UOp UserOp.bvsdivo)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hOverflow with
    hBvuaddo | hBvsaddo | hBvumulo | hBvsmulo |
    hBvusubo | hBvssubo | hBvsdivo
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvuaddo (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvuaddo_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvsaddo (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvsaddo_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvumulo (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvumulo_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvsmulo (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvsmulo_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvusubo (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvusubo_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvssubo (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvssubo_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.bvsdivo (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_bvsdivo_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone

private theorem smtx_typeof_ite_first_arg_none
    (c t e : SmtTerm) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (SmtTerm.ite c t e) = SmtType.None := by
  intro hc
  rw [typeof_ite_eq, hc]
  rfl

private theorem smtx_typeof_eo_to_smt_apply_apply_bv_pred_to_bv_head_none
    (q binders a : Term)
    (hPredToBv :
      q = Term.UOp UserOp.bvultbv ∨
        q = Term.UOp UserOp.bvsltbv)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hPredToBv with hBvultbv | hBvsltbv
  · subst q
    change
      __smtx_typeof
          (SmtTerm.ite
            (SmtTerm.bvult (__eo_to_smt binders) (__eo_to_smt a))
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
        SmtType.None
    apply smtx_typeof_ite_first_arg_none
    exact smtx_typeof_bvult_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.ite
            (SmtTerm.bvslt (__eo_to_smt binders) (__eo_to_smt a))
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
        SmtType.None
    apply smtx_typeof_ite_first_arg_none
    exact smtx_typeof_bvslt_first_arg_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_bv_pred_to_bv_second_head_none
    (q binders a : Term)
    (hPredToBv :
      ∃ z : Term,
        q = Term.Apply (Term.UOp UserOp.bvultbv) z ∨
          q = Term.Apply (Term.UOp UserOp.bvsltbv) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hPredToBv with ⟨z, hBvultbv | hBvsltbv⟩
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.ite
              (SmtTerm.bvult (__eo_to_smt z) (__eo_to_smt binders))
              (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · apply smtx_typeof_ite_first_arg_none
      exact smtx_typeof_bvult_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.ite
              (SmtTerm.bvslt (__eo_to_smt z) (__eo_to_smt binders))
              (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · apply smtx_typeof_ite_first_arg_none
      exact smtx_typeof_bvslt_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_distinct_head_none
    (binders a : Term)
    (hElem : __eo_to_smt_typed_list_elem_type binders = SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.distinct) binders) a)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite
            (native_Teq (__eo_to_smt_typed_list_elem_type binders)
              SmtType.None)
            SmtTerm.None (__eo_to_smt_distinct binders))
          (__eo_to_smt a)) =
      SmtType.None
  rw [hElem]
  simpa [native_ite, native_Teq] using
    smtx_typeof_apply_none_head (__eo_to_smt a)

private theorem smtx_typeof_eo_to_smt_apply_apply_bvsize_head_none
    (binders a : Term)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_bvsize) binders) a)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite
            (native_zleq 0
              (__smtx_bv_sizeof_type
                (__smtx_typeof (__eo_to_smt binders))))
            (SmtTerm._at_purify
              (SmtTerm.Numeral
                (__smtx_bv_sizeof_type
                  (__smtx_typeof (__eo_to_smt binders)))))
            SmtTerm.None)
          (__eo_to_smt a)) =
      SmtType.None
  rw [hBindersNone]
  have hle :
      native_zleq 0 (__smtx_bv_sizeof_type SmtType.None) = false := by
    rfl
  rw [hle]
  simpa [native_ite] using
    smtx_typeof_apply_none_head (__eo_to_smt a)

private theorem smtx_typeof_eo_to_smt_apply_apply_from_bools_head_none
    (binders a : Term)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) binders) a)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.concat
          (SmtTerm.ite (__eo_to_smt binders) (SmtTerm.Binary 1 1)
            (SmtTerm.Binary 1 0))
          (__eo_to_smt a)) =
      SmtType.None
  apply smtx_typeof_concat_first_arg_none
  exact smtx_typeof_ite_first_arg_none
    (__eo_to_smt binders) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)
    hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_from_bools_second_head_none
    (q binders a : Term)
    (hFromBools :
      ∃ z : Term, q = Term.Apply (Term.UOp UserOp._at_from_bools) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hFromBools with ⟨z, hFromBools⟩
  subst q
  change
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.concat
            (SmtTerm.ite (__eo_to_smt z) (SmtTerm.Binary 1 1)
              (SmtTerm.Binary 1 0))
            (__eo_to_smt binders))
          (__eo_to_smt a)) =
      SmtType.None
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_concat_second_arg_none
      (SmtTerm.ite (__eo_to_smt z) (SmtTerm.Binary 1 1)
        (SmtTerm.Binary 1 0))
      (__eo_to_smt binders) hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_list_set_insert_head_none
    (x ys a : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.set_insert)
              (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
            a)) =
      SmtType.None := by
  change
    __smtx_typeof
        (__eo_to_smt_set_insert
          (Term.Apply (Term.Apply Term.__eo_List_cons x) ys)
          (__eo_to_smt a)) =
      SmtType.None
  simp [__eo_to_smt_set_insert]

private theorem smtx_typeof_eo_to_smt_set_insert_arg_none :
    ∀ xs a,
      __smtx_typeof a = SmtType.None ->
      __smtx_typeof (__eo_to_smt_set_insert xs a) = SmtType.None := by
  intro xs a ha
  cases xs <;> try simp [__eo_to_smt_set_insert]
  case Apply f tail =>
    cases f <;> try simp [__eo_to_smt_set_insert]
    case UOp op =>
      cases op <;> simp [__eo_to_smt_set_insert, ha, native_ite, native_Teq]
    case Apply f' head =>
      cases f' <;> try simp [__eo_to_smt_set_insert]
      case UOp op =>
        cases op <;> try simp [__eo_to_smt_set_insert]
        have hTail :
            __smtx_typeof (__eo_to_smt_set_insert tail a) =
              SmtType.None :=
          smtx_typeof_eo_to_smt_set_insert_arg_none tail a ha
        change
          __smtx_typeof
              (SmtTerm.set_union
                (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail a)) =
            SmtType.None
        exact
          smtx_typeof_set_union_second_arg_none
            (SmtTerm.set_singleton (__eo_to_smt head))
            (__eo_to_smt_set_insert tail a) hTail
termination_by xs a _ => xs

private theorem eo_to_smt_set_insert_ne_dt_sel_of_base
    (xs : Term) (base : SmtTerm)
    (hBase : ∀ s d i j, base ≠ SmtTerm.DtSel s d i j)
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt_set_insert xs base ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases xs <;> try cases h
  case Apply f tail =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> try cases h
      case _at__at_TypedList_nil =>
        cases hTy :
            native_Teq (__smtx_typeof base)
              (SmtType.Set (__eo_to_smt_type tail)) <;>
          simp [__eo_to_smt_set_insert, hTy, native_ite] at h
        exact hBase s d i j h
    case Apply f' head =>
      cases f' <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_set_insert_ne_dt_tester_of_base
    (xs : Term) (base : SmtTerm)
    (hBase : ∀ s d i, base ≠ SmtTerm.DtTester s d i)
    (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt_set_insert xs base ≠ SmtTerm.DtTester s d i := by
  intro h
  cases xs <;> try cases h
  case Apply f tail =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> try cases h
      case _at__at_TypedList_nil =>
        cases hTy :
            native_Teq (__smtx_typeof base)
              (SmtType.Set (__eo_to_smt_type tail)) <;>
          simp [__eo_to_smt_set_insert, hTy, native_ite] at h
        exact hBase s d i h
    case Apply f' head =>
      cases f' <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem smtx_typeof_eo_to_smt_apply_apply_set_insert_second_head_none
    (q binders a : Term)
    (hSetInsert :
      ∃ w : Term, q = Term.Apply (Term.UOp UserOp.set_insert) w)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None)
    (hBindersSel :
      ∀ s d i j, __eo_to_smt binders ≠ SmtTerm.DtSel s d i j)
    (hBindersTester :
      ∀ s d i, __eo_to_smt binders ≠ SmtTerm.DtTester s d i) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hSetInsert with ⟨w, rfl⟩
  change
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt_set_insert w (__eo_to_smt binders))
          (__eo_to_smt a)) =
      SmtType.None
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    exact
      eo_to_smt_set_insert_ne_dt_sel_of_base
        w (__eo_to_smt binders) hBindersSel s d i j h
  · intro s d i h
    exact
      eo_to_smt_set_insert_ne_dt_tester_of_base
        w (__eo_to_smt binders) hBindersTester s d i h
  · exact
      smtx_typeof_eo_to_smt_set_insert_arg_none
        w (__eo_to_smt binders) hBindersNone

private theorem smtx_typeof_eo_to_smt_exists_body_none :
    ∀ xs body,
      __smtx_typeof body = SmtType.None ->
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.None := by
  intro xs body hBody
  cases xs <;> try simp [__eo_to_smt_exists]
  case __eo_List_nil =>
    exact hBody
  case Apply f tail =>
    cases f <;> try simp [__eo_to_smt_exists]
    case Apply f' head =>
      cases f' <;> try simp [__eo_to_smt_exists]
      case __eo_List_cons =>
        cases head <;> try simp [__eo_to_smt_exists]
        case Var name T =>
          cases name <;> try simp [__eo_to_smt_exists]
          case String s =>
            have hTail :
                __smtx_typeof (__eo_to_smt_exists tail body) =
                  SmtType.None :=
              smtx_typeof_eo_to_smt_exists_body_none tail body hBody
            change
              __smtx_typeof
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists tail body)) =
                SmtType.None
            rw [smtx_typeof_exists_term_eq, hTail]
            rfl
termination_by xs body _ => xs

private theorem eo_to_smt_exists_ne_dt_sel_of_body
    (xs : Term) (body : SmtTerm)
    (hBody : ∀ s d i j, body ≠ SmtTerm.DtSel s d i j)
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt_exists xs body ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases xs
  case __eo_List_nil =>
    simp [__eo_to_smt_exists] at h
    exact hBody s d i j h
  case Apply f tail =>
    cases f
    case Apply f' head =>
      cases f'
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name <;> simp [__eo_to_smt_exists] at h
        all_goals simp [__eo_to_smt_exists] at h
      all_goals simp [__eo_to_smt_exists] at h
    all_goals simp [__eo_to_smt_exists] at h
  all_goals simp [__eo_to_smt_exists] at h

private theorem eo_to_smt_exists_ne_dt_tester_of_body
    (xs : Term) (body : SmtTerm)
    (hBody : ∀ s d i, body ≠ SmtTerm.DtTester s d i)
    (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt_exists xs body ≠ SmtTerm.DtTester s d i := by
  intro h
  cases xs
  case __eo_List_nil =>
    simp [__eo_to_smt_exists] at h
    exact hBody s d i h
  case Apply f tail =>
    cases f
    case Apply f' head =>
      cases f'
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name <;> simp [__eo_to_smt_exists] at h
        all_goals simp [__eo_to_smt_exists] at h
      all_goals simp [__eo_to_smt_exists] at h
    all_goals simp [__eo_to_smt_exists] at h
  all_goals simp [__eo_to_smt_exists] at h

private theorem smtx_typeof_eo_to_smt_apply_apply_quant_second_head_none
    (q binders a : Term)
    (hQuant :
      ∃ w : Term,
        q = Term.Apply (Term.UOp UserOp.forall) w ∨
          q = Term.Apply (Term.UOp UserOp.exists) w)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None)
    (hBindersSel :
      ∀ s d i j, __eo_to_smt binders ≠ SmtTerm.DtSel s d i j)
    (hBindersTester :
      ∀ s d i, __eo_to_smt binders ≠ SmtTerm.DtTester s d i) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hQuant with ⟨w, hForall | hExists⟩
  · subst q
    by_cases hNil : w = Term.__eo_List_nil
    · subst w
      change
        __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
      exact smtx_typeof_apply_none_head (__eo_to_smt a)
    · change
        __smtx_typeof
            (SmtTerm.Apply
              (__eo_to_smt (qforall w binders)) (__eo_to_smt a)) =
          SmtType.None
      rw [eo_to_smt_forall_eq w binders hNil]
      apply smtx_typeof_apply_head_none_of_non_datatype_head
      · intro s d i j h
        cases h
      · intro s d i h
        cases h
      · rw [typeof_not_eq]
        have hExistsNone :
            __smtx_typeof
                (__eo_to_smt_exists w
                  (SmtTerm.not (__eo_to_smt binders))) =
              SmtType.None :=
          smtx_typeof_eo_to_smt_exists_body_none w
            (SmtTerm.not (__eo_to_smt binders))
            (by rw [typeof_not_eq, hBindersNone]
                simp [native_ite, native_Teq])
        rw [hExistsNone]
        simp [native_ite, native_Teq]
  · subst q
    by_cases hNil : w = Term.__eo_List_nil
    · subst w
      change
        __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
      exact smtx_typeof_apply_none_head (__eo_to_smt a)
    · change
        __smtx_typeof
            (SmtTerm.Apply
              (__eo_to_smt (qexists w binders)) (__eo_to_smt a)) =
          SmtType.None
      rw [eo_to_smt_exists_eq w binders hNil]
      apply smtx_typeof_apply_head_none_of_non_datatype_head
      · intro s d i j h
        exact
          eo_to_smt_exists_ne_dt_sel_of_body
            w (__eo_to_smt binders) hBindersSel s d i j h
      · intro s d i h
        exact
          eo_to_smt_exists_ne_dt_tester_of_body
            w (__eo_to_smt binders) hBindersTester s d i h
      · exact
          smtx_typeof_eo_to_smt_exists_body_none
            w (__eo_to_smt binders) hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_deq_diff_head_none
    (q binders a : Term)
    (hDiff :
      q = Term.UOp UserOp._at_array_deq_diff ∨
        q = Term.UOp UserOp._at_sets_deq_diff)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hDiff with hArrayDiff | hSetDiff
  · subst q
    change
      __smtx_typeof
          (__eo_to_smt_array_deq_diff (__eo_to_smt binders)
            (__smtx_typeof (__eo_to_smt binders)) (__eo_to_smt a)
            (__smtx_typeof (__eo_to_smt a))) =
        SmtType.None
    rw [hBindersNone]
    simp [__eo_to_smt_array_deq_diff]
  · subst q
    change
      __smtx_typeof
          (__eo_to_smt_sets_deq_diff (__eo_to_smt binders)
            (__smtx_typeof (__eo_to_smt binders)) (__eo_to_smt a)
            (__smtx_typeof (__eo_to_smt a))) =
        SmtType.None
    rw [hBindersNone]
    simp [__eo_to_smt_sets_deq_diff]

private theorem smtx_typeof_eo_to_smt_apply_apply_deq_diff_second_head_none
    (q binders a : Term)
    (hDiff :
      ∃ z : Term,
        q = Term.Apply (Term.UOp UserOp._at_array_deq_diff) z ∨
          q = Term.Apply (Term.UOp UserOp._at_sets_deq_diff) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hDiff with ⟨z, hArrayDiff | hSetDiff⟩
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt_array_deq_diff (__eo_to_smt z)
              (__smtx_typeof (__eo_to_smt z)) (__eo_to_smt binders)
              (__smtx_typeof (__eo_to_smt binders)))
            (__eo_to_smt a)) =
        SmtType.None
    rw [hBindersNone]
    cases __smtx_typeof (__eo_to_smt z) <;>
      simp [__eo_to_smt_array_deq_diff, smtx_typeof_apply_none_head]
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt_sets_deq_diff (__eo_to_smt z)
              (__smtx_typeof (__eo_to_smt z)) (__eo_to_smt binders)
              (__smtx_typeof (__eo_to_smt binders)))
            (__eo_to_smt a)) =
        SmtType.None
    rw [hBindersNone]
    cases __smtx_typeof (__eo_to_smt z) <;>
      simp [__eo_to_smt_sets_deq_diff, smtx_typeof_apply_none_head]

private theorem smtx_typeof_str_substr_first_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_substr x y z) = SmtType.None := by
  intro hx
  rw [typeof_str_substr_eq, hx]
  rfl

private theorem smtx_typeof_str_substr_third_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof z = SmtType.None ->
    __smtx_typeof (SmtTerm.str_substr x y z) = SmtType.None := by
  intro hz
  rw [typeof_str_substr_eq, hz]
  cases __smtx_typeof x <;> cases __smtx_typeof y <;>
    simp [__smtx_typeof_str_substr]

private theorem smtx_typeof_not_arg_none
    (x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.not x) = SmtType.None := by
  intro hx
  rw [typeof_not_eq, hx]
  rfl

private theorem smtx_typeof_choice_nth_body_none
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof body = SmtType.None ->
    __smtx_typeof (SmtTerm.choice_nth s T body native_nat_zero) =
      SmtType.None := by
  intro hBody
  rw [smtx_typeof_choice_nth_term_eq]
  simp [__smtx_typeof_choice_nth, hBody, native_ite, native_Teq]

private theorem smtx_typeof_choice_nth_succ_eq_skolemize_of_non_none
    (s : native_String) (T : SmtType) (body : SmtTerm) (n : native_Nat)
    (hNN : term_has_non_none_type (SmtTerm.choice_nth s T body n.succ)) :
    __smtx_typeof (SmtTerm.choice_nth s T body n.succ) =
      __smtx_typeof (__eo_to_smt_quantifiers_skolemize body n) := by
  cases body
  case «exists» s' U body' =>
    simpa [__eo_to_smt_quantifiers_skolemize] using
      choice_nth_succ_typeof_tail_of_non_none hNN
  all_goals
    exfalso
    unfold term_has_non_none_type at hNN
    apply hNN
    simp [__smtx_typeof, __smtx_typeof_choice_nth]

private theorem quantifiers_skolemize_non_none_of_choice_nth_succ_non_none
    (s : native_String) (T : SmtType) (body : SmtTerm) (n : native_Nat)
    (hNN : __smtx_typeof (SmtTerm.choice_nth s T body n.succ) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize body n) ≠ SmtType.None := by
  have hTermNN : term_has_non_none_type (SmtTerm.choice_nth s T body n.succ) := by
    unfold term_has_non_none_type
    exact hNN
  have hEq :=
    smtx_typeof_choice_nth_succ_eq_skolemize_of_non_none
      (s := s) (T := T) (body := body) (n := n) hTermNN
  intro hNone
  apply hNN
  rw [hEq, hNone]

private theorem choice_nth_head_type_wf_of_non_none
    (s : native_String) (T : SmtType) (body : SmtTerm) (n : native_Nat)
    (hNN : __smtx_typeof (SmtTerm.choice_nth s T body n) ≠ SmtType.None) :
    __smtx_type_wf T = true := by
  cases n with
  | zero =>
      have hTermNN : term_has_non_none_type (SmtTerm.choice_nth s T body 0) := by
        unfold term_has_non_none_type
        exact hNN
      have hGuardTy :
          __smtx_typeof (SmtTerm.choice_nth s T body 0) =
            __smtx_typeof_guard_wf T T :=
        choice_term_guard_type_of_non_none hTermNN
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        intro hNone
        apply hNN
        rw [hGuardTy, hNone]
      exact smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  | succ n =>
      cases body with
      | «exists» s' U body' =>
          have hGuardNN :
              __smtx_typeof_guard_wf T (__smtx_typeof_choice_nth U body' n) ≠
                SmtType.None := by
            intro hNone
            apply hNN
            simp [__smtx_typeof, __smtx_typeof_choice_nth, hNone]
          exact
            smtx_typeof_guard_wf_wf_of_non_none
              T (__smtx_typeof_choice_nth U body' n) hGuardNN
      | _ =>
          exfalso
          apply hNN
          simp [__smtx_typeof, __smtx_typeof_choice_nth]

private theorem type_wf_of_quantifiers_skolemize_cons_non_none
    (s : native_String) (T a : Term) (body : SmtTerm) (n : native_Nat)
    (hNN :
      __smtx_typeof
          (__eo_to_smt_quantifiers_skolemize
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
              body) n) ≠
        SmtType.None) :
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  have hChoiceNN :
      __smtx_typeof
          (SmtTerm.choice_nth s (__eo_to_smt_type T)
            (__eo_to_smt_exists a body) n) ≠
        SmtType.None := by
    intro hChoiceNone
    apply hNN
    change
      __smtx_typeof
          (__eo_to_smt_quantifiers_skolemize
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
              body) n) =
        SmtType.None
    rw [TranslationProofs.eo_to_smt_exists_cons]
    exact hChoiceNone
  exact choice_nth_head_type_wf_of_non_none
    (s := s) (T := __eo_to_smt_type T)
    (body := __eo_to_smt_exists a body) (n := n) hChoiceNN

private theorem choice_nth_non_none_of_quantifiers_skolemize_cons_non_none
    (s : native_String) (T a : Term) (body : SmtTerm) (n : native_Nat)
    (hNN :
      __smtx_typeof
          (__eo_to_smt_quantifiers_skolemize
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
              body) n) ≠
        SmtType.None) :
    __smtx_typeof
        (SmtTerm.choice_nth s (__eo_to_smt_type T)
          (__eo_to_smt_exists a body) n) ≠
      SmtType.None := by
  intro hChoiceNone
  apply hNN
  change
    __smtx_typeof
        (__eo_to_smt_quantifiers_skolemize
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
            body) n) =
      SmtType.None
  rw [TranslationProofs.eo_to_smt_exists_cons]
  exact hChoiceNone

private theorem smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
    (s : native_String) (T a : Term) (body : SmtTerm)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
          body) =
      SmtType.Bool := by
  rw [TranslationProofs.eo_to_smt_exists_cons]
  rw [smtx_typeof_exists_term_eq]
  simp [hTailBool, native_ite, native_Teq, __smtx_typeof_guard_wf, hWf]

private theorem eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
    (xs : Term) (body : SmtTerm) (n : native_Nat)
    (hBodyNoExists : ∀ s T F, body ≠ SmtTerm.exists s T F) :
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize
      (__eo_to_smt_exists xs body) n) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  induction n generalizing xs body with
  | zero =>
      intro hNN
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name T =>
                      cases name with
                      | String s =>
                          have hChoiceNN :
                              term_has_non_none_type
                                (SmtTerm.choice_nth s (__eo_to_smt_type T)
                                  (__eo_to_smt_exists a body) 0) := by
                            unfold term_has_non_none_type
                            exact choice_nth_non_none_of_quantifiers_skolemize_cons_non_none
                              (s := s) (T := T) (a := a) (body := body) (n := 0) hNN
                          have hBodyBool :
                              __smtx_typeof (__eo_to_smt_exists a body) =
                                SmtType.Bool :=
                            TranslationProofs.choice_nth_body_bool_of_non_none
                              hChoiceNN
                          have hWf :=
                            type_wf_of_quantifiers_skolemize_cons_non_none
                              (s := s) (T := T) (a := a) (body := body) (n := 0) hNN
                          exact smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
                            (s := s) (T := T) (a := a) (body := body) hWf hBodyBool
                      | _ =>
                          exfalso
                          apply hNN
                          simp [__eo_to_smt_quantifiers_skolemize,
                            __eo_to_smt_exists]
                  | _ =>
                      exfalso
                      apply hNN
                      simp [__eo_to_smt_quantifiers_skolemize,
                        __eo_to_smt_exists]
              | _ =>
                  exfalso
                  apply hNN
                  simp [__eo_to_smt_quantifiers_skolemize,
                    __eo_to_smt_exists]
          | _ =>
              exfalso
              apply hNN
              simp [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]
      | _ =>
          exfalso
          apply hNN
          simp [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]
  | succ n ih =>
      intro hNN
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name T =>
                      cases name with
                      | String s =>
                          have hTailNN :
                              __smtx_typeof
                                  (__eo_to_smt_quantifiers_skolemize
                                    (__eo_to_smt_exists a body) n) ≠
                                SmtType.None := by
                            have hChoiceSucc :
                                __smtx_typeof
                                    (SmtTerm.choice_nth s (__eo_to_smt_type T)
                                      (__eo_to_smt_exists a body) n.succ) ≠
                                  SmtType.None :=
                              choice_nth_non_none_of_quantifiers_skolemize_cons_non_none
                                (s := s) (T := T) (a := a) (body := body)
                                (n := n.succ) hNN
                            exact
                              quantifiers_skolemize_non_none_of_choice_nth_succ_non_none
                                (s := s) (T := __eo_to_smt_type T)
                                (body := __eo_to_smt_exists a body)
                                (n := n) hChoiceSucc
                          have hTailBool :
                              __smtx_typeof (__eo_to_smt_exists a body) =
                                SmtType.Bool :=
                            ih a body hBodyNoExists hTailNN
                          have hWf :=
                            type_wf_of_quantifiers_skolemize_cons_non_none
                              (s := s) (T := T) (a := a) (body := body)
                              (n := n.succ) hNN
                          exact smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
                            (s := s) (T := T) (a := a) (body := body) hWf
                            hTailBool
                      | _ =>
                          exfalso
                          apply hNN
                          simp [__eo_to_smt_quantifiers_skolemize,
                            __eo_to_smt_exists]
                  | _ =>
                      exfalso
                      apply hNN
                      simp [__eo_to_smt_quantifiers_skolemize,
                        __eo_to_smt_exists]
              | _ =>
                  exfalso
                  apply hNN
                  simp [__eo_to_smt_quantifiers_skolemize,
                    __eo_to_smt_exists]
          | _ =>
              exfalso
              apply hNN
              simp [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]
      | _ =>
          exfalso
          cases body
          case «exists» s T F =>
            exact hBodyNoExists s T F rfl
          all_goals
            apply hNN
            simp [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]

private theorem smtx_typeof_eo_to_smt_apply_apply_strings_deq_diff_head_none
    (binders a : Term)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) binders)
            a)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int
          (SmtTerm.not
            (SmtTerm.eq
              (SmtTerm.str_substr (__eo_to_smt binders)
                (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                (SmtTerm.Numeral 1))
              (SmtTerm.str_substr (__eo_to_smt a)
                (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                (SmtTerm.Numeral 1))))
          native_nat_zero) =
      SmtType.None
  apply smtx_typeof_choice_nth_body_none
  apply smtx_typeof_not_arg_none
  apply smtx_typeof_eq_first_arg_none
  apply smtx_typeof_str_substr_first_arg_none
  exact hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_strings_deq_diff_second_head_none
    (q binders a : Term)
    (hStringsDeqDiff :
      ∃ z : Term, q = Term.Apply (Term.UOp UserOp._at_strings_deq_diff) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hStringsDeqDiff with ⟨z, hStringsDeqDiff⟩
  subst q
  change
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int
            (SmtTerm.not
              (SmtTerm.eq
                (SmtTerm.str_substr (__eo_to_smt z)
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                  (SmtTerm.Numeral 1))
                (SmtTerm.str_substr (__eo_to_smt binders)
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                  (SmtTerm.Numeral 1))))
            native_nat_zero)
          (__eo_to_smt a)) =
      SmtType.None
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · apply smtx_typeof_choice_nth_body_none
    apply smtx_typeof_not_arg_none
    apply smtx_typeof_eq_second_arg_none
    apply smtx_typeof_str_substr_first_arg_none
    exact hBindersNone

private theorem smtx_typeof_str_to_int_arg_none
    (x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_to_int x) = SmtType.None := by
  intro hx
  rw [typeof_str_to_int_eq, hx]
  rfl

private theorem smtx_typeof_str_len_arg_none
    (x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_len x) = SmtType.None := by
  intro hx
  rw [typeof_str_len_eq, hx]
  rfl

private theorem smtx_typeof_eo_to_smt_apply_apply_string_result_head_none
    (q binders a : Term)
    (hStringResult :
      q = Term.UOp UserOp._at_strings_stoi_result ∨
        q = Term.UOp UserOp._at_strings_itos_result ∨
        q = Term.UOp UserOp._at_strings_num_occur)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hStringResult with hStoi | hItos | hNumOccur
  · subst q
    change
      __smtx_typeof
          (SmtTerm.str_to_int
            (SmtTerm.str_substr (__eo_to_smt binders)
              (SmtTerm.Numeral 0) (__eo_to_smt a))) =
        SmtType.None
    apply smtx_typeof_str_to_int_arg_none
    apply smtx_typeof_str_substr_first_arg_none
    exact hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.mod (__eo_to_smt binders)
            (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt a))) =
        SmtType.None
    exact smtx_typeof_mod_first_arg_none
      (__eo_to_smt binders)
      (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt a))
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.div
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt binders))
              (SmtTerm.str_len
                (SmtTerm.str_replace_all (__eo_to_smt binders)
                  (__eo_to_smt a)
                  (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
            (SmtTerm.str_len (__eo_to_smt a))) =
        SmtType.None
    apply smtx_typeof_div_first_arg_none
    apply smtx_typeof_neg_first_arg_none
    apply smtx_typeof_str_len_arg_none
    exact hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_string_result_second_head_none
    (q binders a : Term)
    (hStringResult :
      ∃ z : Term,
        q = Term.Apply (Term.UOp UserOp._at_strings_stoi_result) z ∨
          q = Term.Apply (Term.UOp UserOp._at_strings_itos_result) z ∨
          q = Term.Apply (Term.UOp UserOp._at_strings_num_occur) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hStringResult with ⟨z, hStoi | hItos | hNumOccur⟩
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_to_int
              (SmtTerm.str_substr (__eo_to_smt z)
                (SmtTerm.Numeral 0) (__eo_to_smt binders)))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · apply smtx_typeof_str_to_int_arg_none
      apply smtx_typeof_str_substr_third_arg_none
      exact hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.mod (__eo_to_smt z)
              (SmtTerm.multmult (SmtTerm.Numeral 10)
                (__eo_to_smt binders)))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · apply smtx_typeof_mod_second_arg_none
      apply smtx_typeof_multmult_second_arg_none
      exact hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.div
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt z))
                (SmtTerm.str_len
                  (SmtTerm.str_replace_all (__eo_to_smt z)
                    (__eo_to_smt binders)
                    (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
              (SmtTerm.str_len (__eo_to_smt binders)))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · apply smtx_typeof_div_second_arg_none
      apply smtx_typeof_str_len_arg_none
      exact hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_misc_second_head_none
    (q binders a : Term)
    (hMisc :
      ∃ z : Term,
        q = Term.Apply (Term.UOp UserOp._at_from_bools) z ∨
          q = Term.Apply (Term.UOp UserOp._at_array_deq_diff) z ∨
          q = Term.Apply (Term.UOp UserOp._at_sets_deq_diff) z ∨
          q = Term.Apply (Term.UOp UserOp._at_strings_deq_diff) z ∨
          q = Term.Apply (Term.UOp UserOp._at_strings_stoi_result) z ∨
          q = Term.Apply (Term.UOp UserOp._at_strings_itos_result) z ∨
          q = Term.Apply (Term.UOp UserOp._at_strings_num_occur) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hMisc with
    ⟨z, hFromBools | hArrayDiff | hSetDiff | hStringsDeqDiff |
      hStoi | hItos | hNumOccur⟩
  · exact
      smtx_typeof_eo_to_smt_apply_apply_from_bools_second_head_none
        q binders a ⟨z, hFromBools⟩ hBindersNone
  · exact
      smtx_typeof_eo_to_smt_apply_apply_deq_diff_second_head_none
        q binders a ⟨z, Or.inl hArrayDiff⟩ hBindersNone
  · exact
      smtx_typeof_eo_to_smt_apply_apply_deq_diff_second_head_none
        q binders a ⟨z, Or.inr hSetDiff⟩ hBindersNone
  · exact
      smtx_typeof_eo_to_smt_apply_apply_strings_deq_diff_second_head_none
        q binders a ⟨z, hStringsDeqDiff⟩ hBindersNone
  · exact
      smtx_typeof_eo_to_smt_apply_apply_string_result_second_head_none
        q binders a ⟨z, Or.inl hStoi⟩ hBindersNone
  · exact
      smtx_typeof_eo_to_smt_apply_apply_string_result_second_head_none
        q binders a ⟨z, Or.inr (Or.inl hItos)⟩ hBindersNone
  · exact
      smtx_typeof_eo_to_smt_apply_apply_string_result_second_head_none
        q binders a ⟨z, Or.inr (Or.inr hNumOccur)⟩ hBindersNone

private theorem smtx_typeof_ite_second_arg_none
    (c t e : SmtTerm) :
    __smtx_typeof t = SmtType.None ->
    __smtx_typeof (SmtTerm.ite c t e) = SmtType.None := by
  intro ht
  rw [typeof_ite_eq, ht]
  cases __smtx_typeof c <;> cases __smtx_typeof e <;>
    simp [__smtx_typeof_ite, native_ite, native_Teq]

private theorem smtx_typeof_ite_cond_none
    (c t e : SmtTerm) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (SmtTerm.ite c t e) = SmtType.None := by
  intro hc
  rw [typeof_ite_eq, hc]
  rfl

private theorem smtx_typeof_ite_third_arg_none
    (c t e : SmtTerm) :
    __smtx_typeof e = SmtType.None ->
    __smtx_typeof (SmtTerm.ite c t e) = SmtType.None := by
  intro he
  rw [typeof_ite_eq, he]
  cases __smtx_typeof c <;> cases __smtx_typeof t <;>
    simp [__smtx_typeof_ite, native_ite, native_Teq]

private theorem smtx_typeof_str_substr_second_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_substr x y z) = SmtType.None := by
  intro hy
  rw [typeof_str_substr_eq, hy]
  cases __smtx_typeof x <;> cases __smtx_typeof z <;>
    simp [__smtx_typeof_str_substr]

private theorem smtx_typeof_store_second_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.store x y z) = SmtType.None := by
  intro hy
  rw [typeof_store_eq, hy]
  cases hX : __smtx_typeof x with
  | Map A B =>
      by_cases hA : A = SmtType.None
      · have hxNN : term_has_non_none_type x := by
          unfold term_has_non_none_type
          rw [hX]
          simp
        have hNoNone := term_type_has_no_none_components_of_non_none x hxNN
        have hNoNoneAB :
            type_has_no_none_components A ∧
              type_has_no_none_components B := by
          simpa [hX, type_has_no_none_components] using hNoNone
        exact False.elim
          ((type_has_no_none_components_non_none hNoNoneAB.1) hA)
      · simp [__smtx_typeof_store, native_ite, native_Teq, hA]
  | _ =>
      simp [__smtx_typeof_store]

private theorem smtx_typeof_store_third_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof z = SmtType.None ->
    __smtx_typeof (SmtTerm.store x y z) = SmtType.None := by
  intro hz
  rw [typeof_store_eq, hz]
  cases hX : __smtx_typeof x with
  | Map A B =>
      by_cases hB : B = SmtType.None
      · have hxNN : term_has_non_none_type x := by
          unfold term_has_non_none_type
          rw [hX]
          simp
        have hNoNone := term_type_has_no_none_components_of_non_none x hxNN
        have hNoNoneAB :
            type_has_no_none_components A ∧
              type_has_no_none_components B := by
          simpa [hX, type_has_no_none_components] using hNoNone
        exact False.elim
          ((type_has_no_none_components_non_none hNoNoneAB.2) hB)
      · simp [__smtx_typeof_store, native_ite, native_Teq, hB]
  | _ =>
      simp [__smtx_typeof_store]

private theorem smtx_typeof_str_replace_second_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_replace x y z) = SmtType.None := by
  intro hy
  rw [typeof_str_replace_eq, hy]
  cases __smtx_typeof x <;> cases __smtx_typeof z <;>
    simp [__smtx_typeof_seq_op_3]

private theorem smtx_typeof_str_replace_third_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof z = SmtType.None ->
    __smtx_typeof (SmtTerm.str_replace x y z) = SmtType.None := by
  intro hz
  rw [typeof_str_replace_eq, hz]
  cases __smtx_typeof x <;> cases __smtx_typeof y <;>
    simp [__smtx_typeof_seq_op_3]

private theorem smtx_typeof_str_indexof_second_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof x y z) = SmtType.None := by
  intro hy
  rw [typeof_str_indexof_eq, hy]
  cases __smtx_typeof x <;> cases __smtx_typeof z <;>
    simp [__smtx_typeof_str_indexof]

private theorem smtx_typeof_str_indexof_third_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof z = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof x y z) = SmtType.None := by
  intro hz
  rw [typeof_str_indexof_eq, hz]
  cases __smtx_typeof x <;> cases __smtx_typeof y <;>
    simp [__smtx_typeof_str_indexof]

private theorem smtx_typeof_str_update_second_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_update x y z) = SmtType.None := by
  intro hy
  rw [typeof_str_update_eq, hy]
  cases __smtx_typeof x <;> cases __smtx_typeof z <;>
    simp [__smtx_typeof_str_update]

private theorem smtx_typeof_str_update_third_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof z = SmtType.None ->
    __smtx_typeof (SmtTerm.str_update x y z) = SmtType.None := by
  intro hz
  rw [typeof_str_update_eq, hz]
  cases __smtx_typeof x <;> cases __smtx_typeof y <;>
    simp [__smtx_typeof_str_update]

private theorem smtx_typeof_str_replace_all_second_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_replace_all x y z) = SmtType.None := by
  intro hy
  rw [typeof_str_replace_all_eq, hy]
  cases __smtx_typeof x <;> cases __smtx_typeof z <;>
    simp [__smtx_typeof_seq_op_3]

private theorem smtx_typeof_str_replace_all_third_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof z = SmtType.None ->
    __smtx_typeof (SmtTerm.str_replace_all x y z) = SmtType.None := by
  intro hz
  rw [typeof_str_replace_all_eq, hz]
  cases __smtx_typeof x <;> cases __smtx_typeof y <;>
    simp [__smtx_typeof_seq_op_3]

private theorem smtx_typeof_str_replace_re_second_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_replace_re x y z) = SmtType.None := by
  intro hy
  rw [typeof_str_replace_re_eq, hy]
  cases __smtx_typeof x <;> cases __smtx_typeof z <;>
    simp [native_ite, native_Teq]

private theorem smtx_typeof_str_replace_re_third_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof z = SmtType.None ->
    __smtx_typeof (SmtTerm.str_replace_re x y z) = SmtType.None := by
  intro hz
  rw [typeof_str_replace_re_eq, hz]
  cases __smtx_typeof x <;> cases __smtx_typeof y <;>
    simp [native_ite, native_Teq]

private theorem smtx_typeof_str_replace_re_all_second_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_replace_re_all x y z) =
      SmtType.None := by
  intro hy
  rw [typeof_str_replace_re_all_eq, hy]
  cases __smtx_typeof x <;> cases __smtx_typeof z <;>
    simp [native_ite, native_Teq]

private theorem smtx_typeof_str_replace_re_all_third_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof z = SmtType.None ->
    __smtx_typeof (SmtTerm.str_replace_re_all x y z) =
      SmtType.None := by
  intro hz
  rw [typeof_str_replace_re_all_eq, hz]
  cases __smtx_typeof x <;> cases __smtx_typeof y <;>
    simp [native_ite, native_Teq]

private theorem smtx_typeof_str_indexof_re_second_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re x y z) =
      SmtType.None := by
  intro hy
  rw [typeof_str_indexof_re_eq, hy]
  cases __smtx_typeof x <;> cases __smtx_typeof z <;>
    simp [native_ite, native_Teq]

private theorem smtx_typeof_str_indexof_re_third_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof z = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re x y z) =
      SmtType.None := by
  intro hz
  rw [typeof_str_indexof_re_eq, hz]
  cases __smtx_typeof x <;> cases __smtx_typeof y <;>
    simp [native_ite, native_Teq]

private theorem smtx_typeof_str_indexof_re_first_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re x y z) =
      SmtType.None := by
  intro hx
  rw [typeof_str_indexof_re_eq, hx]
  cases __smtx_typeof y <;> cases __smtx_typeof z <;>
    simp [native_ite, native_Teq]

private theorem smtx_typeof_apply_str_indexof_re_head_none
    (x y z w : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_indexof_re x y z) w) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_str_indexof_re_first_arg_none x y z hx

private theorem smtx_typeof_str_indexof_re_split_second_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof y = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re_split x y z) =
      SmtType.None := by
  intro hy
  rw [typeof_str_indexof_re_split_eq, hy]
  cases __smtx_typeof x <;> cases __smtx_typeof z <;>
    simp [native_ite, native_Teq]

private theorem smtx_typeof_str_indexof_re_split_third_arg_none
    (x y z : SmtTerm) :
    __smtx_typeof z = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re_split x y z) =
      SmtType.None := by
  intro hz
  rw [typeof_str_indexof_re_split_eq, hz]
  cases __smtx_typeof x <;> cases __smtx_typeof y <;>
    simp [native_ite, native_Teq]

private theorem smtx_typeof_eo_to_smt_apply_apply_ternary_middle_head_none
    (q binders a : Term)
    (hTernary :
      ∃ z : Term,
          q = Term.Apply (Term.UOp UserOp.ite) z ∨
          q = Term.Apply (Term.UOp UserOp.bvite) z ∨
          q = Term.Apply (Term.UOp UserOp.store) z ∨
          q = Term.Apply (Term.UOp UserOp.str_substr) z ∨
          q = Term.Apply (Term.UOp UserOp.str_replace) z ∨
          q = Term.Apply (Term.UOp UserOp.str_indexof) z ∨
          q = Term.Apply (Term.UOp UserOp.str_update) z ∨
          q = Term.Apply (Term.UOp UserOp.str_replace_all) z ∨
          q = Term.Apply (Term.UOp UserOp.str_replace_re) z ∨
          q = Term.Apply (Term.UOp UserOp.str_replace_re_all) z ∨
          q = Term.Apply (Term.UOp UserOp.str_indexof_re) z ∨
          q = Term.Apply (Term.UOp UserOp.str_indexof_re_split) z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hTernary with
    ⟨z, hIte | hBvite | hStore | hSubstr | hReplace | hIndexof | hUpdate |
      hReplaceAll | hReplaceRe | hReplaceReAll | hIndexofRe |
      hIndexofReSplit⟩
  · subst q
    change
      __smtx_typeof
          (SmtTerm.ite (__eo_to_smt z) (__eo_to_smt binders)
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_ite_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
            (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_ite_second_arg_none
      (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.store (__eo_to_smt z) (__eo_to_smt binders)
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_store_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt z) (__eo_to_smt binders)
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_str_substr_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.str_replace (__eo_to_smt z) (__eo_to_smt binders)
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_str_replace_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt binders)
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_str_indexof_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.str_update (__eo_to_smt z) (__eo_to_smt binders)
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_str_update_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.str_replace_all (__eo_to_smt z)
            (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_str_replace_all_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.str_replace_re (__eo_to_smt z)
            (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_str_replace_re_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.str_replace_re_all (__eo_to_smt z)
            (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_str_replace_re_all_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.str_indexof_re (__eo_to_smt z)
            (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_str_indexof_re_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.str_indexof_re_split (__eo_to_smt z)
            (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_str_indexof_re_split_second_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_ternary_last_head_none
    (q binders a : Term)
    (hTernary :
      ∃ x y : Term,
          q = Term.Apply (Term.Apply (Term.UOp UserOp.ite) x) y ∨
          q = Term.Apply (Term.Apply (Term.UOp UserOp.bvite) x) y ∨
          q = Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y ∨
          q = Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y ∨
          q = Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x) y ∨
          q = Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y ∨
          q = Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y ∨
          q = Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x) y ∨
          q = Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x) y ∨
          q = Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) x) y ∨
          q = Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y ∨
          q = Term.Apply
            (Term.Apply (Term.UOp UserOp.str_indexof_re_split) x) y)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hTernary with
    ⟨x, y, hIte | hBvite | hStore | hSubstr | hReplace | hIndexof |
      hUpdate | hReplaceAll | hReplaceRe | hReplaceReAll | hIndexofRe |
      hIndexofReSplit⟩
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.ite (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_ite_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.ite
              (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Binary 1 1))
              (__eo_to_smt y) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_ite_third_arg_none
        (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Binary 1 1))
        (__eo_to_smt y) (__eo_to_smt binders) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.store (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_store_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_substr (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_str_substr_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_str_replace_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_indexof (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_str_indexof_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_update (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_str_update_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_replace_all (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_str_replace_all_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_replace_re (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_str_replace_re_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_replace_re_all (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_str_replace_re_all_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_indexof_re (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_str_indexof_re_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.str_indexof_re_split (__eo_to_smt x)
              (__eo_to_smt y) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_str_indexof_re_split_third_arg_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt binders)
        hBindersNone

private theorem smtx_typeof_repeat_second_arg_none
    (n x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.repeat n x) = SmtType.None := by
  intro hx
  rw [typeof_repeat_eq, hx]
  cases n <;> rfl

private theorem smtx_typeof_zero_extend_second_arg_none
    (n x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.zero_extend n x) = SmtType.None := by
  intro hx
  rw [typeof_zero_extend_eq, hx]
  cases n <;> rfl

private theorem smtx_typeof_sign_extend_second_arg_none
    (n x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.sign_extend n x) = SmtType.None := by
  intro hx
  rw [typeof_sign_extend_eq, hx]
  cases n <;> rfl

private theorem smtx_typeof_rotate_left_second_arg_none
    (n x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.rotate_left n x) = SmtType.None := by
  intro hx
  rw [typeof_rotate_left_eq, hx]
  cases n <;> rfl

private theorem smtx_typeof_rotate_right_second_arg_none
    (n x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.rotate_right n x) = SmtType.None := by
  intro hx
  rw [typeof_rotate_right_eq, hx]
  cases n <;> rfl

private theorem smtx_typeof_extract_third_arg_none
    (hi lo x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.extract hi lo x) = SmtType.None := by
  intro hx
  rw [typeof_extract_eq, hx]
  cases hi <;> cases lo <;> rfl

private theorem smtx_typeof_re_exp_second_arg_none
    (n x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.re_exp n x) = SmtType.None := by
  intro hx
  rw [typeof_re_exp_eq, hx]
  cases n <;> rfl

private theorem smtx_typeof_re_loop_third_arg_none
    (lo hi x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.re_loop lo hi x) = SmtType.None := by
  intro hx
  rw [typeof_re_loop_eq, hx]
  cases lo <;> cases hi <;> rfl

private theorem smtx_typeof_int_to_bv_second_arg_none
    (n x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.int_to_bv n x) = SmtType.None := by
  intro hx
  rw [typeof_int_to_bv_eq, hx]
  cases n <;> rfl

private theorem smtx_typeof_eo_to_smt_updater_arg_none
    (sel t u : SmtTerm) :
    __smtx_typeof t = SmtType.None ->
    __smtx_typeof (__eo_to_smt_updater sel t u) = SmtType.None := by
  intro ht
  cases sel <;> simp [__eo_to_smt_updater, TranslationProofs.smtx_typeof_none]
  case DtSel s d n m =>
    by_cases hLt :
        native_zlt (native_nat_to_int m)
          (native_nat_to_int (__smtx_dt_num_sels d n))
    · simp [hLt]
      apply smtx_typeof_ite_cond_none
      exact smtx_typeof_apply_arg_none (SmtTerm.DtTester s d n) t ht
    · have hLtFalse :
          native_zlt (native_nat_to_int m)
              (native_nat_to_int (__smtx_dt_num_sels d n)) =
            false := by
        cases hCmp :
            native_zlt (native_nat_to_int m)
              (native_nat_to_int (__smtx_dt_num_sels d n)) <;>
          simp [hCmp] at hLt ⊢
      simp [hLtFalse, native_ite, TranslationProofs.smtx_typeof_none]

private theorem eo_to_smt_updater_ne_dt_sel_local
    (sel t u : SmtTerm) (s : native_String) (d : SmtDatatype)
    (i j : native_Nat) :
    __eo_to_smt_updater sel t u ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases sel <;> try cases h
  case DtSel s' d' i' j' =>
    cases hIdx :
        native_zlt (native_nat_to_int j')
          (native_nat_to_int (__smtx_dt_num_sels d' i')) <;>
      simp [__eo_to_smt_updater, native_ite, hIdx] at h

private theorem eo_to_smt_updater_ne_dt_tester_local
    (sel t u : SmtTerm) (s : native_String) (d : SmtDatatype)
    (i : native_Nat) :
    __eo_to_smt_updater sel t u ≠ SmtTerm.DtTester s d i := by
  intro h
  cases sel <;> try cases h
  case DtSel s' d' i' j' =>
    cases hIdx :
        native_zlt (native_nat_to_int j')
          (native_nat_to_int (__smtx_dt_num_sels d' i')) <;>
      simp [__eo_to_smt_updater, native_ite, hIdx] at h

private theorem smtx_typeof_eo_to_smt_updater_update_arg_none
    (sel t u : SmtTerm) :
    __smtx_typeof u = SmtType.None ->
    __smtx_typeof (__eo_to_smt_updater sel t u) = SmtType.None := by
  intro hu
  by_cases hNone :
      __smtx_typeof (__eo_to_smt_updater sel t u) = SmtType.None
  · exact hNone
  · exfalso
    by_cases hSel : ∃ s d i j, sel = SmtTerm.DtSel s d i j
    · rcases hSel with ⟨s, d, i, j, rfl⟩
      by_cases hIdx :
          native_zlt (native_nat_to_int j)
            (native_nat_to_int (__smtx_dt_num_sels d i)) = true
      · have hIteNN :
            term_has_non_none_type
              (SmtTerm.ite
                (SmtTerm.Apply (SmtTerm.DtTester s d i) t)
                (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                  (__smtx_dt_num_sels d i) t u (SmtTerm.DtCons s d i))
                t) := by
          unfold term_has_non_none_type
          simpa [__eo_to_smt_updater, native_ite, hIdx] using hNone
        rcases ite_args_of_non_none hIteNN with
          ⟨T, _hCond, hThen, _hElse, hTNN⟩
        have hRecNN :
            __smtx_typeof
                (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                  (__smtx_dt_num_sels d i) t u
                  (SmtTerm.DtCons s d i)) ≠ SmtType.None := by
          rw [hThen]
          exact hTNN
        have huNN :
            __smtx_typeof u ≠ SmtType.None :=
          TranslationProofs.eo_to_smt_updater_rec_update_arg_non_none_of_non_none
            s d i j (__smtx_dt_num_sels d i) t u
            (SmtTerm.DtCons s d i)
            (by intro s0 d0 i0 j0 h; cases h)
            (by intro s0 d0 i0 h; cases h)
            hIdx hRecNN
        exact huNN hu
      · apply hNone
        have hIdxFalse :
            native_zlt (native_nat_to_int j)
                (native_nat_to_int (__smtx_dt_num_sels d i)) =
              false := by
          cases hCmp :
              native_zlt (native_nat_to_int j)
                (native_nat_to_int (__smtx_dt_num_sels d i)) <;>
            simp [hCmp] at hIdx ⊢
        simp [__eo_to_smt_updater, native_ite, hIdxFalse,
          TranslationProofs.smtx_typeof_none]
    · apply hNone
      cases sel <;>
        simp [__eo_to_smt_updater, TranslationProofs.smtx_typeof_none]
          at hSel ⊢

private theorem smtx_typeof_eo_to_smt_tuple_update_update_arg_none
    (T : SmtType) (idx t u : SmtTerm) :
    __smtx_typeof u = SmtType.None ->
    __smtx_typeof (__eo_to_smt_tuple_update T idx t u) = SmtType.None := by
  intro hu
  by_cases hTuple :
      ∃ s d n, T = SmtType.Datatype s d ∧ idx = SmtTerm.Numeral n
  · rcases hTuple with ⟨s, d, n, rfl, rfl⟩
    change
      __smtx_typeof
          (native_ite
            (native_and (native_streq s (native_string_lit "@Tuple"))
              (native_zleq 0 n))
            (__eo_to_smt_updater
              (SmtTerm.DtSel (native_string_lit "@Tuple") d
                native_nat_zero (native_int_to_nat n)) t u)
            SmtTerm.None) =
        SmtType.None
    by_cases hGuard :
        native_and (native_streq s (native_string_lit "@Tuple"))
          (native_zleq 0 n) = true
    · simp [hGuard, native_ite]
      exact
        smtx_typeof_eo_to_smt_updater_update_arg_none
          (SmtTerm.DtSel (native_string_lit "@Tuple") d
            native_nat_zero (native_int_to_nat n)) t u hu
    · have hGuardFalse :
          native_and (native_streq s (native_string_lit "@Tuple"))
              (native_zleq 0 n) =
            false := by
        cases hCmp :
            native_and (native_streq s (native_string_lit "@Tuple"))
              (native_zleq 0 n) <;>
          simp [hCmp] at hGuard ⊢
      simp [hGuardFalse, native_ite, TranslationProofs.smtx_typeof_none]
  · cases T <;> cases idx <;>
      simp [__eo_to_smt_tuple_update, TranslationProofs.smtx_typeof_none]
        at hTuple ⊢

private theorem eo_to_smt_tuple_update_ne_dt_sel_local
    (T : SmtType) (idx t u : SmtTerm) (s : native_String)
    (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt_tuple_update T idx t u ≠ SmtTerm.DtSel s d i j := by
  intro h
  simp [__eo_to_smt_tuple_update] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h
    · exact eo_to_smt_updater_ne_dt_sel_local _ _ _ _ _ _ _ h
    · cases h

private theorem eo_to_smt_tuple_update_ne_dt_tester_local
    (T : SmtType) (idx t u : SmtTerm) (s : native_String)
    (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt_tuple_update T idx t u ≠ SmtTerm.DtTester s d i := by
  intro h
  simp [__eo_to_smt_tuple_update] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h
    · exact eo_to_smt_updater_ne_dt_tester_local _ _ _ _ _ _ h
    · cases h

private theorem smtx_typeof_eo_to_smt_apply_apply_uop1_update_second_head_none
    (idx z binders a : Term)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.update idx) z) binders) a)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt_updater (__eo_to_smt idx) (__eo_to_smt z)
            (__eo_to_smt binders))
          (__eo_to_smt a)) =
      SmtType.None
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    exact eo_to_smt_updater_ne_dt_sel_local _ _ _ s d i j h
  · intro s d i h
    exact eo_to_smt_updater_ne_dt_tester_local _ _ _ s d i h
  · exact
      smtx_typeof_eo_to_smt_updater_update_arg_none
        (__eo_to_smt idx) (__eo_to_smt z) (__eo_to_smt binders)
        hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_uop1_tuple_update_second_head_none
    (idx z binders a : Term)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) z) binders)
            a)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt z))
            (__eo_to_smt idx) (__eo_to_smt z) (__eo_to_smt binders))
          (__eo_to_smt a)) =
      SmtType.None
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    exact
      eo_to_smt_tuple_update_ne_dt_sel_local
        (__smtx_typeof (__eo_to_smt z)) (__eo_to_smt idx)
        (__eo_to_smt z) (__eo_to_smt binders) s d i j h
  · intro s d i h
    exact
      eo_to_smt_tuple_update_ne_dt_tester_local
        (__smtx_typeof (__eo_to_smt z)) (__eo_to_smt idx)
        (__eo_to_smt z) (__eo_to_smt binders) s d i h
  · exact
      smtx_typeof_eo_to_smt_tuple_update_update_arg_none
        (__smtx_typeof (__eo_to_smt z)) (__eo_to_smt idx)
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_indexed_unary_head_none
    (q binders a : Term)
    (hIndexed :
      (∃ z : Term, q = Term.UOp1 UserOp1.repeat z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.zero_extend z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.sign_extend z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.rotate_left z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.rotate_right z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1._at_bit z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.re_exp z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.int_to_bv z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.seq_empty z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.set_empty z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.is z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.tuple_select z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.update z) ∨
        (∃ z : Term, q = Term.UOp1 UserOp1.tuple_update z))
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hIndexed with
    ⟨z, hRepeat⟩ | ⟨z, hZeroExtend⟩ | ⟨z, hSignExtend⟩ |
    ⟨z, hRotateLeft⟩ | ⟨z, hRotateRight⟩ | ⟨z, hAtBit⟩ |
    ⟨z, hReExp⟩ | ⟨z, hIntToBv⟩ | ⟨z, hSeqEmpty⟩ |
    ⟨z, hSetEmpty⟩ | ⟨z, hIs⟩ | ⟨z, hTupleSelect⟩ |
    ⟨z, hUpdate⟩ | ⟨z, hTupleUpdate⟩
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.repeat (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_repeat_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.zero_extend (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_zero_extend_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.sign_extend (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_sign_extend_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.rotate_left (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_rotate_left_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.rotate_right (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_rotate_right_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.eq
              (SmtTerm.extract (__eo_to_smt z) (__eo_to_smt z)
                (__eo_to_smt binders))
              (SmtTerm.Binary 1 1))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · apply smtx_typeof_eq_first_arg_none
      exact smtx_typeof_extract_third_arg_none
        (__eo_to_smt z) (__eo_to_smt z) (__eo_to_smt binders)
        hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.re_exp (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_re_exp_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.int_to_bv (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_int_to_bv_second_arg_none
        (__eo_to_smt z) (__eo_to_smt binders) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (__eo_to_smt_seq_empty (__eo_to_smt_type z))
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_apply_arg_none
      (__eo_to_smt_seq_empty (__eo_to_smt_type z))
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (__eo_to_smt_set_empty (__eo_to_smt_type z))
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_apply_arg_none
      (__eo_to_smt_set_empty (__eo_to_smt_type z))
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt z))
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_apply_arg_none
      (__eo_to_smt_tester (__eo_to_smt z))
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt_tuple_select
              (__smtx_typeof (__eo_to_smt binders))
              (__eo_to_smt z) (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      rw [hBindersNone] at h
      simp [__eo_to_smt_tuple_select] at h
    · intro s d i h
      rw [hBindersNone] at h
      simp [__eo_to_smt_tuple_select] at h
    · rw [hBindersNone]
      simp [__eo_to_smt_tuple_select]
  · subst q
    change
      __smtx_typeof
          (__eo_to_smt_updater (__eo_to_smt z)
            (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_eo_to_smt_updater_arg_none
      (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)
      hBindersNone
  · subst q
    change
      __smtx_typeof
          (__eo_to_smt_tuple_update
            (__smtx_typeof (__eo_to_smt binders))
            (__eo_to_smt z) (__eo_to_smt binders) (__eo_to_smt a)) =
        SmtType.None
    rw [hBindersNone]
    simp [__eo_to_smt_tuple_update]

private theorem smtx_typeof_eo_to_smt_apply_apply_uop2_head_none
    (q binders a : Term)
    (hUOp2 : ∃ op z w, q = Term.UOp2 op z w)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hUOp2 with ⟨op, z, w, hq⟩
  subst q
  cases op
  case extract =>
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.extract (__eo_to_smt z) (__eo_to_smt w)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_extract_third_arg_none
        (__eo_to_smt z) (__eo_to_smt w) (__eo_to_smt binders)
        hBindersNone
  case _at_bv =>
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (__eo_to_smt__at_bv (__eo_to_smt z) (__eo_to_smt w))
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_apply_arg_none
      (__eo_to_smt__at_bv (__eo_to_smt z) (__eo_to_smt w))
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  case re_loop =>
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.re_loop (__eo_to_smt z) (__eo_to_smt w)
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    apply smtx_typeof_apply_head_none_of_non_datatype_head
    · intro s d i j h
      cases h
    · intro s d i h
      cases h
    · exact smtx_typeof_re_loop_third_arg_none
        (__eo_to_smt z) (__eo_to_smt w) (__eo_to_smt binders)
        hBindersNone
  case _at_quantifiers_skolemize =>
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (__eo_to_smt
                (Term.UOp2 UserOp2._at_quantifiers_skolemize z w))
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_apply_arg_none
      (__eo_to_smt (Term.UOp2 UserOp2._at_quantifiers_skolemize z w))
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  case _at_const =>
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (__eo_to_smt (Term.UOp2 UserOp2._at_const z w))
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_apply_arg_none
      (__eo_to_smt (Term.UOp2 UserOp2._at_const z w))
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_uop3_head_none
    (q binders a : Term)
    (hUOp3 : ∃ op x y z, q = Term.UOp3 op x y z)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hUOp3 with ⟨op, x, y, z, hq⟩
  subst q
  cases op
  case _at_re_unfold_pos_component =>
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (__eo_to_smt
                (Term.UOp3 UserOp3._at_re_unfold_pos_component x y z))
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_apply_arg_none
      (__eo_to_smt (Term.UOp3 UserOp3._at_re_unfold_pos_component x y z))
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  case _at_witness_string_length =>
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (__eo_to_smt
                (Term.UOp3 UserOp3._at_witness_string_length x y z))
              (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_apply_arg_none
      (__eo_to_smt (Term.UOp3 UserOp3._at_witness_string_length x y z))
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone

private theorem smtx_typeof_eo_to_smt_tuple_prepend_head_none
    (head tail : SmtTerm) :
    __smtx_typeof head = SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_tuple_prepend head (__smtx_typeof head) tail) =
      SmtType.None := by
  intro hHead
  unfold __eo_to_smt_tuple_prepend
  rw [hHead]
  cases hTail : __smtx_typeof tail with
  | Datatype s d =>
      cases d with
      | null =>
          simp [__eo_to_smt_tuple_prepend_of_type,
            TranslationProofs.smtx_typeof_none]
      | sum c rest =>
          cases rest with
          | null =>
              have hWfNone :
                  __smtx_type_wf
                      (SmtType.Datatype (native_string_lit "@Tuple")
                        (SmtDatatype.sum
                          (SmtDatatypeCons.cons SmtType.None c)
                          SmtDatatype.null)) =
                    false := by
                simp [__smtx_type_wf, __smtx_type_wf_component,
                  __smtx_type_wf_rec, __smtx_dt_wf_rec,
                  __smtx_dt_cons_wf_rec, native_and]
                cases native_inhabited_type SmtType.None <;>
                  simp [native_ite]
              simp [__eo_to_smt_tuple_prepend_of_type, hWfNone,
                native_ite, native_and, TranslationProofs.smtx_typeof_none]
          | sum c' rest' =>
              simp [__eo_to_smt_tuple_prepend_of_type,
                TranslationProofs.smtx_typeof_none]
  | _ =>
      simp [__eo_to_smt_tuple_prepend_of_type,
        TranslationProofs.smtx_typeof_none]

private theorem smtx_typeof_eo_to_smt_tuple_prepend_tail_none
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm) :
    __smtx_typeof tail = SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_tuple_prepend head headTy tail) =
      SmtType.None := by
  intro hTail
  unfold __eo_to_smt_tuple_prepend
  rw [hTail]
  simp [__eo_to_smt_tuple_prepend_of_type,
    TranslationProofs.smtx_typeof_none]

private theorem smtx_typeof_eo_to_smt_apply_apply_tuple_second_head_none
    (q binders a : Term)
    (hTuple :
      ∃ w : Term, q = Term.Apply (Term.UOp UserOp.tuple) w)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hTuple with ⟨w, rfl⟩
  change
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt_tuple_prepend (__eo_to_smt w)
            (__smtx_typeof (__eo_to_smt w)) (__eo_to_smt binders))
          (__eo_to_smt a)) =
      SmtType.None
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    exact
      TranslationProofs.eo_to_smt_tuple_prepend_ne_dt_sel
        (__eo_to_smt w) (__smtx_typeof (__eo_to_smt w))
        (__eo_to_smt binders) s d i j h
  · intro s d i h
    exact
      TranslationProofs.eo_to_smt_tuple_prepend_ne_dt_tester
        (__eo_to_smt w) (__smtx_typeof (__eo_to_smt w))
        (__eo_to_smt binders) s d i h
  · exact
      smtx_typeof_eo_to_smt_tuple_prepend_tail_none
        (__eo_to_smt w) (__smtx_typeof (__eo_to_smt w))
        (__eo_to_smt binders) hBindersNone

private theorem smtx_typeof_eo_to_smt_apply_apply_unary_arith_head_none
    (q binders a : Term)
    (hUnaryArith :
      q = Term.UOp UserOp.to_real ∨
        q = Term.UOp UserOp.to_int ∨
        q = Term.UOp UserOp.is_int ∨
        q = Term.UOp UserOp.abs ∨
        q = Term.UOp UserOp.__eoo_neg_2 ∨
        q = Term.UOp UserOp.int_pow2 ∨
        q = Term.UOp UserOp.int_log2 ∨
        q = Term.UOp UserOp.int_ispow2 ∨
        q = Term.UOp UserOp._at_int_div_by_zero ∨
        q = Term.UOp UserOp._at_mod_by_zero ∨
        q = Term.UOp UserOp._at_div_by_zero)
    (hBindersNone :
      __smtx_typeof (__eo_to_smt binders) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply q binders) a)) =
      SmtType.None := by
  rcases hUnaryArith with
    hToReal | hToInt | hIsInt | hAbs | hUneg | hIntPow2 | hIntLog2 |
    hIntIspow2 | hIntDivZero | hModZero | hQdivZero
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.to_real (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_to_real_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.to_int (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_to_int_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.is_int (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_is_int_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.abs (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_abs_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.uneg (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_uneg_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.int_pow2 (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_int_pow2_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.int_log2 (__eo_to_smt binders))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_int_log2_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.and
              (SmtTerm.geq (__eo_to_smt binders) (SmtTerm.Numeral 0))
              (SmtTerm.eq (__eo_to_smt binders)
                (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt binders)))))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_int_ispow2_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.div (__eo_to_smt binders) (SmtTerm.Numeral 0))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_int_div_by_zero_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.mod (__eo_to_smt binders) (SmtTerm.Numeral 0))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_mod_by_zero_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
  · subst q
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.qdiv (__eo_to_smt binders)
              (SmtTerm.Rational (native_mk_rational 0 1)))
            (__eo_to_smt a)) =
        SmtType.None
    exact smtx_typeof_apply_qdiv_by_zero_head_none
      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone

private theorem smtx_typeof_apply_bvredand_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.bvcomp x
            (SmtTerm.bvnot
              (SmtTerm.Binary
                (__smtx_bv_sizeof_type (__smtx_typeof x)) 0)))
          y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · exact smtx_typeof_bvcomp_first_arg_none x
      (SmtTerm.bvnot
        (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof x)) 0)) hx

private theorem smtx_typeof_apply_bvredor_head_none
    (x y : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.bvnot
            (SmtTerm.bvcomp x
              (SmtTerm.Binary
                (__smtx_bv_sizeof_type (__smtx_typeof x)) 0)))
          y) =
      SmtType.None := by
  intro hx
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · apply smtx_typeof_bvnot_arg_none
    exact smtx_typeof_bvcomp_first_arg_none x
      (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof x)) 0) hx

private theorem smtx_typeof_apply_not_head_none (f x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.not f) x) =
      SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [typeof_not_eq]
  cases hTy : __smtx_typeof f <;>
    simp [__smtx_typeof_apply, native_ite, native_Teq]

private theorem smtx_typeof_apply_purify_head_none
    (f x : SmtTerm)
    (hf : __smtx_typeof f = SmtType.None) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm._at_purify f) x) =
      SmtType.None := by
  apply smtx_typeof_apply_head_none_of_non_datatype_head
  · intro s d i j h
    cases h
  · intro s d i h
    cases h
  · rw [__smtx_typeof.eq_def] <;> simp only
    exact hf

private theorem smtx_model_eval_exists_eq_of_body_constant_bool
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (b : Bool)
    (hDefTy : __smtx_typeof_value (__smtx_type_default T) = T)
    (hDefCan : __smtx_value_canonical_bool (__smtx_type_default T) = true)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.exists s T body) = SmtValue.Boolean b := by
  cases b
  · have hNoSat :
        ¬ ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true := by
      intro hSat
      rcases hSat with ⟨v, hvTy, hvCan, hvEval⟩
      have hEval := hConst v hvTy hvCan
      rw [hBody] at hEval
      rw [hEval] at hvEval
      cases hvEval
    simp [__smtx_model_eval, hNoSat]
  · have hSat :
        ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true := by
      refine ⟨__smtx_type_default T, hDefTy, hDefCan, ?_⟩
      rw [hConst (__smtx_type_default T) hDefTy hDefCan, hBody]
    simp [__smtx_model_eval, hSat]

private theorem smtx_model_eval_forall_eq_of_body_constant_bool
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (b : Bool)
    (hDefTy : __smtx_typeof_value (__smtx_type_default T) = T)
    (hDefCan : __smtx_value_canonical_bool (__smtx_type_default T) = true)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.forall s T body) = SmtValue.Boolean b := by
  cases b
  · have hNotAll :
        ¬ ∀ v : SmtValue,
          __smtx_typeof_value v = T ->
            __smtx_value_canonical_bool v = true ->
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true := by
      intro hAll
      have hEval := hAll (__smtx_type_default T) hDefTy hDefCan
      rw [hConst (__smtx_type_default T) hDefTy hDefCan, hBody] at hEval
      cases hEval
    simp [__smtx_model_eval, hNotAll]
  · have hAll :
        ∀ v : SmtValue,
          __smtx_typeof_value v = T ->
            __smtx_value_canonical_bool v = true ->
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true := by
      intro v hvTy hvCan
      rw [hConst v hvTy hvCan, hBody]
    simp [__smtx_model_eval]
    exact hAll

private theorem native_inhabited_type_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    native_inhabited_type T = true := by
  cases T <;>
    simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
      __smtx_value_canonical_bool, native_and] at hWF ⊢
  all_goals first | exact hWF.1 | assumption

private theorem smtx_type_default_typed_canonical_bool_of_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical_bool (__smtx_type_default T) = true := by
  have hDef :=
    Smtm.type_default_typed_canonical_of_native_inhabited_type T
      (native_inhabited_type_of_type_wf T hWF)
  exact ⟨hDef.1, by simpa [__smtx_value_canonical] using hDef.2⟩

private theorem smtx_model_eval_exists_eq_of_body_constant_bool_of_wf
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (b : Bool)
    (hWF : __smtx_type_wf T = true)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.exists s T body) = SmtValue.Boolean b := by
  rcases smtx_type_default_typed_canonical_bool_of_wf T hWF with
    ⟨hDefTy, hDefCan⟩
  exact smtx_model_eval_exists_eq_of_body_constant_bool
    M s T body b hDefTy hDefCan hBody hConst

private theorem smtx_model_eval_forall_eq_of_body_constant_bool_of_wf
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (b : Bool)
    (hWF : __smtx_type_wf T = true)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.forall s T body) = SmtValue.Boolean b := by
  rcases smtx_type_default_typed_canonical_bool_of_wf T hWF with
    ⟨hDefTy, hDefCan⟩
  exact smtx_model_eval_forall_eq_of_body_constant_bool
    M s T body b hDefTy hDefCan hBody hConst

private theorem native_model_push_shadow
    (M : SmtModel) (s1 s2 : native_String) (T1 T2 : SmtType)
    (v1 v2 : SmtValue)
    (hEq :
      ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
        { isVar := true, name := s2, ty := T2 }) :
    native_model_push (native_model_push M s1 T1 v1) s2 T2 v2 =
      native_model_push M s2 T2 v2 := by
  cases M with
  | mk values nativeFuns =>
      change
        SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
              else
                (if k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) then v1
                else values k))
            nativeFuns =
          SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
              else values k)
            nativeFuns
      congr
      funext k
      by_cases h2 : k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey)
      · simp [h2]
      · have h1 : k ≠ ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) := by
          intro hk
          exact h2 (by simpa [hEq] using hk)
        simp [h1, h2]

private theorem native_model_push_comm
    (M : SmtModel) (s1 s2 : native_String) (T1 T2 : SmtType)
    (v1 v2 : SmtValue)
    (hNe :
      ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) ≠
        { isVar := true, name := s2, ty := T2 }) :
    native_model_push (native_model_push M s1 T1 v1) s2 T2 v2 =
      native_model_push (native_model_push M s2 T2 v2) s1 T1 v1 := by
  cases M with
  | mk values nativeFuns =>
      change
        SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
              else
                (if k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) then v1
                else values k))
            nativeFuns =
          SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) then v1
              else
                (if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
                else values k))
            nativeFuns
      congr
      funext k
      by_cases h1 : k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey)
      · subst k
        by_cases h2 :
            ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
              { isVar := true, name := s2, ty := T2 }
        · exact False.elim (hNe h2)
        · simp [h2]
      · by_cases h2 : k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey)
        · subst k
          have h21 :
              ¬ ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) =
                { isVar := true, name := s1, ty := T1 } := by
            intro h
            exact hNe h.symm
          simp [h21]
        · simp [h1, h2]

private theorem smtx_model_eval_eo_to_smt_exists_eq_of_model_push_const
    (xs : Term) (body : SmtTerm)
    (s : native_String) (T : SmtType) (v : SmtValue)
    (hConst : ∀ M : SmtModel,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    ∀ M : SmtModel,
      __smtx_model_eval (native_model_push M s T v)
          (__eo_to_smt_exists xs body) =
        __smtx_model_eval M (__eo_to_smt_exists xs body) := by
  revert s T v
  induction xs, body using __eo_to_smt_exists.induct with
  | case1 F =>
      intro s T v hConst M
      simpa [__eo_to_smt_exists] using hConst M
  | case2 s' Ueo a F ih =>
      intro s T v hConst M
      let U := __eo_to_smt_type Ueo
      change
        __smtx_model_eval (native_model_push M s T v)
            (SmtTerm.exists s' U (__eo_to_smt_exists a F)) =
          __smtx_model_eval M
            (SmtTerm.exists s' U (__eo_to_smt_exists a F))
      refine smtx_model_eval_exists_eq_of_body_eval_eq ?_
      intro w
      by_cases hKey :
          ({ isVar := true, name := s, ty := T } : SmtModelKey) =
            { isVar := true, name := s', ty := U }
      · rw [native_model_push_shadow M s s' T U v w hKey]
      · rw [native_model_push_comm M s s' T U v w hKey]
        exact ih s T v hConst (native_model_push M s' U w)
  | case3 xs F hNotNil hNotConsVar =>
      intro s T v hConst M
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name Ueo =>
                      cases name with
                      | String s' =>
                          exact False.elim (hNotConsVar s' Ueo a rfl)
                      | _ =>
                          simp [__eo_to_smt_exists, __smtx_model_eval]
                  | _ =>
                      simp [__eo_to_smt_exists, __smtx_model_eval]
              | _ =>
                  simp [__eo_to_smt_exists, __smtx_model_eval]
          | _ =>
              simp [__eo_to_smt_exists, __smtx_model_eval]
      | __eo_List_nil =>
          exact False.elim (hNotNil rfl)
      | _ =>
          simp [__eo_to_smt_exists, __smtx_model_eval]

private theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  intro hTy
  have hExists :
      __smtx_typeof
          (SmtTerm.exists s (__eo_to_smt_type T)
            (__eo_to_smt_exists xs body)) = SmtType.Bool := by
    simpa [__eo_to_smt_exists] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.exists s (__eo_to_smt_type T)
          (__eo_to_smt_exists xs body)) := by
    unfold term_has_non_none_type
    rw [hExists]
    simp
  exact exists_body_bool_of_non_none hNN

private theorem smtx_type_wf_of_exists_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro hTy
  have hTail :
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
    smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool ≠ SmtType.None := by
    intro hNone
    have hExists :
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs body)) = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    rw [smtx_typeof_exists_term_eq, hTail] at hExists
    simp [native_ite, native_Teq, hNone] at hExists
  exact smtx_typeof_guard_wf_wf_of_non_none
    (__eo_to_smt_type T) SmtType.Bool hGuardNN

private theorem eo_smt_var_env_of_eo_to_smt_exists_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    ∃ vars : List SmtVarKey, EoSmtVarEnv xs vars := by
  intro hTy
  induction xs, body using __eo_to_smt_exists.induct with
  | case1 F =>
      exact ⟨[], EoSmtVarEnv.nil⟩
  | case2 s T xs F ih =>
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists xs F) = SmtType.Bool :=
        smtx_typeof_exists_tail_bool_of_cons_bool s T xs F hTy
      rcases ih hTailTy with ⟨vars, hEnv⟩
      exact ⟨(s, __eo_to_smt_type T) :: vars, EoSmtVarEnv.cons hEnv⟩
  | case3 xs F hNotNil hNotConsVar =>
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name T =>
                      cases name with
                      | String s =>
                          exact False.elim (hNotConsVar s T a rfl)
                      | _ =>
                          simp [__eo_to_smt_exists] at hTy
                  | _ =>
                      simp [__eo_to_smt_exists] at hTy
              | _ =>
                  simp [__eo_to_smt_exists] at hTy
          | _ =>
              simp [__eo_to_smt_exists] at hTy
      | __eo_List_nil =>
          exact False.elim (hNotNil rfl)
      | _ =>
          simp [__eo_to_smt_exists] at hTy

private theorem qterm_binder_env_of_quant_typeof_bool
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool) :
    ∃ vars : List SmtVarKey, EoSmtVarEnv x vars := by
  rcases hQ with hForall | hExists
  · subst Q
    have hTyForall :
        __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
      simpa [qforall, qterm] using hTy
    have hx : x ≠ Term.__eo_List_nil :=
      qforall_non_nil_of_non_none x F (by rw [hTyForall]; simp)
    have hExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool := by
      rw [eo_to_smt_forall_eq x F hx] at hTyForall
      exact smtx_typeof_not_arg_of_bool _ hTyForall
    exact eo_smt_var_env_of_eo_to_smt_exists_bool
      x (SmtTerm.not (__eo_to_smt F)) hExistsTy
  · subst Q
    have hTyExists :
        __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool := by
      simpa [qexists, qterm] using hTy
    have hx : x ≠ Term.__eo_List_nil :=
      qexists_non_nil_of_non_none x F (by rw [hTyExists]; simp)
    have hExistsTy :
        __smtx_typeof (__eo_to_smt_exists x (__eo_to_smt F)) =
          SmtType.Bool := by
      rw [eo_to_smt_exists_eq x F hx] at hTyExists
      exact hTyExists
    exact eo_smt_var_env_of_eo_to_smt_exists_bool
      x (__eo_to_smt F) hExistsTy

private theorem smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_bool
    (xs : Term) (body : SmtTerm) (M : SmtModel) (b : Bool)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : ∀ (M : SmtModel) (s : native_String) (T : Term)
      (v : SmtValue),
      __smtx_typeof_value v = __eo_to_smt_type T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (__eo_to_smt_exists xs body) =
      SmtValue.Boolean b := by
  revert hTy hConst M b
  induction xs, body using __eo_to_smt_exists.induct with
  | case1 F =>
      intro M b hTy hBody hConst
      simpa [__eo_to_smt_exists] using hBody
  | case2 s T xs F ih =>
      intro M b hTy hBody hConst
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists xs F) = SmtType.Bool :=
        smtx_typeof_exists_tail_bool_of_cons_bool s T xs F hTy
      have hWF :
          __smtx_type_wf (__eo_to_smt_type T) = true :=
        smtx_type_wf_of_exists_cons_bool s T xs F hTy
      have hTailEval :
          __smtx_model_eval M (__eo_to_smt_exists xs F) =
            SmtValue.Boolean b :=
        ih M b hTailTy hBody hConst
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs F)) =
          SmtValue.Boolean b
      refine smtx_model_eval_exists_eq_of_body_constant_bool_of_wf
        M s (__eo_to_smt_type T) (__eo_to_smt_exists xs F) b hWF
        hTailEval ?_
      intro v hvTy hvCan
      exact smtx_model_eval_eo_to_smt_exists_eq_of_model_push_const
        xs F s (__eo_to_smt_type T) v
        (fun M' => hConst M' s T v hvTy hvCan) M
  | case3 xs F hNotNil hNotConsVar =>
      intro M b hTy hBody hConst
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name T =>
                      cases name with
                      | String s =>
                          exact False.elim (hNotConsVar s T a rfl)
                      | _ =>
                          simp [__eo_to_smt_exists] at hTy
                  | _ =>
                      simp [__eo_to_smt_exists] at hTy
              | _ =>
                  simp [__eo_to_smt_exists] at hTy
          | _ =>
              simp [__eo_to_smt_exists] at hTy
      | __eo_List_nil =>
          exact False.elim (hNotNil rfl)
      | _ =>
          simp [__eo_to_smt_exists] at hTy

private theorem smtx_model_eval_qexists_eq_of_body_constant_bool
    (x F : Term) (M : SmtModel) (b : Bool)
    (hx : x ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool)
    (hBody : __smtx_model_eval M (__eo_to_smt F) = SmtValue.Boolean b)
    (hConst : ∀ (M : SmtModel) (s : native_String) (T : Term)
      (v : SmtValue),
      __smtx_typeof_value v = __eo_to_smt_type T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
          (__eo_to_smt F) =
        __smtx_model_eval M (__eo_to_smt F)) :
    __smtx_model_eval M (__eo_to_smt (qexists x F)) =
      SmtValue.Boolean b := by
  rw [eo_to_smt_exists_eq x F hx] at hTy ⊢
  exact smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_bool
    x (__eo_to_smt F) M b hTy hBody hConst

private theorem smtx_model_eval_qforall_eq_of_body_constant_bool
    (x F : Term) (M : SmtModel) (b : Bool)
    (hx : x ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool)
    (hBody : __smtx_model_eval M (__eo_to_smt F) = SmtValue.Boolean b)
    (hConst : ∀ (M : SmtModel) (s : native_String) (T : Term)
      (v : SmtValue),
      __smtx_typeof_value v = __eo_to_smt_type T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
          (__eo_to_smt F) =
        __smtx_model_eval M (__eo_to_smt F)) :
    __smtx_model_eval M (__eo_to_smt (qforall x F)) =
      SmtValue.Boolean b := by
  have hExistsTy :
      __smtx_typeof (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool := by
    have hTy' := hTy
    rw [eo_to_smt_forall_eq x F hx] at hTy'
    exact smtx_typeof_not_arg_of_bool _ hTy'
  have hNotBody :
      __smtx_model_eval M (SmtTerm.not (__eo_to_smt F)) =
        SmtValue.Boolean (SmtEval.native_not b) := by
    cases b <;>
      simp [__smtx_model_eval, hBody, __smtx_model_eval_not,
        SmtEval.native_not]
  have hNotConst :
      ∀ (M : SmtModel) (s : native_String) (T : Term) (v : SmtValue),
        __smtx_typeof_value v = __eo_to_smt_type T ->
        __smtx_value_canonical_bool v = true ->
        __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
            (SmtTerm.not (__eo_to_smt F)) =
          __smtx_model_eval M (SmtTerm.not (__eo_to_smt F)) := by
    intro M' s T v hvTy hvCan
    rw [__smtx_model_eval.eq_6, __smtx_model_eval.eq_6]
    rw [hConst M' s T v hvTy hvCan]
  have hExistsEval :
      __smtx_model_eval M
          (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtValue.Boolean (SmtEval.native_not b) :=
    smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_bool
      x (SmtTerm.not (__eo_to_smt F)) M (SmtEval.native_not b)
      hExistsTy hNotBody hNotConst
  rw [eo_to_smt_forall_eq x F hx]
  cases b <;>
    simp [__smtx_model_eval, hExistsEval, __smtx_model_eval_not,
      SmtEval.native_not]

private def body_constant_on_eo_binders (body : SmtTerm) : Term -> Prop
  | Term.Apply (Term.Apply Term.__eo_List_cons
      (Term.Var (Term.String s) T)) xs =>
      (∀ (M : SmtModel) (v : SmtValue),
        __smtx_typeof_value v = __eo_to_smt_type T ->
        __smtx_value_canonical_bool v = true ->
        __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
            body =
          __smtx_model_eval M body) ∧
      body_constant_on_eo_binders body xs
  | _ => True

private theorem smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_on_binders
    (xs : Term) (body : SmtTerm) (M : SmtModel) (b : Bool)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : body_constant_on_eo_binders body xs) :
    __smtx_model_eval M (__eo_to_smt_exists xs body) =
      SmtValue.Boolean b := by
  revert hTy hBody hConst M b
  induction xs, body using __eo_to_smt_exists.induct with
  | case1 F =>
      intro M b hTy hBody hConst
      simpa [__eo_to_smt_exists] using hBody
  | case2 s T xs F ih =>
      intro M b hTy hBody hConst
      have hHeadConst :
          ∀ (M : SmtModel) (v : SmtValue),
            __smtx_typeof_value v = __eo_to_smt_type T ->
            __smtx_value_canonical_bool v = true ->
            __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                F =
              __smtx_model_eval M F := hConst.1
      have hTailConst : body_constant_on_eo_binders F xs := hConst.2
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists xs F) = SmtType.Bool :=
        smtx_typeof_exists_tail_bool_of_cons_bool s T xs F hTy
      have hWF :
          __smtx_type_wf (__eo_to_smt_type T) = true :=
        smtx_type_wf_of_exists_cons_bool s T xs F hTy
      have hTailEval :
          __smtx_model_eval M (__eo_to_smt_exists xs F) =
            SmtValue.Boolean b :=
        ih M b hTailTy hBody hTailConst
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs F)) =
          SmtValue.Boolean b
      refine smtx_model_eval_exists_eq_of_body_constant_bool_of_wf
        M s (__eo_to_smt_type T) (__eo_to_smt_exists xs F) b hWF
        hTailEval ?_
      intro v hvTy hvCan
      exact smtx_model_eval_eo_to_smt_exists_eq_of_model_push_const
        xs F s (__eo_to_smt_type T) v
        (fun M' => hHeadConst M' v hvTy hvCan) M
  | case3 xs F hNotNil hNotConsVar =>
      intro M b hTy hBody hConst
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name T =>
                      cases name with
                      | String s =>
                          exact False.elim (hNotConsVar s T a rfl)
                      | _ =>
                          simp [__eo_to_smt_exists] at hTy
                  | _ =>
                      simp [__eo_to_smt_exists] at hTy
              | _ =>
                  simp [__eo_to_smt_exists] at hTy
          | _ =>
              simp [__eo_to_smt_exists] at hTy
      | __eo_List_nil =>
          exact False.elim (hNotNil rfl)
      | _ =>
          simp [__eo_to_smt_exists] at hTy

private theorem smtx_model_eval_qexists_eq_of_body_constant_on_binders
    (x F : Term) (M : SmtModel) (b : Bool)
    (hx : x ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool)
    (hBody : __smtx_model_eval M (__eo_to_smt F) = SmtValue.Boolean b)
    (hConst : body_constant_on_eo_binders (__eo_to_smt F) x) :
    __smtx_model_eval M (__eo_to_smt (qexists x F)) =
      SmtValue.Boolean b := by
  rw [eo_to_smt_exists_eq x F hx] at hTy ⊢
  exact smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_on_binders
    x (__eo_to_smt F) M b hTy hBody hConst

private theorem body_constant_on_eo_binders_not
    (body : SmtTerm) :
    ∀ xs,
      body_constant_on_eo_binders body xs ->
      body_constant_on_eo_binders (SmtTerm.not body) xs
  | xs, hConst => by
      cases xs with
      | Apply f tail =>
          cases f with
          | Apply g head =>
              cases g with
              | __eo_List_cons =>
                  cases head with
                  | Var name T =>
                      cases name with
                      | String s =>
                          constructor
                          · intro M v hvTy hvCan
                            rw [__smtx_model_eval.eq_6, __smtx_model_eval.eq_6]
                            exact congrArg __smtx_model_eval_not
                              (hConst.1 M v hvTy hvCan)
                          · exact body_constant_on_eo_binders_not body tail
                              hConst.2
                      | _ =>
                          trivial
                  | _ =>
                      trivial
              | _ =>
                  trivial
          | _ =>
              trivial
      | _ =>
          trivial

private theorem smtx_model_eval_qforall_eq_of_body_constant_on_binders
    (x F : Term) (M : SmtModel) (b : Bool)
    (hx : x ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool)
    (hBody : __smtx_model_eval M (__eo_to_smt F) = SmtValue.Boolean b)
    (hConst : body_constant_on_eo_binders (__eo_to_smt F) x) :
    __smtx_model_eval M (__eo_to_smt (qforall x F)) =
      SmtValue.Boolean b := by
  have hExistsTy :
      __smtx_typeof (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool := by
    have hTy' := hTy
    rw [eo_to_smt_forall_eq x F hx] at hTy'
    exact smtx_typeof_not_arg_of_bool _ hTy'
  have hNotBody :
      __smtx_model_eval M (SmtTerm.not (__eo_to_smt F)) =
        SmtValue.Boolean (SmtEval.native_not b) := by
    cases b <;>
      simp [__smtx_model_eval, hBody, __smtx_model_eval_not,
        SmtEval.native_not]
  have hNotConst :
      body_constant_on_eo_binders (SmtTerm.not (__eo_to_smt F)) x := by
    exact body_constant_on_eo_binders_not (__eo_to_smt F) x hConst
  have hExistsEval :
      __smtx_model_eval M
          (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtValue.Boolean (SmtEval.native_not b) :=
    smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_on_binders
      x (SmtTerm.not (__eo_to_smt F)) M (SmtEval.native_not b)
      hExistsTy hNotBody hNotConst
  rw [eo_to_smt_forall_eq x F hx]
  cases b <;>
    simp [__smtx_model_eval, hExistsEval, __smtx_model_eval_not,
      SmtEval.native_not]

private theorem smtx_model_eval_exists_eq_of_body_term_eval_eq
    (M : SmtModel) (s : native_String) (T : SmtType)
    (body body' : SmtTerm)
    (hBody : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push M s T v) body') :
    __smtx_model_eval M (SmtTerm.exists s T body) =
      __smtx_model_eval M (SmtTerm.exists s T body') := by
  have hSatIff :
      (∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical_bool v = true ∧
          __smtx_model_eval (native_model_push M s T v) body =
            SmtValue.Boolean true) ↔
      (∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical_bool v = true ∧
          __smtx_model_eval (native_model_push M s T v) body' =
            SmtValue.Boolean true) := by
    constructor
    · intro h
      rcases h with ⟨v, hvTy, hvCan, hvEval⟩
      refine ⟨v, hvTy, hvCan, ?_⟩
      simpa [hBody v hvTy hvCan] using hvEval
    · intro h
      rcases h with ⟨v, hvTy, hvCan, hvEval⟩
      refine ⟨v, hvTy, hvCan, ?_⟩
      simpa [hBody v hvTy hvCan] using hvEval
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical_bool v = true ∧
          __smtx_model_eval (native_model_push M s T v) body =
            SmtValue.Boolean true
  · have hSat' :
        ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body' =
              SmtValue.Boolean true :=
      hSatIff.mp hSat
    simp [__smtx_model_eval, hSat, hSat']
  · have hSat' :
        ¬ ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body' =
              SmtValue.Boolean true := by
      intro h
      exact hSat (hSatIff.mpr h)
    simp [__smtx_model_eval, hSat, hSat']

private theorem eo_smt_var_env_term_ne_stuck {xs : Term} {vars : List SmtVarKey}
    (h : EoSmtVarEnv xs vars) :
    xs ≠ Term.Stuck := by
  cases h <;> intro hxs <;> cases hxs

private theorem eo_mk_apply_of_ne_stuck_local {a w : Term}
    (ha : a ≠ Term.Stuck) (hw : w ≠ Term.Stuck) :
    __eo_mk_apply a w = Term.Apply a w := by
  cases a <;> cases w <;> simp_all [__eo_mk_apply]

private theorem eo_list_concat_rec_nil_left_of_ne {z : Term}
    (hz : z ≠ Term.Stuck) :
    __eo_list_concat_rec Term.__eo_List_nil z = z := by
  cases z <;> first | exact absurd rfl hz | rfl

private theorem eo_list_concat_rec_cons_left_of_suffix_ne
    (f x y z : Term) (hz : z ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) y) z =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec y z) := by
  cases z <;> first | exact absurd rfl hz | rfl

private theorem smtx_model_eval_eo_to_smt_exists_concat_rec_eq_of_suffix_const
    (M : SmtModel) (hM : model_total_typed M)
    (ys zs : Term) (body : SmtTerm) {ysVars zsVars : List SmtVarKey}
    (hYs : EoSmtVarEnv ys ysVars) (hZs : EoSmtVarEnv zs zsVars)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hConcatTy :
      __smtx_typeof
          (__eo_to_smt_exists (__eo_list_concat_rec ys zs) body) =
        SmtType.Bool)
    (hYsTy :
      __smtx_typeof (__eo_to_smt_exists ys body) = SmtType.Bool)
    (hConstZ : body_constant_on_eo_binders body zs) :
    __smtx_model_eval M
        (__eo_to_smt_exists (__eo_list_concat_rec ys zs) body) =
      __smtx_model_eval M (__eo_to_smt_exists ys body) := by
  induction hYs generalizing M with
  | nil =>
      rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with
        ⟨b, hBodyEval⟩
      have hZsNe : zs ≠ Term.Stuck :=
        eo_smt_var_env_term_ne_stuck hZs
      have hConcatNil :
          __eo_list_concat_rec Term.__eo_List_nil zs = zs := by
        exact eo_list_concat_rec_nil_left_of_ne hZsNe
      have hZTy :
          __smtx_typeof (__eo_to_smt_exists zs body) = SmtType.Bool := by
        simpa [hConcatNil] using hConcatTy
      have hCollapse :
          __smtx_model_eval M (__eo_to_smt_exists zs body) =
            SmtValue.Boolean b :=
        smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_on_binders
          zs body M b hZTy hBodyEval hConstZ
      simpa [hConcatNil, __eo_to_smt_exists]
        using hCollapse.trans hBodyEval.symm
  | cons hTail ih =>
      rename_i s T tail varsTail
      have hTailConcatEnv :
          EoSmtVarEnv (__eo_list_concat_rec tail zs) (varsTail ++ zsVars) :=
        EoSmtVarEnv.concat_rec hTail hZs
      have hTailConcatNe :
          __eo_list_concat_rec tail zs ≠ Term.Stuck :=
        eo_smt_var_env_term_ne_stuck hTailConcatEnv
      have hZsNe : zs ≠ Term.Stuck :=
        eo_smt_var_env_term_ne_stuck hZs
      have hConcatCons :
          __eo_list_concat_rec
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) tail) zs =
            Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T))
              (__eo_list_concat_rec tail zs) := by
        rw [eo_list_concat_rec_cons_left_of_suffix_ne
          Term.__eo_List_cons (Term.Var (Term.String s) T) tail zs hZsNe]
        exact eo_mk_apply_of_ne_stuck_local (by simp) hTailConcatNe
      rw [hConcatCons] at hConcatTy ⊢
      have hConcatTailTy :
          __smtx_typeof
              (__eo_to_smt_exists (__eo_list_concat_rec tail zs) body) =
            SmtType.Bool :=
        smtx_typeof_exists_tail_bool_of_cons_bool s T
          (__eo_list_concat_rec tail zs) body hConcatTy
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists tail body) =
            SmtType.Bool :=
        smtx_typeof_exists_tail_bool_of_cons_bool s T tail body hYsTy
      have hWF :
          __smtx_type_wf (__eo_to_smt_type T) = true :=
        smtx_type_wf_of_exists_cons_bool s T tail body hYsTy
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists (__eo_list_concat_rec tail zs) body)) =
          __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail body))
      refine smtx_model_eval_exists_eq_of_body_term_eval_eq
        M s (__eo_to_smt_type T)
        (__eo_to_smt_exists (__eo_list_concat_rec tail zs) body)
        (__eo_to_smt_exists tail body) ?_
      intro v hvTy hvCan
      exact ih (native_model_push M s (__eo_to_smt_type T) v)
        (model_total_typed_push hM s (__eo_to_smt_type T) v hWF hvTy
          (by simpa [__smtx_value_canonical] using hvCan))
        hConcatTailTy hTailTy

private def smtExistsOfBinders : List SmtVarKey -> SmtTerm -> SmtTerm
  | [], body => body
  | b :: bs, body => SmtTerm.exists b.1 b.2 (smtExistsOfBinders bs body)

private theorem native_model_push_same
    (M : SmtModel) (s : native_String) (T : SmtType) (v w : SmtValue) :
    native_model_push (native_model_push M s T v) s T w =
      native_model_push M s T w := by
  cases M with
  | mk values nativeFuns =>
      change
        SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then w
              else
                (if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then v
                else values k))
            nativeFuns =
          SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then w
              else values k)
            nativeFuns
      congr
      funext k
      by_cases hk : k = ({ isVar := true, name := s, ty := T } : SmtModelKey)
      · simp [hk]
      · simp [hk]

private theorem smtExistsOfBinders_cons_congr
    (M : SmtModel) (b : SmtVarKey) (t u : SmtTerm) :
    (∀ M2, __smtx_model_eval M2 t = __smtx_model_eval M2 u) ->
    __smtx_model_eval M (smtExistsOfBinders [b] t) =
      __smtx_model_eval M (smtExistsOfBinders [b] u) := by
  rcases b with ⟨s, T⟩
  intro hEval
  classical
  let P : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) t =
          SmtValue.Boolean true
  let Q : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) u =
          SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    constructor
    · intro hSat
      rcases hSat with ⟨v, hv, hCan, hT⟩
      exact ⟨v, hv, hCan, by
        simpa [hEval (native_model_push M s T v)] using hT⟩
    · intro hSat
      rcases hSat with ⟨v, hv, hCan, hU⟩
      exact ⟨v, hv, hCan, by
        simpa [hEval (native_model_push M s T v)] using hU⟩
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, hPropEq]

private theorem smtExistsOfBinders_swap
    (M : SmtModel) (b1 b2 : SmtVarKey) (tail : List SmtVarKey)
    (body : SmtTerm) :
    __smtx_model_eval M (smtExistsOfBinders (b1 :: b2 :: tail) body) =
      __smtx_model_eval M (smtExistsOfBinders (b2 :: b1 :: tail) body) := by
  rcases b1 with ⟨s1, T1⟩
  rcases b2 with ⟨s2, T2⟩
  classical
  let rest := smtExistsOfBinders tail body
  let P : Prop :=
    ∃ v1 : SmtValue,
      __smtx_typeof_value v1 = T1 ∧
        __smtx_value_canonical_bool v1 = true ∧
        ∃ v2 : SmtValue,
          __smtx_typeof_value v2 = T2 ∧
            __smtx_value_canonical_bool v2 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s1 T1 v1) s2 T2 v2)
                rest =
              SmtValue.Boolean true
  let Q : Prop :=
    ∃ v2 : SmtValue,
      __smtx_typeof_value v2 = T2 ∧
        __smtx_value_canonical_bool v2 = true ∧
        ∃ v1 : SmtValue,
          __smtx_typeof_value v1 = T1 ∧
            __smtx_value_canonical_bool v1 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s2 T2 v2) s1 T1 v1)
                rest =
              SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    by_cases hKey :
        ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
          { isVar := true, name := s2, ty := T2 }
    · cases hKey
      constructor
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        exact ⟨v1, hv1, hc1, v2, hv2, hc2, by
          simpa [native_model_push_same] using hEval⟩
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        exact ⟨v1, hv1, hc1, v2, hv2, hc2, by
          simpa [native_model_push_same] using hEval⟩
    · constructor
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        refine ⟨v2, hv2, hc2, v1, hv1, hc1, ?_⟩
        simpa [native_model_push_comm M s1 s2 T1 T2 v1 v2 hKey] using
          hEval
      · intro hSat
        rcases hSat with ⟨v2, hv2, hc2, v1, hv1, hc1, hEval⟩
        refine ⟨v1, hv1, hc1, v2, hv2, hc2, ?_⟩
        simpa [native_model_push_comm M s1 s2 T1 T2 v1 v2 hKey] using
          hEval
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, rest, hPropEq]

private theorem smtExistsOfBinders_duplicate_cons
    (M : SmtModel) (b : SmtVarKey) (tail : List SmtVarKey)
    (body : SmtTerm) :
    __smtx_model_eval M (smtExistsOfBinders (b :: b :: tail) body) =
      __smtx_model_eval M (smtExistsOfBinders (b :: tail) body) := by
  rcases b with ⟨s, T⟩
  classical
  let rest := smtExistsOfBinders tail body
  let P : Prop :=
    ∃ v1 : SmtValue,
      __smtx_typeof_value v1 = T ∧
        __smtx_value_canonical_bool v1 = true ∧
        ∃ v2 : SmtValue,
          __smtx_typeof_value v2 = T ∧
            __smtx_value_canonical_bool v2 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s T v1) s T v2)
                rest =
              SmtValue.Boolean true
  let Q : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) rest =
          SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    constructor
    · intro hSat
      rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
      exact ⟨v2, hv2, hc2, by
        simpa [native_model_push_same] using hEval⟩
    · intro hSat
      rcases hSat with ⟨v, hv, hc, hEval⟩
      exact ⟨v, hv, hc, v, hv, hc, by
        simpa [native_model_push_same] using hEval⟩
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, rest, hPropEq]

private theorem smtExistsOfBinders_eval_perm
    (body : SmtTerm) {xs ys : List SmtVarKey}
    (hperm : xs.Perm ys) :
    ∀ M, __smtx_model_eval M (smtExistsOfBinders xs body) =
      __smtx_model_eval M (smtExistsOfBinders ys body) := by
  induction hperm with
  | nil =>
      intro M
      rfl
  | cons b _h ih =>
      intro M
      exact smtExistsOfBinders_cons_congr M b
        (smtExistsOfBinders _ body) (smtExistsOfBinders _ body) ih
  | swap b1 b2 tail =>
      intro M
      exact (smtExistsOfBinders_swap M b1 b2 tail body).symm
  | trans _h1 _h2 ih1 ih2 =>
      intro M
      exact (ih1 M).trans (ih2 M)

private theorem smtExistsOfBinders_cons_of_mem
    (body : SmtTerm) {b : SmtVarKey} {xs : List SmtVarKey}
    (hMem : b ∈ xs) :
    ∀ M, __smtx_model_eval M (smtExistsOfBinders (b :: xs) body) =
      __smtx_model_eval M (smtExistsOfBinders xs body) := by
  intro M
  have hPerm : xs.Perm (b :: xs.erase b) :=
    List.perm_cons_erase hMem
  have hMove :
      __smtx_model_eval M (smtExistsOfBinders (b :: xs) body) =
        __smtx_model_eval M
          (smtExistsOfBinders (b :: b :: xs.erase b) body) :=
    smtExistsOfBinders_eval_perm body (List.Perm.cons b hPerm) M
  have hDrop :
      __smtx_model_eval M
          (smtExistsOfBinders (b :: b :: xs.erase b) body) =
        __smtx_model_eval M
          (smtExistsOfBinders (b :: xs.erase b) body) :=
    smtExistsOfBinders_duplicate_cons M b (xs.erase b) body
  have hBack :
      __smtx_model_eval M
          (smtExistsOfBinders (b :: xs.erase b) body) =
        __smtx_model_eval M (smtExistsOfBinders xs body) :=
    (smtExistsOfBinders_eval_perm body hPerm M).symm
  exact hMove.trans (hDrop.trans hBack)

private theorem smtExistsOfBinders_eval_of_mem_iff
    (body : SmtTerm) {xs ys : List SmtVarKey}
    (hMemIff : ∀ b, b ∈ xs ↔ b ∈ ys) :
    ∀ M, __smtx_model_eval M (smtExistsOfBinders xs body) =
      __smtx_model_eval M (smtExistsOfBinders ys body) := by
  intro M
  classical
  cases xs with
  | nil =>
      cases ys with
      | nil =>
          rfl
      | cons y ys =>
          have hFalse : y ∈ ([] : List SmtVarKey) :=
            (hMemIff y).2 (by simp)
          exact False.elim (by simpa using hFalse)
  | cons x xs =>
      by_cases hxTail : x ∈ xs
      · have hDrop :
            __smtx_model_eval M (smtExistsOfBinders (x :: xs) body) =
              __smtx_model_eval M (smtExistsOfBinders xs body) :=
          smtExistsOfBinders_cons_of_mem body hxTail M
        have hTailMemIff : ∀ b, b ∈ xs ↔ b ∈ ys := by
          intro b
          constructor
          · intro hb
            exact (hMemIff b).1 (by simp [hb])
          · intro hb
            have hbCons : b = x ∨ b ∈ xs := by
              simpa using (hMemIff b).2 hb
            rcases hbCons with hEq | hbTail
            · subst b
              exact hxTail
            · exact hbTail
        exact hDrop.trans
          (smtExistsOfBinders_eval_of_mem_iff body hTailMemIff M)
      · have hxYs : x ∈ ys :=
          (hMemIff x).1 (by simp)
        have hPermYs : ys.Perm (x :: ys.erase x) :=
          List.perm_cons_erase hxYs
        have hYsMove :
            __smtx_model_eval M (smtExistsOfBinders ys body) =
              __smtx_model_eval M
                (smtExistsOfBinders (x :: ys.erase x) body) :=
          smtExistsOfBinders_eval_perm body hPermYs M
        by_cases hxErase : x ∈ ys.erase x
        · have hYsDrop :
              __smtx_model_eval M (smtExistsOfBinders ys body) =
                __smtx_model_eval M
                  (smtExistsOfBinders (ys.erase x) body) :=
            hYsMove.trans
              (smtExistsOfBinders_cons_of_mem body hxErase M)
          have hMemIffErase :
              ∀ b, b ∈ x :: xs ↔ b ∈ ys.erase x := by
            intro b
            constructor
            · intro hb
              have hbCons : b = x ∨ b ∈ xs := by
                simpa using hb
              rcases hbCons with hEq | hbTail
              · subst b
                exact hxErase
              · have hbYs : b ∈ ys :=
                  (hMemIff b).1 (by simp [hbTail])
                have hbNe : b ≠ x := by
                  intro hEq
                  subst b
                  exact hxTail hbTail
                exact (List.mem_erase_of_ne hbNe).mpr hbYs
            · intro hbErase
              have hbYs : b ∈ ys := List.mem_of_mem_erase hbErase
              exact (hMemIff b).2 hbYs
          exact
            (smtExistsOfBinders_eval_of_mem_iff body hMemIffErase M).trans
              hYsDrop.symm
        · have hTailMemIff : ∀ b, b ∈ xs ↔ b ∈ ys.erase x := by
            intro b
            constructor
            · intro hb
              have hbYs : b ∈ ys :=
                (hMemIff b).1 (by simp [hb])
              have hbNe : b ≠ x := by
                intro hEq
                subst b
                exact hxTail hb
              exact (List.mem_erase_of_ne hbNe).mpr hbYs
            · intro hbErase
              have hbYs : b ∈ ys := List.mem_of_mem_erase hbErase
              have hbCons : b = x ∨ b ∈ xs := by
                simpa using (hMemIff b).2 hbYs
              rcases hbCons with hEq | hbTail
              · subst b
                exact False.elim (hxErase hbErase)
              · exact hbTail
          have hCons :
              __smtx_model_eval M (smtExistsOfBinders (x :: xs) body) =
                __smtx_model_eval M
                  (smtExistsOfBinders (x :: ys.erase x) body) :=
            smtExistsOfBinders_cons_congr M x
              (smtExistsOfBinders xs body)
              (smtExistsOfBinders (ys.erase x) body)
              (smtExistsOfBinders_eval_of_mem_iff body hTailMemIff)
          exact hCons.trans hYsMove.symm
termination_by xs.length + ys.length
decreasing_by
  all_goals
    simp_wf
    simp_all
    try have hLenPos : 0 < ys.length := List.length_pos_of_mem hxYs
    try omega

private theorem eo_to_smt_exists_eq_smtExistsOfBinders
    {xs : Term} {vars : List SmtVarKey} (body : SmtTerm)
    (hEnv : EoSmtVarEnv xs vars) :
    __eo_to_smt_exists xs body = smtExistsOfBinders vars body := by
  induction hEnv with
  | nil =>
      simp [__eo_to_smt_exists, smtExistsOfBinders]
  | cons hTail ih =>
      rename_i s T env varsTail
      simp [__eo_to_smt_exists, smtExistsOfBinders, ih]

private theorem smtx_model_eval_eo_to_smt_exists_mem_iff_of_env
    (M : SmtModel) (body : SmtTerm)
    {xs ys : Term} {xsVars ysVars : List SmtVarKey}
    (hXs : EoSmtVarEnv xs xsVars) (hYs : EoSmtVarEnv ys ysVars)
    (hMemIff : ∀ key, key ∈ xsVars ↔ key ∈ ysVars) :
    __smtx_model_eval M (__eo_to_smt_exists xs body) =
      __smtx_model_eval M (__eo_to_smt_exists ys body) := by
  rw [eo_to_smt_exists_eq_smtExistsOfBinders body hXs]
  rw [eo_to_smt_exists_eq_smtExistsOfBinders body hYs]
  exact smtExistsOfBinders_eval_of_mem_iff body hMemIff M

private theorem eo_smt_var_env_vars_wf_of_exists_bool
    {xs : Term} {vars : List SmtVarKey} {body : SmtTerm}
    (hEnv : EoSmtVarEnv xs vars)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool) :
    ∀ key ∈ vars, __smtx_type_wf key.2 = true := by
  induction hEnv with
  | nil =>
      intro key hMem
      have hFalse : False := by simpa using hMem
      exact False.elim hFalse
  | cons hTail ih =>
      rename_i s T tail varsTail
      intro key hMem
      have hMem' :
          key = (s, __eo_to_smt_type T) ∨ key ∈ varsTail := by
        simpa using hMem
      rcases hMem' with hHead | hTailMem
      · subst key
        exact smtx_type_wf_of_exists_cons_bool s T tail body hTy
      · have hTailTy :
            __smtx_typeof (__eo_to_smt_exists tail body) =
              SmtType.Bool :=
          smtx_typeof_exists_tail_bool_of_cons_bool s T tail body hTy
        exact ih hTailTy key hTailMem

private theorem smtx_typeof_eo_to_smt_exists_bool_of_env_vars_wf
    {xs : Term} {vars : List SmtVarKey} {body : SmtTerm}
    (hEnv : EoSmtVarEnv xs vars)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hWf : ∀ key ∈ vars, __smtx_type_wf key.2 = true) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  induction hEnv with
  | nil =>
      simpa [__eo_to_smt_exists] using hBodyTy
  | cons hTail ih =>
      rename_i s T tail varsTail
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists tail body) =
            SmtType.Bool :=
        ih (fun key hMem => hWf key (by simp [hMem]))
      have hHeadWf :
          __smtx_type_wf (__eo_to_smt_type T) = true :=
        hWf (s, __eo_to_smt_type T) (by simp)
      change
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail body)) =
          SmtType.Bool
      rw [smtx_typeof_exists_term_eq]
      simp [hTailTy, hHeadWf, __smtx_typeof_guard_wf,
        native_ite, native_Teq]

private theorem smtx_model_eval_eo_to_smt_exists_perm_of_env
    (M : SmtModel) (body : SmtTerm)
    {xs ys : Term} {xsVars ysVars : List SmtVarKey}
    (hXs : EoSmtVarEnv xs xsVars) (hYs : EoSmtVarEnv ys ysVars)
    (hPerm : xsVars.Perm ysVars) :
    __smtx_model_eval M (__eo_to_smt_exists xs body) =
      __smtx_model_eval M (__eo_to_smt_exists ys body) := by
  rw [eo_to_smt_exists_eq_smtExistsOfBinders body hXs]
  rw [eo_to_smt_exists_eq_smtExistsOfBinders body hYs]
  exact smtExistsOfBinders_eval_perm body hPerm M

private theorem smtx_model_eval_qexists_perm_of_env
    (M : SmtModel) (xs ys F : Term)
    {xsVars ysVars : List SmtVarKey}
    (hXs : EoSmtVarEnv xs xsVars) (hYs : EoSmtVarEnv ys ysVars)
    (hPerm : xsVars.Perm ysVars)
    (hxs : xs ≠ Term.__eo_List_nil) (hys : ys ≠ Term.__eo_List_nil) :
    __smtx_model_eval M (__eo_to_smt (qexists xs F)) =
      __smtx_model_eval M (__eo_to_smt (qexists ys F)) := by
  rw [eo_to_smt_exists_eq xs F hxs]
  rw [eo_to_smt_exists_eq ys F hys]
  exact smtx_model_eval_eo_to_smt_exists_perm_of_env
    M (__eo_to_smt F) hXs hYs hPerm

private theorem smtx_model_eval_qforall_perm_of_env
    (M : SmtModel) (xs ys F : Term)
    {xsVars ysVars : List SmtVarKey}
    (hXs : EoSmtVarEnv xs xsVars) (hYs : EoSmtVarEnv ys ysVars)
    (hPerm : xsVars.Perm ysVars)
    (hxs : xs ≠ Term.__eo_List_nil) (hys : ys ≠ Term.__eo_List_nil) :
    __smtx_model_eval M (__eo_to_smt (qforall xs F)) =
      __smtx_model_eval M (__eo_to_smt (qforall ys F)) := by
  have hInner :=
    smtx_model_eval_eo_to_smt_exists_perm_of_env
      M (SmtTerm.not (__eo_to_smt F)) hXs hYs hPerm
  rw [eo_to_smt_forall_eq xs F hxs]
  rw [eo_to_smt_forall_eq ys F hys]
  simp [__smtx_model_eval, hInner]

private theorem eq_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hEq : native_teq x y = true
  · simpa [native_teq] using hEq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    unfold __eo_requires at hReq
    simp [hEqFalse, native_ite] at hReq

private theorem body_ne_stuck_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    B ≠ Term.Stuck := by
  intro hReq hB
  subst B
  unfold __eo_requires at hReq
  by_cases hEq : native_teq x y = true
  · by_cases hStuck : native_teq x Term.Stuck = true
    · simp [hEq, hStuck, native_ite] at hReq
    · have hStuckFalse : native_teq x Term.Stuck = false := by
        cases h : native_teq x Term.Stuck <;> simp [h] at hStuck ⊢
      simp [hEq, hStuckFalse, native_ite] at hReq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    simp [hEqFalse, native_ite] at hReq

private theorem condition_true_of_requires_true_false_eq_false {c : Term} :
    __eo_requires c (Term.Boolean true) (Term.Boolean false) =
      Term.Boolean false ->
    c = Term.Boolean true := by
  intro hReq
  cases c <;> simp [__eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not] at hReq ⊢
  case Boolean b =>
    cases b <;> simp at hReq ⊢

private theorem eo_or_eq_true_cases_local (x y : Term) :
    __eo_or x y = Term.Boolean true ->
    x = Term.Boolean true ∨ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_or] at h ⊢
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp [native_or] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [__eo_requires, hNumNe, native_ite, native_teq] at h

private theorem eo_and_eq_true_cases_local (x y : Term) :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_and, __eo_requires, native_ite,
    native_teq, native_and, native_not, SmtEval.native_not] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [hW] at h

private theorem eo_ite_true_branch_eq_false_cases
    (c d : Term) :
    __eo_ite c (Term.Boolean true) d = Term.Boolean false ->
    c = Term.Boolean false ∧ d = Term.Boolean false := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b <;> simp at h ⊢
    exact h

private theorem eo_ite_false_branch_eq_false_cases
    (c d : Term) :
    __eo_ite c (Term.Boolean false) d = Term.Boolean false ->
    c = Term.Boolean true ∨
      (c = Term.Boolean false ∧ d = Term.Boolean false) := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b <;> simp at h ⊢
    exact h

private structure scannerModelRel
    (xs bvs : Term) (M N : SmtModel) : Prop where
  globals : model_agrees_on_globals M N
  vars_eq :
    ∀ (s : native_String) (T : Term),
      __eo_ite
          (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T)))
          (Term.Boolean false)
          (__eo_is_neg (__eo_list_find Term.__eo_List_cons bvs
            (Term.Var (Term.String s) T))) =
        Term.Boolean false ->
      native_model_var_lookup M s (__eo_to_smt_type T) =
        native_model_var_lookup N s (__eo_to_smt_type T)

private theorem scannerModelRel_refl
    (xs bvs : Term) (M : SmtModel) :
    scannerModelRel xs bvs M M := by
  exact ⟨model_agrees_on_globals_refl M, by intro s T _; rfl⟩

private theorem scannerModelRel_push_same
    (xs bvs : Term) (M N : SmtModel)
    (s : native_String) (T : SmtType) (v : SmtValue)
    (hRel : scannerModelRel xs bvs M N) :
    scannerModelRel xs bvs
      (native_model_push M s T v) (native_model_push N s T v) := by
  refine ⟨model_agrees_on_globals_push₂ hRel.globals, ?_⟩
  intro s' T' hAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
        SmtModelKey) =
        { isVar := true, name := s, ty := T }
  · simpa [native_model_var_lookup, native_model_push, hKey]
  · simpa [native_model_var_lookup, native_model_push, hKey]
      using hRel.vars_eq s' T' hAllowed

private theorem eo_is_neg_list_find_nil_var
    (s : native_String) (T : Term) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons Term.__eo_List_nil
          (Term.Var (Term.String s) T)) =
      Term.Boolean true := by
  simp [__eo_list_find, __eo_is_list, __eo_get_nil_rec,
    __eo_requires, __eo_is_ok, __eo_is_list_nil, __eo_list_find_rec,
    __eo_is_neg, native_ite, native_teq, native_not,
    SmtEval.native_not]
  native_decide

private theorem eo_get_nil_rec_ne_stuck_of_is_list_true {f xs : Term}
    (hList : __eo_is_list f xs = Term.Boolean true) :
    __eo_get_nil_rec f xs ≠ Term.Stuck := by
  intro h
  cases f <;> cases xs <;> simp [__eo_is_list, __eo_is_ok,
    __eo_get_nil_rec, __eo_requires, native_ite, native_teq,
    native_not] at hList h
  all_goals first | exact hList h | exact hList.2 (h hList.1)

private theorem eo_is_list_cons_of_tail_list (x xs : Term)
    (hList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true) :
    __eo_is_list Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) =
      Term.Boolean true := by
  have hNilNe := eo_get_nil_rec_ne_stuck_of_is_list_true hList
  simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
    native_ite, native_teq, native_not]
  exact hNilNe

private theorem eo_is_list_tail_of_apply_apply_list (f x y : Term)
    (hList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply f x) y) =
        Term.Boolean true) :
    __eo_is_list Term.__eo_List_cons y = Term.Boolean true := by
  cases f <;> simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec,
    __eo_requires, native_ite, native_teq, native_not] at hList ⊢
  case __eo_List_cons =>
    cases y <;> simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec,
      __eo_requires, native_ite, native_teq, native_not] at hList ⊢
    all_goals exact hList

private theorem eo_is_list_head_eq_of_apply_apply_list (f x y : Term)
    (hList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply f x) y) =
        Term.Boolean true) :
    f = Term.__eo_List_cons := by
  cases f <;> simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec,
    __eo_requires, native_ite, native_teq, native_not] at hList ⊢

private theorem term_ne_stuck_of_eo_is_list_true {f xs : Term}
    (hList : __eo_is_list f xs = Term.Boolean true) :
    xs ≠ Term.Stuck := by
  intro h
  subst xs
  cases f <;> simp [__eo_is_list] at hList

private theorem term_var_string_ne_stuck (s : native_String) (T : Term) :
    Term.Var (Term.String s) T ≠ Term.Stuck := by
  intro h
  cases h

private theorem eo_eq_true_of_eq_ne_stuck
    {x : Term} (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  simp [__eo_eq, hx, native_teq]

private theorem eo_eq_false_of_ne_nonstuck
    {x y : Term} (hNe : x ≠ y)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_eq x y = Term.Boolean false := by
  simp [__eo_eq, hx, hy, native_teq, eq_comm, hNe]

private theorem eo_eq_var_string_true
    (s : native_String) (T : Term) :
    __eo_eq (Term.Var (Term.String s) T)
      (Term.Var (Term.String s) T) =
    Term.Boolean true := by
  simp [__eo_eq, native_teq]

private theorem eo_eq_var_string_false_of_ne
    {s s' : native_String} {T T' : Term}
    (hNe :
      Term.Var (Term.String s) T ≠
        Term.Var (Term.String s') T') :
    __eo_eq (Term.Var (Term.String s) T)
      (Term.Var (Term.String s') T') =
    Term.Boolean false := by
  simp [__eo_eq, native_teq, eq_comm, hNe]

private theorem eo_eq_var_string_bool_of_ne_stuck
    {z : Term} (hz : z ≠ Term.Stuck) (s : native_String) (T : Term) :
    ∃ b : Bool, __eo_eq z (Term.Var (Term.String s) T) = Term.Boolean b := by
  cases z <;> simp [__eo_eq] at hz ⊢

private theorem native_zlt_plus_one_nonneg
    {n : native_Int}
    (hN : native_zlt n 0 = false) :
    native_zlt (native_zplus n 1) 0 = false := by
  simp [native_zlt, native_zplus] at hN ⊢
  omega

private def eo_var_list : Term -> Prop
  | Term.__eo_List_nil => True
  | Term.Apply (Term.Apply Term.__eo_List_cons
      (Term.Var (Term.String _) _)) xs =>
      eo_var_list xs
  | _ => False

private def eo_var_list_mem (z : Term) : Term -> Prop
  | Term.__eo_List_nil => False
  | Term.Apply (Term.Apply Term.__eo_List_cons x) xs =>
      x = z ∨ eo_var_list_mem z xs
  | _ => False

private theorem eo_smt_var_env_mem_wf_of_exists_bool
    {xs : Term} {vars : List SmtVarKey} {body : SmtTerm}
    (hEnv : EoSmtVarEnv xs vars)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool) :
    ∀ (s : native_String) (T : Term),
      eo_var_list_mem (Term.Var (Term.String s) T) xs ->
        __smtx_type_wf (__eo_to_smt_type T) = true := by
  induction hEnv with
  | nil =>
      intro s T hMem
      exact False.elim hMem
  | cons hTail ih =>
      rename_i s0 T0 tail varsTail
      intro s T hMem
      rcases hMem with hHead | hTailMem
      · cases hHead
        exact smtx_type_wf_of_exists_cons_bool s0 T0 tail body hTy
      · have hTailTy :
            __smtx_typeof (__eo_to_smt_exists tail body) =
              SmtType.Bool :=
          smtx_typeof_exists_tail_bool_of_cons_bool
            s0 T0 tail body hTy
        exact ih hTailTy s T hTailMem

private theorem eo_var_list_of_env :
    ∀ {xs : Term} {vars : List SmtVarKey},
      EoSmtVarEnv xs vars -> eo_var_list xs
  | _, _, EoSmtVarEnv.nil => by
      trivial
  | _, _, EoSmtVarEnv.cons hTail => by
      simpa [eo_var_list] using eo_var_list_of_env hTail

private theorem eo_smt_var_env_of_var_list {xs : Term}
    (hVarList : eo_var_list xs) :
    ∃ vars : List SmtVarKey, EoSmtVarEnv xs vars := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            rcases ih hTailVar with ⟨vars, hEnv⟩
            exact ⟨(s, __eo_to_smt_type T) :: vars,
              EoSmtVarEnv.cons hEnv⟩
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          exact ⟨[], EoSmtVarEnv.nil⟩
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_smt_var_env_mem_of_var_list_mem
    {xs : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv xs vars) :
    ∀ {s : native_String} {T : Term},
      eo_var_list_mem (Term.Var (Term.String s) T) xs ->
        (s, __eo_to_smt_type T) ∈ vars := by
  induction hEnv with
  | nil =>
      intro s T hMem
      exact False.elim hMem
  | cons hTail ih =>
      rename_i s0 T0 tail varsTail
      intro s T hMem
      rcases hMem with hHead | hTailMem
      · cases hHead
        simp
      · simpa using
          (Or.inr (ih hTailMem) :
            (s, __eo_to_smt_type T) = (s0, __eo_to_smt_type T0) ∨
              (s, __eo_to_smt_type T) ∈ varsTail)

private theorem eo_smt_var_env_var_list_mem_of_mem
    {xs : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv xs vars) :
    ∀ {key : SmtVarKey},
      key ∈ vars ->
        ∃ s T,
          key = (s, __eo_to_smt_type T) ∧
            eo_var_list_mem (Term.Var (Term.String s) T) xs := by
  induction hEnv with
  | nil =>
      intro key hMem
      have hFalse : False := by simpa using hMem
      exact False.elim hFalse
  | cons hTail ih =>
      rename_i s0 T0 tail varsTail
      intro key hMem
      have hMem' :
          key = (s0, __eo_to_smt_type T0) ∨ key ∈ varsTail := by
        simpa using hMem
      rcases hMem' with hHead | hTailMem
      · refine ⟨s0, T0, hHead, ?_⟩
        exact Or.inl rfl
      · rcases ih hTailMem with ⟨s, T, hKey, hTermMem⟩
        refine ⟨s, T, hKey, ?_⟩
        exact Or.inr hTermMem

private theorem eo_var_list_is_list {xs : Term}
    (hVarList : eo_var_list xs) :
    __eo_is_list Term.__eo_List_cons xs = Term.Boolean true := by
  cases xs with
  | __eo_List_nil =>
      exact EoSmtVarEnv.nil.is_list
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g <;> try exact False.elim hVarList
          case __eo_List_cons =>
            cases x <;> try exact False.elim hVarList
            case Var name T =>
              cases name <;> try exact False.elim hVarList
              case String s =>
                exact eo_is_list_cons_of_tail_list
                  (Term.Var (Term.String s) T) a
                  (eo_var_list_is_list hVarList)
      | _ => exact False.elim hVarList
  | _ => exact False.elim hVarList

private theorem eo_var_list_ne_stuck {xs : Term}
    (hVarList : eo_var_list xs) :
    xs ≠ Term.Stuck := by
  intro h
  subst xs
  exact hVarList

private theorem eo_get_elements_rec_eq_self_of_var_list
    {xs : Term} (hVarList : eo_var_list xs) :
    __eo_get_elements_rec xs = xs := by
  induction xs using __eo_get_elements_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hRec : __eo_get_elements_rec y = y := ih hTailVar
            have hTailNe : y ≠ Term.Stuck :=
              eo_var_list_ne_stuck hTailVar
            simpa [__eo_get_elements_rec, hRec] using
              eo_mk_apply_of_ne_stuck_local (by simp) hTailNe
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          rfl
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_list_minclude_eq_rec_of_var_lists
    {xs ys : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys) :
    __eo_list_minclude Term.__eo_List_cons xs ys =
      __eo_list_minclude_rec xs ys (Term.Boolean true) := by
  have hXsList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hXsVar
  have hYsList : __eo_is_list Term.__eo_List_cons ys = Term.Boolean true :=
    eo_var_list_is_list hYsVar
  have hGetXs : __eo_get_elements_rec xs = xs :=
    eo_get_elements_rec_eq_self_of_var_list hXsVar
  have hGetYs : __eo_get_elements_rec ys = ys :=
    eo_get_elements_rec_eq_self_of_var_list hYsVar
  simp [__eo_list_minclude, hXsList, hYsList, hGetXs, hGetYs,
    __eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]

private theorem eo_var_list_erase_all_rec
    {xs : Term} (hVarList : eo_var_list xs) {z : Term}
    (hz : z ≠ Term.Stuck) :
    eo_var_list (__eo_list_erase_all_rec xs z) := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hRec := ih hTailVar
            have hRecNe :
                __eo_list_erase_all_rec y z ≠ Term.Stuck :=
              eo_var_list_ne_stuck hRec
            rcases eo_eq_var_string_bool_of_ne_stuck hz s T with ⟨b, hb⟩
            cases b
            · simpa [eo_var_list, __eo_list_erase_all_rec, hb, __eo_not,
                __eo_prepend_if, hRecNe, term_var_string_ne_stuck s T,
                SmtEval.native_not]
                using hRec
            · simpa [eo_var_list, __eo_list_erase_all_rec, hb, __eo_not,
                __eo_prepend_if, hRecNe, term_var_string_ne_stuck s T,
                SmtEval.native_not]
                using hRec
  | case3 nil =>
      simpa [__eo_list_erase_all_rec, hz]

private theorem eo_var_list_erase_rec
    {xs : Term} (hVarList : eo_var_list xs) {z : Term}
    (hz : z ≠ Term.Stuck) :
    eo_var_list (__eo_list_erase_rec xs z) := by
  induction xs, z using __eo_list_erase_rec.induct with
  | case1 z =>
      exact False.elim hVarList
  | case2 xs hZStuck =>
      exact False.elim (hz rfl)
  | case3 f x y z hZNotStuck ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            by_cases hEq : Term.Var (Term.String s) T = z
            · have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) z =
                    Term.Boolean true := by
                rw [hEq]
                exact eo_eq_true_of_eq_ne_stuck hz
              simpa [eo_var_list, __eo_list_erase_rec, hEqTerm,
                __eo_ite, native_ite, native_teq] using hTailVar
            · have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) z =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hEq hHeadNe hz
              have hRec : eo_var_list (__eo_list_erase_rec y z) :=
                ih hTailVar hz
              have hRecNe :
                  __eo_list_erase_rec y z ≠ Term.Stuck :=
                eo_var_list_ne_stuck hRec
              simpa [eo_var_list, __eo_list_erase_rec, hEqTerm,
                __eo_ite, __eo_mk_apply, hRecNe, native_ite, native_teq]
                using hRec
  | case4 nil z hNil hZ hNotApply =>
      simpa [__eo_list_erase_rec] using hVarList

private theorem eo_var_list_setof_rec
    {xs : Term} (hVarList : eo_var_list xs) :
    eo_var_list (__eo_list_setof_rec xs) := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hSetTail := ih hTailVar
            have hErase :
                eo_var_list
                  (__eo_list_erase_all_rec (__eo_list_setof_rec y)
                    (Term.Var (Term.String s) T)) :=
              eo_var_list_erase_all_rec hSetTail
                (term_var_string_ne_stuck s T)
            have hEraseNe :
                __eo_list_erase_all_rec (__eo_list_setof_rec y)
                    (Term.Var (Term.String s) T) ≠
                  Term.Stuck :=
              eo_var_list_ne_stuck hErase
            simpa [eo_var_list, __eo_list_setof_rec, __eo_mk_apply,
              hEraseNe] using hErase
  | case3 nil =>
      simpa [__eo_list_setof_rec]

private theorem eo_list_setof_rec_is_list_of_var_list
    {xs : Term} (hVarList : eo_var_list xs) :
    __eo_is_list Term.__eo_List_cons (__eo_list_setof_rec xs) =
      Term.Boolean true :=
  eo_var_list_is_list (eo_var_list_setof_rec hVarList)

private theorem eo_var_list_setof
    {xs : Term} (hVarList : eo_var_list xs) :
    eo_var_list (__eo_list_setof Term.__eo_List_cons xs) := by
  have hList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hSetRec : eo_var_list (__eo_list_setof_rec xs) :=
    eo_var_list_setof_rec hVarList
  simpa [__eo_list_setof, hList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hSetRec

private theorem eo_list_erase_all_rec_is_list_of_var_list
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck) :
    __eo_is_list Term.__eo_List_cons (__eo_list_erase_all_rec xs z) =
      Term.Boolean true :=
  eo_var_list_is_list (eo_var_list_erase_all_rec hVarList hz)

private theorem eo_var_list_diff_rec
    {xs ys : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys) :
    eo_var_list (__eo_list_diff_rec xs ys) := by
  induction xs, ys using __eo_list_diff_rec.induct with
  | case1 ys =>
      exact False.elim hXsVar
  | case2 xs hYsStuck =>
      exact False.elim (eo_var_list_ne_stuck hYsVar rfl)
  | case3 f x y ys hYsNotStuck v0 ih =>
      cases f <;> try exact False.elim hXsVar
      case __eo_List_cons =>
        cases x <;> try exact False.elim hXsVar
        case Var name T =>
          cases name <;> try exact False.elim hXsVar
          case String s =>
            have hTailVar : eo_var_list y := hXsVar
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hEraseVar :
                eo_var_list
                  (__eo_list_erase_rec ys (Term.Var (Term.String s) T)) :=
              eo_var_list_erase_rec hYsVar hHeadNe
            have hEraseNe :
                __eo_list_erase_rec ys (Term.Var (Term.String s) T) ≠
                  Term.Stuck :=
              eo_var_list_ne_stuck hEraseVar
            have hRec :
                eo_var_list (__eo_list_diff_rec y v0) :=
              ih hTailVar (by simpa [v0] using hEraseVar)
            have hRecNe : __eo_list_diff_rec y v0 ≠ Term.Stuck :=
              eo_var_list_ne_stuck hRec
            by_cases hSame :
                __eo_list_erase_rec ys (Term.Var (Term.String s) T) = ys
            · have hv0 : v0 = ys := by
                simpa [v0] using hSame
              have hYsNe : ys ≠ Term.Stuck :=
                eo_var_list_ne_stuck hYsVar
              have hEqTerm :
                  __eo_eq v0 ys = Term.Boolean true := by
                rw [hv0]
                exact eo_eq_true_of_eq_ne_stuck hYsNe
              simpa [eo_var_list, __eo_list_diff_rec, v0, hEqTerm,
                __eo_prepend_if, hHeadNe, hRecNe] using hRec
            · have hv0Ne : v0 ≠ ys := by
                simpa [v0] using hSame
              have hYsNe : ys ≠ Term.Stuck :=
                eo_var_list_ne_stuck hYsVar
              have hv0Stuck : v0 ≠ Term.Stuck := by
                simpa [v0] using hEraseNe
              have hEqTerm :
                  __eo_eq v0 ys = Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hv0Ne hv0Stuck hYsNe
              simpa [__eo_list_diff_rec, v0, hEqTerm,
                __eo_prepend_if, hRecNe] using hRec
  | case4 nil ys hNil hYs hNotApply =>
      simpa [__eo_list_diff_rec] using hXsVar

private theorem eo_var_list_diff
    {xs ys : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys) :
    eo_var_list (__eo_list_diff Term.__eo_List_cons xs ys) := by
  have hXsList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hXsVar
  have hYsList : __eo_is_list Term.__eo_List_cons ys = Term.Boolean true :=
    eo_var_list_is_list hYsVar
  have hDiffRec : eo_var_list (__eo_list_diff_rec xs ys) :=
    eo_var_list_diff_rec hXsVar hYsVar
  simpa [__eo_list_diff, hXsList, hYsList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hDiffRec

private theorem eo_list_concat_rec_nil_eq_of_var_list
    {xs : Term} (hVarList : eo_var_list xs) :
    __eo_list_concat_rec xs Term.__eo_List_nil = xs := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hRec :
                __eo_list_concat_rec y Term.__eo_List_nil = y :=
              ih hTailVar
            have hTailNe : y ≠ Term.Stuck := eo_var_list_ne_stuck hTailVar
            simp [__eo_list_concat_rec, hRec, __eo_mk_apply, hTailNe]
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          rfl
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_list_concat_nil_eq_of_var_list
    {xs : Term} (hVarList : eo_var_list xs) :
    __eo_list_concat Term.__eo_List_cons xs Term.__eo_List_nil = xs := by
  have hXsList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hNilList :
      __eo_is_list Term.__eo_List_cons Term.__eo_List_nil =
        Term.Boolean true :=
    eo_var_list_is_list (by trivial : eo_var_list Term.__eo_List_nil)
  have hRec : __eo_list_concat_rec xs Term.__eo_List_nil = xs :=
    eo_list_concat_rec_nil_eq_of_var_list hVarList
  simpa [__eo_list_concat, hXsList, hNilList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hRec

private theorem eo_var_list_concat_rec
    {xs ys : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys) :
    eo_var_list (__eo_list_concat_rec xs ys) := by
  rcases eo_smt_var_env_of_var_list hXsVar with ⟨xsVars, hXsEnv⟩
  rcases eo_smt_var_env_of_var_list hYsVar with ⟨ysVars, hYsEnv⟩
  exact eo_var_list_of_env (EoSmtVarEnv.concat_rec hXsEnv hYsEnv)

private theorem eo_var_list_concat
    {xs ys : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys) :
    eo_var_list (__eo_list_concat Term.__eo_List_cons xs ys) := by
  rcases eo_smt_var_env_of_var_list hXsVar with ⟨xsVars, hXsEnv⟩
  rcases eo_smt_var_env_of_var_list hYsVar with ⟨ysVars, hYsEnv⟩
  exact eo_var_list_of_env (EoSmtVarEnv.concat hXsEnv hYsEnv)

private theorem eo_var_list_mem_concat_rec_iff
    {xs ys z : Term} (hXsVar : eo_var_list xs)
    (hYsVar : eo_var_list ys) :
    eo_var_list_mem z (__eo_list_concat_rec xs ys) ↔
      eo_var_list_mem z xs ∨ eo_var_list_mem z ys := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hXsVar
  | case2 f x tail ih =>
      cases f <;> try exact False.elim hXsVar
      case __eo_List_cons =>
        cases x <;> try exact False.elim hXsVar
        case Var name T =>
          cases name <;> try exact False.elim hXsVar
          case String s =>
            have hTailVar : eo_var_list tail := hXsVar
            have hConcatTailVar :
                eo_var_list (__eo_list_concat_rec tail ys) :=
              eo_var_list_concat_rec hTailVar hYsVar
            have hConcatTailNe :
                __eo_list_concat_rec tail ys ≠ Term.Stuck :=
              eo_var_list_ne_stuck hConcatTailVar
            have hCons :
                __eo_list_concat_rec
                    (Term.Apply (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) tail) ys =
                  Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T))
                    (__eo_list_concat_rec tail ys) := by
              have hYsNe : ys ≠ Term.Stuck := eo_var_list_ne_stuck hYsVar
              rw [eo_list_concat_rec_cons_left_of_suffix_ne
                Term.__eo_List_cons (Term.Var (Term.String s) T)
                tail ys hYsNe]
              exact eo_mk_apply_of_ne_stuck_local
                (by intro h; cases h) hConcatTailNe
            rw [hCons]
            have hTailIff :=
              ih hTailVar
            simp [eo_var_list_mem, hTailIff, or_assoc]
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          have hYsNe : ys ≠ Term.Stuck := eo_var_list_ne_stuck hYsVar
          rw [eo_list_concat_rec_nil_left_of_ne hYsNe]
          simp [eo_var_list_mem]
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hXsVar
      | _ =>
          exact False.elim hXsVar

private theorem eo_var_list_mem_concat_iff
    {xs ys z : Term} (hXsVar : eo_var_list xs)
    (hYsVar : eo_var_list ys) :
    eo_var_list_mem z (__eo_list_concat Term.__eo_List_cons xs ys) ↔
      eo_var_list_mem z xs ∨ eo_var_list_mem z ys := by
  have hXsList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hXsVar
  have hYsList : __eo_is_list Term.__eo_List_cons ys = Term.Boolean true :=
    eo_var_list_is_list hYsVar
  simpa [__eo_list_concat, hXsList, hYsList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using
    (eo_var_list_mem_concat_rec_iff
      (xs := xs) (ys := ys) (z := z) hXsVar hYsVar)

private theorem eo_var_list_mem_concat_rec_cons_comm
    (s : native_String) (T tail bvs z : Term)
    (hTailVar : eo_var_list tail) (hBvsVar : eo_var_list bvs) :
    eo_var_list_mem z
        (__eo_list_concat_rec
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) tail) bvs) ↔
      eo_var_list_mem z
        (__eo_list_concat_rec tail
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) bvs)) := by
  have hConsTailVar :
      eo_var_list
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) tail) := by
    simpa [eo_var_list] using hTailVar
  have hConsBvsVar :
      eo_var_list
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) bvs) := by
    simpa [eo_var_list] using hBvsVar
  rw [eo_var_list_mem_concat_rec_iff
        (xs := Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) tail)
        (ys := bvs) (z := z) hConsTailVar hBvsVar,
      eo_var_list_mem_concat_rec_iff
        (xs := tail)
        (ys := Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) bvs) (z := z)
        hTailVar hConsBvsVar]
  simp [eo_var_list_mem, or_left_comm, or_comm]

private theorem eo_is_neg_list_find_rec_false_of_var_list_mem
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck)
    (hMem : eo_var_list_mem z xs) :
    ∀ n : native_Int,
      native_zlt n 0 = false ->
        __eo_is_neg
            (__eo_list_find_rec xs z (Term.Numeral n)) =
          Term.Boolean false := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hxNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            rcases hMem with hHead | hTail
            · intro n hN
              have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) z =
                    Term.Boolean true := by
                rw [hHead]
                exact eo_eq_true_of_eq_ne_stuck hz
              simp [__eo_list_find_rec, hEqTerm, __eo_ite,
                __eo_is_neg, native_ite, native_teq, hN]
            · intro n hN
              by_cases hEq :
                  Term.Var (Term.String s) T = z
              · have hEqTerm :
                    __eo_eq (Term.Var (Term.String s) T) z =
                      Term.Boolean true := by
                  rw [hEq]
                  exact eo_eq_true_of_eq_ne_stuck hz
                simp [__eo_list_find_rec, hEqTerm, __eo_ite,
                  __eo_is_neg, native_ite, native_teq, hN]
              · have hEqTerm :
                    __eo_eq (Term.Var (Term.String s) T) z =
                      Term.Boolean false :=
                  eo_eq_false_of_ne_nonstuck hEq hxNe hz
                have hN' :
                    native_zlt (native_zplus n 1) 0 = false :=
                  native_zlt_plus_one_nonneg hN
                have hRec :=
                  ih hTailVar hTail (native_zplus n 1) hN'
                simpa [__eo_list_find_rec, hEqTerm, __eo_ite,
                  native_ite, native_teq] using hRec
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          simpa [__eo_list_erase_all_rec, eo_var_list_mem] using hMem
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_is_neg_list_find_false_of_var_list_mem
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck)
    (hMem : eo_var_list_mem z xs) :
    __eo_is_neg (__eo_list_find Term.__eo_List_cons xs z) =
      Term.Boolean false := by
  have hList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hFindRec :
      __eo_is_neg (__eo_list_find_rec xs z (Term.Numeral 0)) =
        Term.Boolean false :=
    eo_is_neg_list_find_rec_false_of_var_list_mem
      hVarList hz hMem 0 hZero
  simpa [__eo_list_find, hList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hFindRec

private theorem eo_var_list_mem_of_eo_is_neg_list_find_rec_false
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck) :
    ∀ n : native_Int,
      native_zlt n 0 = false ->
        __eo_is_neg
            (__eo_list_find_rec xs z (Term.Numeral n)) =
          Term.Boolean false ->
        eo_var_list_mem z xs := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hxNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            intro n hN hFind
            by_cases hEq :
                Term.Var (Term.String s) T = z
            · exact Or.inl hEq
            · have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) z =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hEq hxNe hz
              have hTailFind :
                  __eo_is_neg
                      (__eo_list_find_rec y z
                        (Term.Numeral (native_zplus n 1))) =
                    Term.Boolean false := by
                simpa [__eo_list_find_rec, hEqTerm, __eo_ite,
                  native_ite, native_teq] using hFind
              have hN' :
                  native_zlt (native_zplus n 1) 0 = false :=
                native_zlt_plus_one_nonneg hN
              exact Or.inr (ih hTailVar (native_zplus n 1) hN'
                hTailFind)
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          intro n hN hFind
          have hNeg : native_zlt (-1 : native_Int) 0 = true := by
            native_decide
          simp [__eo_list_find_rec, __eo_is_neg, hNeg] at hFind
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
      exact False.elim hVarList

private theorem eo_is_neg_list_find_rec_true_of_var_list_not_mem
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck)
    (hNotMem : ¬ eo_var_list_mem z xs) :
    ∀ n : native_Int,
      native_zlt n 0 = false ->
        __eo_is_neg
            (__eo_list_find_rec xs z (Term.Numeral n)) =
          Term.Boolean true := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hNotTail : ¬ eo_var_list_mem z y := by
              intro hTail
              exact hNotMem (Or.inr hTail)
            intro n hN
            by_cases hEq :
                Term.Var (Term.String s) T = z
            · exact False.elim (hNotMem (Or.inl hEq))
            · have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) z =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hEq hHeadNe hz
              have hN' :
                  native_zlt (native_zplus n 1) 0 = false :=
                native_zlt_plus_one_nonneg hN
              have hRec :=
                ih hTailVar hNotTail (native_zplus n 1) hN'
              simpa [__eo_list_find_rec, hEqTerm, __eo_ite,
                __eo_add, native_ite, native_teq] using hRec
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          intro n hN
          have hNeg : native_zlt (-1 : native_Int) 0 = true := by
            native_decide
          simp [__eo_list_find_rec, __eo_is_neg, hNeg]
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_is_neg_list_find_true_of_var_list_not_mem
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck)
    (hNotMem : ¬ eo_var_list_mem z xs) :
    __eo_is_neg (__eo_list_find Term.__eo_List_cons xs z) =
      Term.Boolean true := by
  have hList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hFindRec :
      __eo_is_neg (__eo_list_find_rec xs z (Term.Numeral 0)) =
        Term.Boolean true :=
    eo_is_neg_list_find_rec_true_of_var_list_not_mem
      hVarList hz hNotMem 0 hZero
  simpa [__eo_list_find, hList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hFindRec

private theorem eo_var_list_mem_of_eo_is_neg_list_find_false
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck)
    (hFind :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons xs z) =
        Term.Boolean false) :
    eo_var_list_mem z xs := by
  have hList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hFindRec :
      __eo_is_neg (__eo_list_find_rec xs z (Term.Numeral 0)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hFind
  exact eo_var_list_mem_of_eo_is_neg_list_find_rec_false
    hVarList hz 0 hZero hFindRec

private theorem scannerModelRel_bvs_of_mem_iff
    {xs bvs1 bvs2 : Term} {M N : SmtModel}
    (hBvs1 : eo_var_list bvs1) (hBvs2 : eo_var_list bvs2)
    (hMemIff :
      ∀ (s : native_String) (T : Term),
        eo_var_list_mem (Term.Var (Term.String s) T) bvs2 ↔
          eo_var_list_mem (Term.Var (Term.String s) T) bvs1)
    (hRel : scannerModelRel xs bvs1 M N) :
    scannerModelRel xs bvs2 M N := by
  refine ⟨hRel.globals, ?_⟩
  intro s T hAllowed
  apply hRel.vars_eq s T
  rcases eo_ite_false_branch_eq_false_cases
      (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs
        (Term.Var (Term.String s) T)))
      (__eo_is_neg (__eo_list_find Term.__eo_List_cons bvs2
        (Term.Var (Term.String s) T))) hAllowed with
    hXsMiss | ⟨hXsHit, hBvs2Hit⟩
  · simp [__eo_ite, hXsMiss, native_ite, native_teq]
  · have hMem2 :
        eo_var_list_mem (Term.Var (Term.String s) T) bvs2 :=
      eo_var_list_mem_of_eo_is_neg_list_find_false
        hBvs2 (term_var_string_ne_stuck s T) hBvs2Hit
    have hMem1 :
        eo_var_list_mem (Term.Var (Term.String s) T) bvs1 :=
      (hMemIff s T).1 hMem2
    have hBvs1Hit :
        __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs1
          (Term.Var (Term.String s) T)) =
          Term.Boolean false :=
      eo_is_neg_list_find_false_of_var_list_mem
        hBvs1 (term_var_string_ne_stuck s T) hMem1
    simp [__eo_ite, hXsHit, hBvs1Hit, native_ite, native_teq]

private theorem scannerModelRel_concat_rec_cons_comm
    (xs tail bvs : Term) (M N : SmtModel)
    (s : native_String) (T : Term)
    (hTailVar : eo_var_list tail) (hBvsVar : eo_var_list bvs)
    (hRel :
      scannerModelRel xs
        (__eo_list_concat_rec
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) tail) bvs) M N) :
    scannerModelRel xs
      (__eo_list_concat_rec tail
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) bvs)) M N := by
  have hConsTailVar :
      eo_var_list
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) tail) := by
    simpa [eo_var_list] using hTailVar
  have hConsBvsVar :
      eo_var_list
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) bvs) := by
    simpa [eo_var_list] using hBvsVar
  have hLeftVar :
      eo_var_list
        (__eo_list_concat_rec
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) tail) bvs) :=
    eo_var_list_concat_rec hConsTailVar hBvsVar
  have hRightVar :
      eo_var_list
        (__eo_list_concat_rec tail
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) bvs)) :=
    eo_var_list_concat_rec hTailVar hConsBvsVar
  exact scannerModelRel_bvs_of_mem_iff
    hLeftVar hRightVar
    (fun s' T' =>
      (eo_var_list_mem_concat_rec_cons_comm
        s T tail bvs (Term.Var (Term.String s') T')
        hTailVar hBvsVar).symm)
    hRel

private theorem scannerModelRel_concat_rec_cons_comm_symm
    (xs tail bvs : Term) (M N : SmtModel)
    (s : native_String) (T : Term)
    (hTailVar : eo_var_list tail) (hBvsVar : eo_var_list bvs)
    (hRel :
      scannerModelRel xs
        (__eo_list_concat_rec tail
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) bvs)) M N) :
    scannerModelRel xs
      (__eo_list_concat_rec
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) tail) bvs) M N := by
  have hConsTailVar :
      eo_var_list
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) tail) := by
    simpa [eo_var_list] using hTailVar
  have hConsBvsVar :
      eo_var_list
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) bvs) := by
    simpa [eo_var_list] using hBvsVar
  have hLeftVar :
      eo_var_list
        (__eo_list_concat_rec
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) tail) bvs) :=
    eo_var_list_concat_rec hConsTailVar hBvsVar
  have hRightVar :
      eo_var_list
        (__eo_list_concat_rec tail
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) bvs)) :=
    eo_var_list_concat_rec hTailVar hConsBvsVar
  exact scannerModelRel_bvs_of_mem_iff
    hRightVar hLeftVar
    (fun s' T' =>
      eo_var_list_mem_concat_rec_cons_comm
        s T tail bvs (Term.Var (Term.String s') T')
        hTailVar hBvsVar)
    hRel

private theorem eo_var_list_mem_erase_all_rec_of_ne
    {xs z e : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (he : e ≠ Term.Stuck)
    (hNe : z ≠ e) (hMem : eo_var_list_mem z xs) :
    eo_var_list_mem z (__eo_list_erase_all_rec xs e) := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hEraseTailVar :
                eo_var_list (__eo_list_erase_all_rec y e) :=
              eo_var_list_erase_all_rec hTailVar he
            have hEraseTailNe :
                __eo_list_erase_all_rec y e ≠ Term.Stuck :=
              eo_var_list_ne_stuck hEraseTailVar
            rcases hMem with hHead | hTail
            · have hEHead :
                  e ≠ Term.Var (Term.String s) T := by
                intro hEq
                apply hNe
                exact hHead.symm.trans hEq.symm
              have hEqTerm :
                  __eo_eq e (Term.Var (Term.String s) T) =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hEHead he hHeadNe
              simpa [eo_var_list_mem, __eo_list_erase_all_rec,
                hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                hHeadNe, SmtEval.native_not] using
                (Or.inl hHead :
                  Term.Var (Term.String s) T = z ∨
                    eo_var_list_mem z (__eo_list_erase_all_rec y e))
            · have hRec :
                  eo_var_list_mem z (__eo_list_erase_all_rec y e) :=
                ih hTailVar hTail
              by_cases hEHead :
                  e = Term.Var (Term.String s) T
              · have hEqTerm :
                    __eo_eq e (Term.Var (Term.String s) T) =
                      Term.Boolean true := by
                  rw [hEHead]
                  exact eo_eq_true_of_eq_ne_stuck hHeadNe
                simpa [eo_var_list_mem, __eo_list_erase_all_rec,
                  hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                  hHeadNe, SmtEval.native_not] using hRec
              · have hEqTerm :
                    __eo_eq e (Term.Var (Term.String s) T) =
                      Term.Boolean false :=
                  eo_eq_false_of_ne_nonstuck hEHead he hHeadNe
                simpa [eo_var_list_mem, __eo_list_erase_all_rec,
                  hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                  hHeadNe, SmtEval.native_not] using
                  (Or.inr hRec :
                    Term.Var (Term.String s) T = z ∨
                      eo_var_list_mem z (__eo_list_erase_all_rec y e))
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          have hFalse : False := by
            simpa [__eo_list_erase_all_rec, eo_var_list_mem] using hMem
          exact False.elim hFalse
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_mem_of_mem_erase_all_rec
    {xs z e : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (he : e ≠ Term.Stuck)
    (hMem : eo_var_list_mem z (__eo_list_erase_all_rec xs e)) :
    eo_var_list_mem z xs := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hEraseTailVar :
                eo_var_list (__eo_list_erase_all_rec y e) :=
              eo_var_list_erase_all_rec hTailVar he
            have hEraseTailNe :
                __eo_list_erase_all_rec y e ≠ Term.Stuck :=
              eo_var_list_ne_stuck hEraseTailVar
            by_cases hEHead :
                e = Term.Var (Term.String s) T
            · have hEqTerm :
                  __eo_eq e (Term.Var (Term.String s) T) =
                    Term.Boolean true := by
                rw [hEHead]
                exact eo_eq_true_of_eq_ne_stuck hHeadNe
              have hMemTail :
                  eo_var_list_mem z (__eo_list_erase_all_rec y e) := by
                simpa [eo_var_list_mem, __eo_list_erase_all_rec,
                  hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                  hHeadNe, SmtEval.native_not] using hMem
              exact Or.inr (ih hTailVar hMemTail)
            · have hEqTerm :
                  __eo_eq e (Term.Var (Term.String s) T) =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hEHead he hHeadNe
              have hMemCons :
                  Term.Var (Term.String s) T = z ∨
                    eo_var_list_mem z (__eo_list_erase_all_rec y e) := by
                simpa [eo_var_list_mem, __eo_list_erase_all_rec,
                  hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                  hHeadNe, SmtEval.native_not] using hMem
              rcases hMemCons with hHead | hTail
              · exact Or.inl hHead
              · exact Or.inr (ih hTailVar hTail)
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          have hFalse : False := by
            cases e <;>
              simp [__eo_list_erase_all_rec, eo_var_list_mem] at hMem he
          exact False.elim hFalse
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_mem_of_mem_setof_rec
    {xs z : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck)
    (hMem : eo_var_list_mem z (__eo_list_setof_rec xs)) :
    eo_var_list_mem z xs := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            let head := Term.Var (Term.String s) T
            have hHeadNe : head ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hSetTailVar : eo_var_list (__eo_list_setof_rec y) :=
              eo_var_list_setof_rec hTailVar
            have hEraseVar :
                eo_var_list
                  (__eo_list_erase_all_rec (__eo_list_setof_rec y) head) :=
              eo_var_list_erase_all_rec hSetTailVar hHeadNe
            have hEraseNe :
                __eo_list_erase_all_rec (__eo_list_setof_rec y) head ≠
                  Term.Stuck :=
              eo_var_list_ne_stuck hEraseVar
            have hMemCons :
                head = z ∨
                  eo_var_list_mem z
                    (__eo_list_erase_all_rec (__eo_list_setof_rec y) head) := by
              simpa [head, eo_var_list_mem, __eo_list_setof_rec,
                __eo_mk_apply, hEraseNe] using hMem
            rcases hMemCons with hHead | hTail
            · exact Or.inl hHead
            · have hMemSetTail :
                  eo_var_list_mem z (__eo_list_setof_rec y) :=
                eo_var_list_mem_of_mem_erase_all_rec
                  hSetTailVar hz hHeadNe hTail
              exact Or.inr (ih hTailVar hMemSetTail)
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          exact False.elim hMem
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_mem_of_mem_setof
    {xs z : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck)
    (hMem :
      eo_var_list_mem z (__eo_list_setof Term.__eo_List_cons xs)) :
    eo_var_list_mem z xs := by
  have hList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hMemRec :
      eo_var_list_mem z (__eo_list_setof_rec xs) := by
    simpa [__eo_list_setof, hList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hMem
  exact eo_var_list_mem_of_mem_setof_rec hVarList hz hMemRec

private theorem eo_var_list_mem_of_mem_diff_rec_left
    {xs ys z : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys)
    (hz : z ≠ Term.Stuck)
    (hMem : eo_var_list_mem z (__eo_list_diff_rec xs ys)) :
    eo_var_list_mem z xs := by
  induction xs, ys using __eo_list_diff_rec.induct with
  | case1 ys =>
      exact False.elim hXsVar
  | case2 xs hYsStuck =>
      exact False.elim (eo_var_list_ne_stuck hYsVar rfl)
  | case3 f x y ys hYsNotStuck v0 ih =>
      cases f <;> try exact False.elim hXsVar
      case __eo_List_cons =>
        cases x <;> try exact False.elim hXsVar
        case Var name T =>
          cases name <;> try exact False.elim hXsVar
          case String s =>
            have hTailVar : eo_var_list y := hXsVar
            let head := Term.Var (Term.String s) T
            have hHeadNe : head ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hEraseVar :
                eo_var_list (__eo_list_erase_rec ys head) :=
              eo_var_list_erase_rec hYsVar hHeadNe
            have hEraseNe : __eo_list_erase_rec ys head ≠ Term.Stuck :=
              eo_var_list_ne_stuck hEraseVar
            have hRecNe : __eo_list_diff_rec y v0 ≠ Term.Stuck :=
              eo_var_list_ne_stuck
                (eo_var_list_diff_rec hTailVar (by simpa [v0] using hEraseVar))
            by_cases hSame : __eo_list_erase_rec ys head = ys
            · have hv0 : v0 = ys := by
                simpa [v0] using hSame
              have hYsNe : ys ≠ Term.Stuck :=
                eo_var_list_ne_stuck hYsVar
              have hEqTerm : __eo_eq v0 ys = Term.Boolean true := by
                rw [hv0]
                exact eo_eq_true_of_eq_ne_stuck hYsNe
              have hMemCons :
                  head = z ∨ eo_var_list_mem z (__eo_list_diff_rec y v0) := by
                simpa [head, eo_var_list_mem, __eo_list_diff_rec, v0,
                  hEqTerm, __eo_prepend_if, hHeadNe, hRecNe] using hMem
              rcases hMemCons with hHead | hTail
              · exact Or.inl hHead
              · exact Or.inr
                  (ih hTailVar (by simpa [v0] using hEraseVar) hTail)
            · have hv0Ne : v0 ≠ ys := by
                simpa [v0] using hSame
              have hYsNe : ys ≠ Term.Stuck :=
                eo_var_list_ne_stuck hYsVar
              have hv0Stuck : v0 ≠ Term.Stuck := by
                simpa [v0] using hEraseNe
              have hEqTerm : __eo_eq v0 ys = Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hv0Ne hv0Stuck hYsNe
              have hMemTail :
                  eo_var_list_mem z (__eo_list_diff_rec y v0) := by
                simpa [__eo_list_diff_rec, v0, hEqTerm,
                  __eo_prepend_if, hRecNe] using hMem
              exact Or.inr
                (ih hTailVar (by simpa [v0] using hEraseVar) hMemTail)
  | case4 nil ys hNil hYs hNotApply =>
      cases nil with
      | __eo_List_nil =>
          simpa [__eo_list_diff_rec, eo_var_list_mem] using hMem
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApply g x a rfl)
          | _ =>
              exact False.elim hXsVar
      | _ =>
          exact False.elim hXsVar

private theorem eo_var_list_mem_of_mem_diff_left
    {xs ys z : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys)
    (hz : z ≠ Term.Stuck)
    (hMem :
      eo_var_list_mem z (__eo_list_diff Term.__eo_List_cons xs ys)) :
    eo_var_list_mem z xs := by
  have hXsList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hXsVar
  have hYsList : __eo_is_list Term.__eo_List_cons ys = Term.Boolean true :=
    eo_var_list_is_list hYsVar
  have hMemRec :
      eo_var_list_mem z (__eo_list_diff_rec xs ys) := by
    simpa [__eo_list_diff, hXsList, hYsList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hMem
  exact eo_var_list_mem_of_mem_diff_rec_left hXsVar hYsVar hz hMemRec

private def eo_var_list_nodup : Term -> Prop
  | Term.__eo_List_nil => True
  | Term.Apply (Term.Apply Term.__eo_List_cons x) xs =>
      ¬ eo_var_list_mem x xs ∧ eo_var_list_nodup xs
  | _ => False

private theorem eo_var_list_mem_erase_rec_of_ne
    {xs z e : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (he : e ≠ Term.Stuck)
    (hNe : z ≠ e) (hMem : eo_var_list_mem z xs) :
    eo_var_list_mem z (__eo_list_erase_rec xs e) := by
  induction xs, e using __eo_list_erase_rec.induct with
  | case1 e =>
      exact False.elim hVarList
  | case2 xs hEStuck =>
      exact False.elim (he rfl)
  | case3 f x y e hENotStuck ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            rcases hMem with hHead | hTail
            · have hHeadNotE :
                  Term.Var (Term.String s) T ≠ e := by
                intro hEq
                exact hNe (hHead.symm.trans hEq)
              have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) e =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hHeadNotE hHeadNe he
              have hEraseTailVar :
                  eo_var_list (__eo_list_erase_rec y e) :=
                eo_var_list_erase_rec hTailVar he
              have hEraseTailNe :
                  __eo_list_erase_rec y e ≠ Term.Stuck :=
                eo_var_list_ne_stuck hEraseTailVar
              simpa [eo_var_list_mem, __eo_list_erase_rec, hEqTerm,
                __eo_ite, __eo_mk_apply, hEraseTailNe, native_ite,
                native_teq] using
                (Or.inl hHead :
                  Term.Var (Term.String s) T = z ∨
                    eo_var_list_mem z (__eo_list_erase_rec y e))
            · by_cases hHeadEqE :
                  Term.Var (Term.String s) T = e
              · have hEqTerm :
                    __eo_eq (Term.Var (Term.String s) T) e =
                      Term.Boolean true := by
                  rw [hHeadEqE]
                  exact eo_eq_true_of_eq_ne_stuck he
                simpa [eo_var_list_mem, __eo_list_erase_rec, hEqTerm,
                  __eo_ite, native_ite, native_teq] using hTail
              · have hEqTerm :
                    __eo_eq (Term.Var (Term.String s) T) e =
                      Term.Boolean false :=
                  eo_eq_false_of_ne_nonstuck hHeadEqE hHeadNe he
                have hEraseTailVar :
                    eo_var_list (__eo_list_erase_rec y e) :=
                  eo_var_list_erase_rec hTailVar he
                have hEraseTailNe :
                    __eo_list_erase_rec y e ≠ Term.Stuck :=
                  eo_var_list_ne_stuck hEraseTailVar
                have hRec :
                    eo_var_list_mem z (__eo_list_erase_rec y e) :=
                  ih hTailVar he hNe hTail
                simpa [eo_var_list_mem, __eo_list_erase_rec, hEqTerm,
                  __eo_ite, __eo_mk_apply, hEraseTailNe, native_ite,
                  native_teq] using
                  (Or.inr hRec :
                    Term.Var (Term.String s) T = z ∨
                      eo_var_list_mem z (__eo_list_erase_rec y e))
  | case4 nil e hNil hE hNotApply =>
      cases nil with
      | __eo_List_nil =>
          exact False.elim hMem
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_not_mem_of_erase_rec_eq_self
    {xs e : Term} (hVarList : eo_var_list xs)
    (he : e ≠ Term.Stuck)
    (hEq : __eo_list_erase_rec xs e = xs) :
    ¬ eo_var_list_mem e xs := by
  induction xs, e using __eo_list_erase_rec.induct with
  | case1 e =>
      exact False.elim hVarList
  | case2 xs hEStuck =>
      exact False.elim (he rfl)
  | case3 f x y e hENotStuck ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            intro hMem
            by_cases hHeadEqE :
                Term.Var (Term.String s) T = e
            · have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) e =
                    Term.Boolean true := by
                rw [hHeadEqE]
                exact eo_eq_true_of_eq_ne_stuck he
              have hShort :
                  y =
                    Term.Apply
                      (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s) T)) y := by
                simpa [__eo_list_erase_rec, hEqTerm, __eo_ite,
                  native_ite, native_teq] using hEq
              have hSize := congrArg sizeOf hShort
              simp at hSize
            · have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) e =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hHeadEqE hHeadNe he
              have hEraseTailVar :
                  eo_var_list (__eo_list_erase_rec y e) :=
                eo_var_list_erase_rec hTailVar he
              have hEraseTailNe :
                  __eo_list_erase_rec y e ≠ Term.Stuck :=
                eo_var_list_ne_stuck hEraseTailVar
              have hTailEq :
                  __eo_list_erase_rec y e = y := by
                have hConsEq :
                    Term.Apply
                        (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T))
                        (__eo_list_erase_rec y e) =
                      Term.Apply
                        (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T)) y := by
                  simpa [__eo_list_erase_rec, hEqTerm, __eo_ite,
                    __eo_mk_apply, hEraseTailNe, native_ite, native_teq]
                    using hEq
                injection hConsEq with _ hTailEq
              rcases hMem with hHead | hTail
              · exact hHeadEqE hHead
              · exact ih hTailVar he hTailEq hTail
  | case4 nil e hNil hE hNotApply =>
      cases nil with
      | __eo_List_nil =>
          intro hMem
          cases e <;> simp [__eo_list_erase_all_rec, eo_var_list_mem] at hMem he
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_mem_of_mem_erase_rec
    {xs z e : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (he : e ≠ Term.Stuck)
    (hMem : eo_var_list_mem z (__eo_list_erase_rec xs e)) :
    eo_var_list_mem z xs := by
  induction xs, e using __eo_list_erase_rec.induct with
  | case1 e =>
      exact False.elim hVarList
  | case2 xs hEStuck =>
      exact False.elim (he rfl)
  | case3 f x y e hENotStuck ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            let head := Term.Var (Term.String s) T
            have hHeadNe : head ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            by_cases hHeadEqE : head = e
            · have hEqTerm : __eo_eq head e = Term.Boolean true := by
                rw [hHeadEqE]
                exact eo_eq_true_of_eq_ne_stuck he
              have hTailMem : eo_var_list_mem z y := by
                simpa [head, eo_var_list_mem, __eo_list_erase_rec,
                  hEqTerm, __eo_ite, native_ite, native_teq] using hMem
              exact Or.inr hTailMem
            · have hEqTerm : __eo_eq head e = Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hHeadEqE hHeadNe he
              have hEraseTailVar :
                  eo_var_list (__eo_list_erase_rec y e) :=
                eo_var_list_erase_rec hTailVar he
              have hEraseTailNe :
                  __eo_list_erase_rec y e ≠ Term.Stuck :=
                eo_var_list_ne_stuck hEraseTailVar
              have hMemCons :
                  head = z ∨
                    eo_var_list_mem z (__eo_list_erase_rec y e) := by
                simpa [head, eo_var_list_mem, __eo_list_erase_rec,
                  hEqTerm, __eo_ite, __eo_mk_apply, hEraseTailNe,
                  native_ite, native_teq] using hMem
              rcases hMemCons with hHead | hTail
              · exact Or.inl hHead
              · exact Or.inr (ih hTailVar he hTail)
  | case4 nil e hNil hE hNotApply =>
      cases nil with
      | __eo_List_nil =>
          have hFalse : False := by
            cases e <;> simp [__eo_list_erase_rec, eo_var_list_mem] at hMem he
          exact False.elim hFalse
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_erase_rec_eq_self_of_not_mem
    {xs e : Term} (hVarList : eo_var_list xs)
    (he : e ≠ Term.Stuck)
    (hNotMem : ¬ eo_var_list_mem e xs) :
    __eo_list_erase_rec xs e = xs := by
  induction xs, e using __eo_list_erase_rec.induct with
  | case1 e =>
      exact False.elim hVarList
  | case2 xs hEStuck =>
      exact False.elim (he rfl)
  | case3 f x y e hENotStuck ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            let head := Term.Var (Term.String s) T
            have hHeadNe : head ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hHeadNotE : head ≠ e := by
              intro hEq
              exact hNotMem (Or.inl hEq)
            have hTailNotMem : ¬ eo_var_list_mem e y := by
              intro hTail
              exact hNotMem (Or.inr hTail)
            have hEqTerm : __eo_eq head e = Term.Boolean false :=
              eo_eq_false_of_ne_nonstuck hHeadNotE hHeadNe he
            have hTailEq : __eo_list_erase_rec y e = y :=
              ih hTailVar he hTailNotMem
            have hTailNe : y ≠ Term.Stuck :=
              eo_var_list_ne_stuck hTailVar
            simpa [head, __eo_list_erase_rec, hEqTerm, __eo_ite,
              hTailEq, native_ite, native_teq] using
              eo_mk_apply_of_ne_stuck_local (by simp) hTailNe
  | case4 nil e hNil hE hNotApply =>
      cases nil with
      | __eo_List_nil =>
          cases e <;>
            first | exact False.elim (he rfl) | rfl
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_mem_of_erase_rec_changed
    {xs e : Term} (hVarList : eo_var_list xs)
    (he : e ≠ Term.Stuck)
    (hChanged : __eo_list_erase_rec xs e ≠ xs) :
    eo_var_list_mem e xs := by
  by_cases hMem : eo_var_list_mem e xs
  · exact hMem
  · exact False.elim
      (hChanged
        (eo_var_list_erase_rec_eq_self_of_not_mem hVarList he hMem))

private theorem eo_list_minclude_rec_cons_true_eq
    {xs e tail : Term} (hXsVar : eo_var_list xs) :
    __eo_list_minclude_rec xs
        (Term.Apply (Term.Apply Term.__eo_List_cons e) tail)
        (Term.Boolean true) =
      __eo_list_minclude_rec (__eo_list_erase_rec xs e) tail
        (__eo_not (__eo_eq (__eo_list_erase_rec xs e) xs)) := by
  have hXsNe : xs ≠ Term.Stuck := eo_var_list_ne_stuck hXsVar
  cases xs <;> first | exact False.elim (hXsNe rfl) | rfl

private theorem eo_list_minclude_rec_false_of_var_lists
    {xs ys : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys) :
    __eo_list_minclude_rec xs ys (Term.Boolean false) =
      Term.Boolean false := by
  have hXsNe : xs ≠ Term.Stuck := eo_var_list_ne_stuck hXsVar
  have hYsNe : ys ≠ Term.Stuck := eo_var_list_ne_stuck hYsVar
  cases xs <;> cases ys <;>
    first
    | exact False.elim (hXsNe rfl)
    | exact False.elim (hYsNe rfl)
    | rfl

private theorem eo_var_list_mem_head_of_minclude_rec_cons
    {xs e tail : Term} (hXsVar : eo_var_list xs)
    (hTailVar : eo_var_list tail) (he : e ≠ Term.Stuck)
    (hIncl :
      __eo_list_minclude_rec xs
          (Term.Apply (Term.Apply Term.__eo_List_cons e) tail)
          (Term.Boolean true) =
        Term.Boolean true) :
    eo_var_list_mem e xs := by
  by_cases hMem : eo_var_list_mem e xs
  · exact hMem
  rw [eo_list_minclude_rec_cons_true_eq hXsVar] at hIncl
  have hEraseEq : __eo_list_erase_rec xs e = xs :=
    eo_var_list_erase_rec_eq_self_of_not_mem hXsVar he hMem
  rw [hEraseEq] at hIncl
  have hXsNe : xs ≠ Term.Stuck := eo_var_list_ne_stuck hXsVar
  have hEqTerm : __eo_eq xs xs = Term.Boolean true :=
    eo_eq_true_of_eq_ne_stuck hXsNe
  have hFalse :
      __eo_list_minclude_rec xs tail (Term.Boolean false) =
        Term.Boolean false :=
    eo_list_minclude_rec_false_of_var_lists hXsVar hTailVar
  simpa [hEqTerm, __eo_not, hFalse, SmtEval.native_not] using hIncl

private theorem eo_var_list_mem_of_minclude_rec
    {xs ys z : Term} (hXsVar : eo_var_list xs)
    (hYsVar : eo_var_list ys) (hz : z ≠ Term.Stuck)
    (hIncl :
      __eo_list_minclude_rec xs ys (Term.Boolean true) =
        Term.Boolean true)
    (hMem : eo_var_list_mem z ys) :
    eo_var_list_mem z xs := by
  induction ys using __eo_list_setof_rec.induct generalizing xs with
  | case1 =>
      exact False.elim hYsVar
  | case2 f x y ih =>
      cases f <;> try exact False.elim hYsVar
      case __eo_List_cons =>
        cases x <;> try exact False.elim hYsVar
        case Var name T =>
          cases name <;> try exact False.elim hYsVar
          case String s =>
            let head := Term.Var (Term.String s) T
            have hTailVar : eo_var_list y := hYsVar
            have hHeadNe : head ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hHeadMemXs :
                eo_var_list_mem head xs :=
              eo_var_list_mem_head_of_minclude_rec_cons
                hXsVar hTailVar hHeadNe (by
                  simpa [head] using hIncl)
            rcases hMem with hHead | hTail
            · subst z
              exact hHeadMemXs
            · rw [eo_list_minclude_rec_cons_true_eq hXsVar] at hIncl
              have hEraseVar :
                  eo_var_list (__eo_list_erase_rec xs head) :=
                eo_var_list_erase_rec hXsVar hHeadNe
              have hEraseNe :
                  __eo_list_erase_rec xs head ≠ Term.Stuck :=
                eo_var_list_ne_stuck hEraseVar
              have hXsNe : xs ≠ Term.Stuck :=
                eo_var_list_ne_stuck hXsVar
              have hChanged :
                  __eo_list_erase_rec xs head ≠ xs := by
                intro hEq
                exact
                  (eo_var_list_not_mem_of_erase_rec_eq_self
                    hXsVar hHeadNe hEq) hHeadMemXs
              have hEqTerm :
                  __eo_eq (__eo_list_erase_rec xs head) xs =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hChanged hEraseNe hXsNe
              have hFlag :
                  __eo_not
                      (__eo_eq (__eo_list_erase_rec xs head) xs) =
                    Term.Boolean true := by
                simp [__eo_not, hEqTerm, SmtEval.native_not]
              have hTailIncl :
                  __eo_list_minclude_rec (__eo_list_erase_rec xs head) y
                      (Term.Boolean true) =
                    Term.Boolean true := by
                simpa [head, hFlag] using hIncl
              have hTailMemErase :
                  eo_var_list_mem z (__eo_list_erase_rec xs head) :=
                ih hEraseVar hTailVar hTailIncl hTail
              exact
                eo_var_list_mem_of_mem_erase_rec hXsVar hz hHeadNe
                  hTailMemErase
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          exact False.elim hMem
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hYsVar
      | _ =>
          exact False.elim hYsVar

private theorem eo_var_list_mem_of_minclude
    {xs ys z : Term} (hXsVar : eo_var_list xs)
    (hYsVar : eo_var_list ys) (hz : z ≠ Term.Stuck)
    (hIncl :
      __eo_list_minclude Term.__eo_List_cons xs ys =
        Term.Boolean true)
    (hMem : eo_var_list_mem z ys) :
    eo_var_list_mem z xs := by
  have hInclRec :
      __eo_list_minclude_rec xs ys (Term.Boolean true) =
        Term.Boolean true := by
    simpa [eo_list_minclude_eq_rec_of_var_lists hXsVar hYsVar]
      using hIncl
  exact eo_var_list_mem_of_minclude_rec hXsVar hYsVar hz hInclRec hMem

private theorem eo_var_list_mem_left_of_minclude_setof
    {x y z : Term} (hXVar : eo_var_list x) (hYVar : eo_var_list y)
    (hz : z ≠ Term.Stuck)
    (hIncl :
      __eo_list_minclude Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y =
        Term.Boolean true)
    (hMemY : eo_var_list_mem z y) :
    eo_var_list_mem z x := by
  have hMemSetof :
      eo_var_list_mem z (__eo_list_setof Term.__eo_List_cons x) :=
    eo_var_list_mem_of_minclude
      (eo_var_list_setof hXVar) hYVar hz hIncl hMemY
  exact eo_var_list_mem_of_mem_setof hXVar hz hMemSetof

private theorem eo_var_list_mem_diff_rec_of_mem_left_not_mem_right
    {xs ys z : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys)
    (hz : z ≠ Term.Stuck)
    (hMemXs : eo_var_list_mem z xs)
    (hNotMemYs : ¬ eo_var_list_mem z ys) :
    eo_var_list_mem z (__eo_list_diff_rec xs ys) := by
  induction xs, ys using __eo_list_diff_rec.induct with
  | case1 ys =>
      exact False.elim hXsVar
  | case2 xs hYsStuck =>
      exact False.elim (eo_var_list_ne_stuck hYsVar rfl)
  | case3 f x tail ys hYsNotStuck v0 ih =>
      cases f <;> try exact False.elim hXsVar
      case __eo_List_cons =>
        cases x <;> try exact False.elim hXsVar
        case Var name T =>
          cases name <;> try exact False.elim hXsVar
          case String s =>
            let head := Term.Var (Term.String s) T
            have hTailVar : eo_var_list tail := hXsVar
            have hHeadNe : head ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hEraseVar :
                eo_var_list (__eo_list_erase_rec ys head) :=
              eo_var_list_erase_rec hYsVar hHeadNe
            have hEraseNe :
                __eo_list_erase_rec ys head ≠ Term.Stuck :=
              eo_var_list_ne_stuck hEraseVar
            have hRecVar :
                eo_var_list (__eo_list_diff_rec tail v0) :=
              eo_var_list_diff_rec hTailVar (by simpa [v0] using hEraseVar)
            have hRecNe : __eo_list_diff_rec tail v0 ≠ Term.Stuck :=
              eo_var_list_ne_stuck hRecVar
            by_cases hHeadEqZ : head = z
            · subst z
              have hEraseEq :
                  __eo_list_erase_rec ys head = ys :=
                eo_var_list_erase_rec_eq_self_of_not_mem
                  hYsVar hHeadNe hNotMemYs
              have hv0 : v0 = ys := by
                simpa [v0] using hEraseEq
              have hYsNe : ys ≠ Term.Stuck :=
                eo_var_list_ne_stuck hYsVar
              have hEqTerm : __eo_eq v0 ys = Term.Boolean true := by
                rw [hv0]
                exact eo_eq_true_of_eq_ne_stuck hYsNe
              simpa [head, eo_var_list_mem, __eo_list_diff_rec, v0,
                hEqTerm, __eo_prepend_if, hHeadNe, hRecNe] using
                (Or.inl rfl :
                  head = head ∨ eo_var_list_mem head (__eo_list_diff_rec tail v0))
            · have hTailMem : eo_var_list_mem z tail := by
                rcases hMemXs with hHead | hTail
                · exact False.elim (hHeadEqZ hHead)
                · exact hTail
              have hNotMemErase :
                  ¬ eo_var_list_mem z v0 := by
                intro hMemErase
                exact hNotMemYs
                  (eo_var_list_mem_of_mem_erase_rec hYsVar hz hHeadNe
                    (by simpa [v0] using hMemErase))
              have hRecMem :
                  eo_var_list_mem z (__eo_list_diff_rec tail v0) :=
                ih hTailVar (by simpa [v0] using hEraseVar)
                  hTailMem hNotMemErase
              by_cases hSame : __eo_list_erase_rec ys head = ys
              · have hv0 : v0 = ys := by
                  simpa [v0] using hSame
                have hYsNe : ys ≠ Term.Stuck :=
                  eo_var_list_ne_stuck hYsVar
                have hEqTerm : __eo_eq v0 ys = Term.Boolean true := by
                  rw [hv0]
                  exact eo_eq_true_of_eq_ne_stuck hYsNe
                simpa [head, eo_var_list_mem, __eo_list_diff_rec, v0,
                  hEqTerm, __eo_prepend_if, hHeadNe, hRecNe] using
                  (Or.inr hRecMem :
                    head = z ∨ eo_var_list_mem z (__eo_list_diff_rec tail v0))
              · have hv0Ne : v0 ≠ ys := by
                  simpa [v0] using hSame
                have hYsNe : ys ≠ Term.Stuck :=
                  eo_var_list_ne_stuck hYsVar
                have hv0Stuck : v0 ≠ Term.Stuck := by
                  simpa [v0] using hEraseNe
                have hEqTerm : __eo_eq v0 ys = Term.Boolean false :=
                  eo_eq_false_of_ne_nonstuck hv0Ne hv0Stuck hYsNe
                simpa [__eo_list_diff_rec, v0, hEqTerm,
                  __eo_prepend_if, hRecNe] using hRecMem
  | case4 nil ys hNil hYs hNotApply =>
      cases nil with
      | __eo_List_nil =>
          exact False.elim hMemXs
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApply g x a rfl)
          | _ =>
              exact False.elim hXsVar
      | _ =>
          exact False.elim hXsVar

private theorem eo_var_list_mem_diff_of_mem_left_not_mem_right
    {xs ys z : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys)
    (hz : z ≠ Term.Stuck)
    (hMemXs : eo_var_list_mem z xs)
    (hNotMemYs : ¬ eo_var_list_mem z ys) :
    eo_var_list_mem z (__eo_list_diff Term.__eo_List_cons xs ys) := by
  have hXsList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hXsVar
  have hYsList : __eo_is_list Term.__eo_List_cons ys = Term.Boolean true :=
    eo_var_list_is_list hYsVar
  have hMemRec :
      eo_var_list_mem z (__eo_list_diff_rec xs ys) :=
    eo_var_list_mem_diff_rec_of_mem_left_not_mem_right
      hXsVar hYsVar hz hMemXs hNotMemYs
  simpa [__eo_list_diff, hXsList, hYsList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hMemRec

private theorem eo_var_list_not_mem_erase_all_rec_self
    {xs e : Term} (hVarList : eo_var_list xs)
    (he : e ≠ Term.Stuck) :
    ¬ eo_var_list_mem e (__eo_list_erase_all_rec xs e) := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hEraseTailVar :
                eo_var_list (__eo_list_erase_all_rec y e) :=
              eo_var_list_erase_all_rec hTailVar he
            have hEraseTailNe :
                __eo_list_erase_all_rec y e ≠ Term.Stuck :=
              eo_var_list_ne_stuck hEraseTailVar
            intro hMem
            by_cases hEHead :
                e = Term.Var (Term.String s) T
            · have hEqTerm :
                  __eo_eq e (Term.Var (Term.String s) T) =
                    Term.Boolean true := by
                rw [hEHead]
                exact eo_eq_true_of_eq_ne_stuck hHeadNe
              have hTailMem :
                  eo_var_list_mem e (__eo_list_erase_all_rec y e) := by
                simpa [eo_var_list_mem, __eo_list_erase_all_rec,
                  hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                  hHeadNe, SmtEval.native_not] using hMem
              exact ih hTailVar hTailMem
            · have hEqTerm :
                  __eo_eq e (Term.Var (Term.String s) T) =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hEHead he hHeadNe
              have hMemCons :
                  Term.Var (Term.String s) T = e ∨
                    eo_var_list_mem e (__eo_list_erase_all_rec y e) := by
                simpa [eo_var_list_mem, __eo_list_erase_all_rec,
                  hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                  hHeadNe, SmtEval.native_not] using hMem
              rcases hMemCons with hHead | hTail
              · exact hEHead hHead.symm
              · exact ih hTailVar hTail
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          intro hMem
          cases e <;> simp [__eo_list_erase_all_rec, eo_var_list_mem] at hMem he
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_nodup_erase_all_rec
    {xs e : Term} (hVarList : eo_var_list xs)
    (hNoDup : eo_var_list_nodup xs) (he : e ≠ Term.Stuck) :
    eo_var_list_nodup (__eo_list_erase_all_rec xs e) := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hNoMemHead : ¬ eo_var_list_mem
                (Term.Var (Term.String s) T) y := hNoDup.1
            have hNoDupTail : eo_var_list_nodup y := hNoDup.2
            have hEraseTailVar :
                eo_var_list (__eo_list_erase_all_rec y e) :=
              eo_var_list_erase_all_rec hTailVar he
            have hEraseTailNe :
                __eo_list_erase_all_rec y e ≠ Term.Stuck :=
              eo_var_list_ne_stuck hEraseTailVar
            have hRec :
                eo_var_list_nodup (__eo_list_erase_all_rec y e) :=
              ih hTailVar hNoDupTail
            by_cases hEHead :
                e = Term.Var (Term.String s) T
            · have hEqTerm :
                  __eo_eq e (Term.Var (Term.String s) T) =
                    Term.Boolean true := by
                rw [hEHead]
                exact eo_eq_true_of_eq_ne_stuck hHeadNe
              simpa [eo_var_list_nodup, __eo_list_erase_all_rec,
                hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                hHeadNe, SmtEval.native_not] using hRec
            · have hEqTerm :
                  __eo_eq e (Term.Var (Term.String s) T) =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hEHead he hHeadNe
              have hNoMemErase :
                  ¬ eo_var_list_mem (Term.Var (Term.String s) T)
                      (__eo_list_erase_all_rec y e) := by
                intro hMemErase
                exact hNoMemHead
                  (eo_var_list_mem_of_mem_erase_all_rec hTailVar
                    hHeadNe he hMemErase)
              simpa [eo_var_list_nodup, __eo_list_erase_all_rec,
                hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                hHeadNe, SmtEval.native_not] using
                And.intro hNoMemErase hRec
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          simpa [__eo_list_erase_all_rec, eo_var_list_nodup]
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_nodup_setof_rec
    {xs : Term} (hVarList : eo_var_list xs) :
    eo_var_list_nodup (__eo_list_setof_rec xs) := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            let head := Term.Var (Term.String s) T
            have hHeadNe : head ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hSetTailVar :
                eo_var_list (__eo_list_setof_rec y) :=
              eo_var_list_setof_rec hTailVar
            have hEraseVar :
                eo_var_list
                  (__eo_list_erase_all_rec (__eo_list_setof_rec y) head) :=
              eo_var_list_erase_all_rec hSetTailVar hHeadNe
            have hEraseNe :
                __eo_list_erase_all_rec (__eo_list_setof_rec y) head ≠
                  Term.Stuck :=
              eo_var_list_ne_stuck hEraseVar
            have hNoMemHead :
                ¬ eo_var_list_mem head
                    (__eo_list_erase_all_rec (__eo_list_setof_rec y) head) :=
              eo_var_list_not_mem_erase_all_rec_self
                hSetTailVar hHeadNe
            have hNoDupTail :
                eo_var_list_nodup
                  (__eo_list_erase_all_rec (__eo_list_setof_rec y) head) :=
              eo_var_list_nodup_erase_all_rec hSetTailVar
                (ih hTailVar) hHeadNe
            simpa [head, eo_var_list_nodup, __eo_list_setof_rec,
              __eo_mk_apply, hEraseNe] using
              And.intro hNoMemHead hNoDupTail
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          trivial
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_nodup_setof
    {xs : Term} (hVarList : eo_var_list xs) :
    eo_var_list_nodup (__eo_list_setof Term.__eo_List_cons xs) := by
  have hList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hNoDupRec : eo_var_list_nodup (__eo_list_setof_rec xs) :=
    eo_var_list_nodup_setof_rec hVarList
  simpa [__eo_list_setof, hList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hNoDupRec

private theorem eo_var_list_not_mem_of_not_mem_erase_rec_ne
    {xs z e : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (he : e ≠ Term.Stuck)
    (hNe : z ≠ e)
    (hNotMemErase : ¬ eo_var_list_mem z (__eo_list_erase_rec xs e)) :
    ¬ eo_var_list_mem z xs := by
  intro hMem
  exact hNotMemErase
    (eo_var_list_mem_erase_rec_of_ne hVarList hz he hNe hMem)

private theorem eo_var_list_not_mem_of_mem_diff_rec
    {xs ys z : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys)
    (hNoDupXs : eo_var_list_nodup xs) (hz : z ≠ Term.Stuck)
    (hMem : eo_var_list_mem z (__eo_list_diff_rec xs ys)) :
    ¬ eo_var_list_mem z ys := by
  induction xs, ys using __eo_list_diff_rec.induct with
  | case1 ys =>
      exact False.elim hXsVar
  | case2 xs hYsStuck =>
      exact False.elim (eo_var_list_ne_stuck hYsVar rfl)
  | case3 f x y ys hYsNotStuck v0 ih =>
      cases f <;> try exact False.elim hXsVar
      case __eo_List_cons =>
        cases x <;> try exact False.elim hXsVar
        case Var name T =>
          cases name <;> try exact False.elim hXsVar
          case String s =>
            have hTailVar : eo_var_list y := hXsVar
            let head := Term.Var (Term.String s) T
            have hHeadNe : head ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hHeadNotTail : ¬ eo_var_list_mem head y :=
              hNoDupXs.1
            have hTailNoDup : eo_var_list_nodup y :=
              hNoDupXs.2
            have hEraseVar : eo_var_list (__eo_list_erase_rec ys head) :=
              eo_var_list_erase_rec hYsVar hHeadNe
            have hEraseNe : __eo_list_erase_rec ys head ≠ Term.Stuck :=
              eo_var_list_ne_stuck hEraseVar
            have hRecNe : __eo_list_diff_rec y v0 ≠ Term.Stuck :=
              eo_var_list_ne_stuck
                (eo_var_list_diff_rec hTailVar (by simpa [v0] using hEraseVar))
            by_cases hSame : __eo_list_erase_rec ys head = ys
            · have hv0 : v0 = ys := by
                simpa [v0] using hSame
              have hYsNe : ys ≠ Term.Stuck :=
                eo_var_list_ne_stuck hYsVar
              have hEqTerm : __eo_eq v0 ys = Term.Boolean true := by
                rw [hv0]
                exact eo_eq_true_of_eq_ne_stuck hYsNe
              have hMemCons :
                  head = z ∨ eo_var_list_mem z (__eo_list_diff_rec y v0) := by
                simpa [head, eo_var_list_mem, __eo_list_diff_rec, v0,
                  hEqTerm, __eo_prepend_if, hHeadNe, hRecNe] using hMem
              rcases hMemCons with hHead | hTail
              · subst z
                exact eo_var_list_not_mem_of_erase_rec_eq_self
                  hYsVar hHeadNe hSame
              · have hNotMem :
                  ¬ eo_var_list_mem z v0 :=
                  ih hTailVar (by simpa [v0] using hEraseVar)
                    hTailNoDup hTail
                simpa [hv0] using hNotMem
            · have hv0Ne : v0 ≠ ys := by
                simpa [v0] using hSame
              have hYsNe : ys ≠ Term.Stuck :=
                eo_var_list_ne_stuck hYsVar
              have hv0Stuck : v0 ≠ Term.Stuck := by
                simpa [v0] using hEraseNe
              have hEqTerm : __eo_eq v0 ys = Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hv0Ne hv0Stuck hYsNe
              have hTailMem :
                  eo_var_list_mem z (__eo_list_diff_rec y v0) := by
                simpa [__eo_list_diff_rec, v0, hEqTerm,
                  __eo_prepend_if, hRecNe] using hMem
              have hNotMemErase :
                  ¬ eo_var_list_mem z v0 :=
                ih hTailVar (by simpa [v0] using hEraseVar)
                  hTailNoDup hTailMem
              have hMemTailLeft :
                  eo_var_list_mem z y :=
                eo_var_list_mem_of_mem_diff_rec_left hTailVar
                  (by simpa [v0] using hEraseVar) hz hTailMem
              have hNeHead : z ≠ head := by
                intro hEq
                subst z
                exact hHeadNotTail hMemTailLeft
              exact
                eo_var_list_not_mem_of_not_mem_erase_rec_ne hYsVar hz
                  hHeadNe hNeHead (by simpa [v0] using hNotMemErase)
  | case4 nil ys hNil hYs hNotApply =>
      cases nil with
      | __eo_List_nil =>
          have hFalse : False := by
            simpa [__eo_list_diff_rec, eo_var_list_mem] using hMem
          exact False.elim hFalse
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApply g x a rfl)
          | _ =>
              exact False.elim hXsVar
      | _ =>
          exact False.elim hXsVar

private theorem eo_var_list_not_mem_of_mem_diff
    {xs ys z : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys)
    (hNoDupXs : eo_var_list_nodup xs) (hz : z ≠ Term.Stuck)
    (hMem :
      eo_var_list_mem z (__eo_list_diff Term.__eo_List_cons xs ys)) :
    ¬ eo_var_list_mem z ys := by
  have hXsList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hXsVar
  have hYsList : __eo_is_list Term.__eo_List_cons ys = Term.Boolean true :=
    eo_var_list_is_list hYsVar
  have hMemRec :
      eo_var_list_mem z (__eo_list_diff_rec xs ys) := by
    simpa [__eo_list_diff, hXsList, hYsList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hMem
  exact eo_var_list_not_mem_of_mem_diff_rec hXsVar hYsVar hNoDupXs hz hMemRec

private theorem eo_is_neg_list_find_cons_of_tail
    (x z xs : Term)
    (hx : x ≠ Term.Stuck) (hz : z ≠ Term.Stuck)
    (hTailVar : eo_var_list xs)
    (hTailFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs z) =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) z) =
      Term.Boolean false := by
  have hTailList :
      __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hTailVar
  have hWholeList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) =
        Term.Boolean true :=
    eo_is_list_cons_of_tail_list x xs hTailList
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hOne : native_zlt (1 : native_Int) 0 = false := by
    native_decide
  have hTailFindRec0 :
      __eo_is_neg
          (__eo_list_find_rec xs z (Term.Numeral 0)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hTailList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hTailFind
  have hTailMem :
      eo_var_list_mem z xs :=
    eo_var_list_mem_of_eo_is_neg_list_find_rec_false
      hTailVar hz 0 hZero hTailFindRec0
  have hTailFindRec1 :
      __eo_is_neg
          (__eo_list_find_rec xs z (Term.Numeral 1)) =
        Term.Boolean false :=
    eo_is_neg_list_find_rec_false_of_var_list_mem
      hTailVar hz hTailMem 1 hOne
  by_cases hEq : x = z
  · have hEqTerm : __eo_eq x z = Term.Boolean true := by
      subst z
      exact eo_eq_true_of_eq_ne_stuck hx
    simp [__eo_list_find, hWholeList, __eo_requires,
      __eo_list_find_rec, hEqTerm, __eo_ite,
      __eo_is_neg, native_ite, native_teq, native_not, SmtEval.native_not]
    native_decide
  · have hEqTerm : __eo_eq x z = Term.Boolean false :=
      eo_eq_false_of_ne_nonstuck hEq hx hz
    simpa [__eo_list_find, hWholeList, hTailList, __eo_requires,
      __eo_list_find_rec, hEqTerm, __eo_ite, native_ite,
      native_teq, native_not, SmtEval.native_not] using hTailFindRec1

private theorem eo_is_neg_list_find_erase_all_rec_of_ne
    {xs z e : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (he : e ≠ Term.Stuck)
    (hNe : z ≠ e)
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs z) =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_erase_all_rec xs e) z) =
      Term.Boolean false := by
  have hXsList :
      __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hEraseVar :
      eo_var_list (__eo_list_erase_all_rec xs e) :=
    eo_var_list_erase_all_rec hVarList he
  have hEraseList :
      __eo_is_list Term.__eo_List_cons
          (__eo_list_erase_all_rec xs e) =
        Term.Boolean true :=
    eo_var_list_is_list hEraseVar
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hFindRec0 :
      __eo_is_neg
          (__eo_list_find_rec xs z (Term.Numeral 0)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hXsList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hFind
  have hMem :
      eo_var_list_mem z xs :=
    eo_var_list_mem_of_eo_is_neg_list_find_rec_false
      hVarList hz 0 hZero hFindRec0
  have hEraseMem :
      eo_var_list_mem z (__eo_list_erase_all_rec xs e) :=
    eo_var_list_mem_erase_all_rec_of_ne hVarList hz he hNe hMem
  have hFindEraseRec :
      __eo_is_neg
          (__eo_list_find_rec (__eo_list_erase_all_rec xs e) z
            (Term.Numeral 0)) =
        Term.Boolean false :=
    eo_is_neg_list_find_rec_false_of_var_list_mem
      hEraseVar hz hEraseMem 0 hZero
  simpa [__eo_list_find, hEraseList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hFindEraseRec

private theorem eo_is_neg_list_find_cons_var_of_tail
    (s s' : native_String) (T T' xs : Term)
    (hTailVar : eo_var_list xs)
    (hTailFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T)) =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s') T')) xs)
          (Term.Var (Term.String s) T)) =
      Term.Boolean false := by
  have hTailList :
      __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hTailVar
  have hWholeList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s') T')) xs) =
        Term.Boolean true :=
    eo_is_list_cons_of_tail_list (Term.Var (Term.String s') T') xs
      hTailList
  have hz : Term.Var (Term.String s) T ≠ Term.Stuck :=
    term_var_string_ne_stuck s T
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hOne : native_zlt (1 : native_Int) 0 = false := by
    native_decide
  have hTailFindRec0 :
      __eo_is_neg
          (__eo_list_find_rec xs (Term.Var (Term.String s) T)
            (Term.Numeral 0)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hTailList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hTailFind
  have hTailMem :
      eo_var_list_mem (Term.Var (Term.String s) T) xs :=
    eo_var_list_mem_of_eo_is_neg_list_find_rec_false
      hTailVar hz 0 hZero hTailFindRec0
  have hTailFindRec1 :
      __eo_is_neg
          (__eo_list_find_rec xs (Term.Var (Term.String s) T)
            (Term.Numeral 1)) =
        Term.Boolean false :=
    eo_is_neg_list_find_rec_false_of_var_list_mem
      hTailVar hz hTailMem 1 hOne
  by_cases hEq :
      Term.Var (Term.String s') T' = Term.Var (Term.String s) T
  · have hEqTerm :
        __eo_eq (Term.Var (Term.String s') T')
            (Term.Var (Term.String s) T) =
          Term.Boolean true := by
      rw [hEq]
      exact eo_eq_var_string_true s T
    simp [__eo_list_find, hWholeList, __eo_requires,
      __eo_list_find_rec, hEqTerm, __eo_ite,
      __eo_is_neg, native_ite, native_teq, native_not, SmtEval.native_not]
    native_decide
  · have hEqTerm :
        __eo_eq (Term.Var (Term.String s') T')
            (Term.Var (Term.String s) T) =
          Term.Boolean false :=
      eo_eq_var_string_false_of_ne hEq
    simpa [__eo_list_find, hWholeList, hTailList, __eo_requires,
      __eo_list_find_rec, hEqTerm, __eo_ite, native_ite,
      native_teq, native_not, SmtEval.native_not] using hTailFindRec1

private theorem eo_is_neg_list_find_tail_of_cons_var_ne
    (s s' : native_String) (T T' xs : Term)
    (hTailVar : eo_var_list xs)
    (hNe :
      Term.Var (Term.String s) T ≠
        Term.Var (Term.String s') T')
    (hFindCons :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) xs)
            (Term.Var (Term.String s') T')) =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons xs
          (Term.Var (Term.String s') T')) =
      Term.Boolean false := by
  have hTailList :
      __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hTailVar
  have hWholeList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs) =
        Term.Boolean true :=
    eo_is_list_cons_of_tail_list (Term.Var (Term.String s) T) xs
      hTailList
  have hHeadNe :
      Term.Var (Term.String s) T ≠ Term.Stuck :=
    term_var_string_ne_stuck s T
  have hTargetNe :
      Term.Var (Term.String s') T' ≠ Term.Stuck :=
    term_var_string_ne_stuck s' T'
  have hEqTerm :
      __eo_eq (Term.Var (Term.String s) T)
          (Term.Var (Term.String s') T') =
        Term.Boolean false :=
    eo_eq_var_string_false_of_ne hNe
  have hTailFindRec1 :
      __eo_is_neg
          (__eo_list_find_rec xs (Term.Var (Term.String s') T')
            (Term.Numeral 1)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hWholeList, hTailList, __eo_requires,
      __eo_list_find_rec, hEqTerm, __eo_ite, native_ite,
      native_teq, native_not, SmtEval.native_not] using hFindCons
  have hOne : native_zlt (1 : native_Int) 0 = false := by
    native_decide
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hTailMem :
      eo_var_list_mem (Term.Var (Term.String s') T') xs :=
    eo_var_list_mem_of_eo_is_neg_list_find_rec_false
      hTailVar hTargetNe 1 hOne hTailFindRec1
  have hTailFindRec0 :
      __eo_is_neg
          (__eo_list_find_rec xs (Term.Var (Term.String s') T')
            (Term.Numeral 0)) =
        Term.Boolean false :=
    eo_is_neg_list_find_rec_false_of_var_list_mem
      hTailVar hTargetNe hTailMem 0 hZero
  simpa [__eo_list_find, hTailList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hTailFindRec0

private theorem eo_is_neg_list_find_setof_rec_of_var_list_mem
    {xs z : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (hMem : eo_var_list_mem z xs) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_setof_rec xs) z) =
      Term.Boolean false := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            let head := Term.Var (Term.String s) T
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe : head ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hSetTailVar :
                eo_var_list (__eo_list_setof_rec y) :=
              eo_var_list_setof_rec hTailVar
            have hEraseVar :
                eo_var_list
                  (__eo_list_erase_all_rec (__eo_list_setof_rec y) head) :=
              eo_var_list_erase_all_rec hSetTailVar hHeadNe
            have hEraseNe :
                __eo_list_erase_all_rec (__eo_list_setof_rec y) head ≠
                  Term.Stuck :=
              eo_var_list_ne_stuck hEraseVar
            rcases hMem with hHead | hTail
            · subst z
              have hEqTerm : __eo_eq head head = Term.Boolean true :=
                eo_eq_true_of_eq_ne_stuck hHeadNe
              have hConsList :
                  __eo_is_list Term.__eo_List_cons
                      (Term.Apply (Term.Apply Term.__eo_List_cons head)
                        (__eo_list_erase_all_rec (__eo_list_setof_rec y)
                          head)) =
                    Term.Boolean true :=
                eo_is_list_cons_of_tail_list head
                  (__eo_list_erase_all_rec (__eo_list_setof_rec y) head)
                  (eo_var_list_is_list hEraseVar)
              simp [head, __eo_list_setof_rec, __eo_mk_apply, hEraseNe,
                __eo_list_find, hConsList, __eo_requires,
                __eo_list_find_rec, hEqTerm, __eo_ite, __eo_is_neg,
                native_ite, native_teq, native_not, SmtEval.native_not]
              native_decide
            · by_cases hEq : head = z
              · subst z
                have hEqTerm : __eo_eq head head = Term.Boolean true :=
                  eo_eq_true_of_eq_ne_stuck hHeadNe
                have hConsList :
                    __eo_is_list Term.__eo_List_cons
                        (Term.Apply (Term.Apply Term.__eo_List_cons head)
                          (__eo_list_erase_all_rec (__eo_list_setof_rec y)
                            head)) =
                      Term.Boolean true :=
                  eo_is_list_cons_of_tail_list head
                    (__eo_list_erase_all_rec (__eo_list_setof_rec y) head)
                    (eo_var_list_is_list hEraseVar)
                simp [head, __eo_list_setof_rec, __eo_mk_apply, hEraseNe,
                  __eo_list_find, hConsList, __eo_requires,
                  __eo_list_find_rec, hEqTerm, __eo_ite, __eo_is_neg,
                  native_ite, native_teq, native_not, SmtEval.native_not]
                native_decide
              · have hZHead : z ≠ head := by
                  intro hZH
                  exact hEq hZH.symm
                have hTailFind :
                    __eo_is_neg
                        (__eo_list_find Term.__eo_List_cons
                          (__eo_list_setof_rec y) z) =
                      Term.Boolean false :=
                  ih hTailVar hTail
                have hTailFindErase :
                    __eo_is_neg
                        (__eo_list_find Term.__eo_List_cons
                          (__eo_list_erase_all_rec
                            (__eo_list_setof_rec y) head) z) =
                      Term.Boolean false :=
                  eo_is_neg_list_find_erase_all_rec_of_ne
                    hSetTailVar hz hHeadNe hZHead hTailFind
                have hConsFind :
                    __eo_is_neg
                        (__eo_list_find Term.__eo_List_cons
                          (Term.Apply (Term.Apply Term.__eo_List_cons head)
                            (__eo_list_erase_all_rec
                              (__eo_list_setof_rec y) head)) z) =
                      Term.Boolean false :=
                  eo_is_neg_list_find_cons_of_tail head z
                    (__eo_list_erase_all_rec (__eo_list_setof_rec y) head)
                    hHeadNe hz hEraseVar hTailFindErase
                simpa [head, __eo_list_setof_rec, __eo_mk_apply,
                  hEraseNe] using hConsFind
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          exact False.elim hMem
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_is_neg_list_find_setof_of_var_list_mem
    {xs z : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (hMem : eo_var_list_mem z xs) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons xs) z) =
      Term.Boolean false := by
  have hList :
      __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hFind :=
    eo_is_neg_list_find_setof_rec_of_var_list_mem
      hVarList hz hMem
  simpa [__eo_list_setof, hList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hFind

private theorem eo_var_list_mem_setof_of_mem
    {xs z : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (hMem : eo_var_list_mem z xs) :
    eo_var_list_mem z (__eo_list_setof Term.__eo_List_cons xs) := by
  have hSetVar :
      eo_var_list (__eo_list_setof Term.__eo_List_cons xs) :=
    eo_var_list_setof hVarList
  have hSetList :
      __eo_is_list Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons xs) =
        Term.Boolean true :=
    eo_var_list_is_list hSetVar
  have hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons xs) z) =
        Term.Boolean false :=
    eo_is_neg_list_find_setof_of_var_list_mem hVarList hz hMem
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hFindRec :
      __eo_is_neg
          (__eo_list_find_rec
            (__eo_list_setof Term.__eo_List_cons xs) z
            (Term.Numeral 0)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hSetList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hFind
  exact eo_var_list_mem_of_eo_is_neg_list_find_rec_false
    hSetVar hz 0 hZero hFindRec

private theorem eo_is_neg_list_find_setof_cons_head
    (s : native_String) (T xs : Term)
    (hTailVar : eo_var_list xs) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) xs))
          (Term.Var (Term.String s) T)) =
      Term.Boolean false := by
  have hWholeList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs) =
        Term.Boolean true :=
    eo_is_list_cons_of_tail_list (Term.Var (Term.String s) T) xs
      (eo_var_list_is_list hTailVar)
  have hWholeVar :
      eo_var_list
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) xs) := hTailVar
  have hSetList :
      __eo_is_list Term.__eo_List_cons
          (__eo_list_setof_rec
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) xs)) =
        Term.Boolean true :=
    eo_list_setof_rec_is_list_of_var_list hWholeVar
  have hSetTailList :
      __eo_is_list Term.__eo_List_cons
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs)
            (Term.Var (Term.String s) T)) =
        Term.Boolean true :=
    eo_list_erase_all_rec_is_list_of_var_list
      (eo_var_list_setof_rec hTailVar) (term_var_string_ne_stuck s T)
  have hSetTailNe :
      __eo_list_erase_all_rec (__eo_list_setof_rec xs)
          (Term.Var (Term.String s) T) ≠ Term.Stuck :=
    term_ne_stuck_of_eo_is_list_true hSetTailList
  have hConsSetList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply
            (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
            (__eo_list_erase_all_rec (__eo_list_setof_rec xs)
              (Term.Var (Term.String s) T))) =
        Term.Boolean true := by
    simpa [__eo_list_setof_rec, __eo_mk_apply, hSetTailNe] using hSetList
  rw [__eo_list_setof]
  simp [hWholeList, __eo_requires, native_ite, native_teq, native_not]
  rw [__eo_list_setof_rec]
  simp [__eo_mk_apply, hSetTailNe, __eo_list_find, hConsSetList,
    hSetTailList, __eo_requires, __eo_list_find_rec, __eo_eq, __eo_ite,
    __eo_is_neg, native_ite, native_teq, native_not, SmtEval.native_not]
  native_decide

private theorem eo_to_smt_type_eq_self_of_wf
    {T U : Term}
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTy : __eo_to_smt_type U = __eo_to_smt_type T) :
    U = T := by
  have hByRec :
      ∀ {A : SmtType},
        __eo_to_smt_type T = A ->
          __smtx_type_wf_rec A native_reflist_nil = true ->
            U = T := by
    intro A hTA hRec
    have hU : __eo_to_smt_type U = A := hTy.trans hTA
    have hField :
        TranslationProofs.smtx_type_field_wf_rec A native_reflist_nil :=
      TranslationProofs.smtx_type_field_wf_rec_of_type_wf_rec hRec
    exact TranslationProofs.eo_to_smt_type_injective_of_field_wf_rec
      (T := U) (U := T) (A := A) hU hTA hField
  cases hA : __eo_to_smt_type T with
  | RegLan =>
      have hU : U = Term.UOp UserOp.RegLan :=
        TranslationProofs.eo_to_smt_type_eq_reglan (by
          simpa [hA] using hTy)
      have hT : T = Term.UOp UserOp.RegLan :=
        TranslationProofs.eo_to_smt_type_eq_reglan hA
      rw [hU, hT]
  | FunType A B =>
      have hWF' : __smtx_type_wf (SmtType.FunType A B) = true := by
        simpa [hA] using hWF
      rcases TranslationProofs.fun_type_wf_rec_components_of_wf hWF' with
        ⟨hARec, hBRec⟩
      have hAField :
          TranslationProofs.smtx_type_field_wf_rec A native_reflist_nil :=
        TranslationProofs.smtx_type_field_wf_rec_of_type_wf_rec hARec
      have hBField :
          TranslationProofs.smtx_type_field_wf_rec B native_reflist_nil :=
        TranslationProofs.smtx_type_field_wf_rec_of_type_wf_rec hBRec
      have hUFun : __eo_to_smt_type U = SmtType.FunType A B := by
        simpa [hA] using hTy
      rcases TranslationProofs.eo_to_smt_type_eq_fun hA with
        ⟨T1, T2, hTShape, hT1, hT2⟩
      rcases TranslationProofs.eo_to_smt_type_eq_fun hUFun with
        ⟨U1, U2, hUShape, hU1, hU2⟩
      subst T
      subst U
      have h1 : U1 = T1 :=
        TranslationProofs.eo_to_smt_type_injective_of_field_wf_rec
          (T := U1) (U := T1) (A := A)
          hU1 hT1 hAField
      have h2 : U2 = T2 :=
        TranslationProofs.eo_to_smt_type_injective_of_field_wf_rec
          (T := U2) (U := T2) (A := B)
          hU2 hT2 hBField
      subst U1
      subst U2
      rfl
  | None =>
      simp [hA, __smtx_type_wf, __smtx_type_wf_component,
        __smtx_type_wf_rec, native_inhabited_type, native_and] at hWF
  | TypeRef s =>
      simp [hA, __smtx_type_wf, __smtx_type_wf_component,
        __smtx_type_wf_rec, native_inhabited_type, native_and] at hWF
  | DtcAppType A B =>
      simp [hA, __smtx_type_wf, __smtx_type_wf_component,
        __smtx_type_wf_rec, native_inhabited_type, native_and] at hWF
  | Bool =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | Int =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | Real =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | BitVec w =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | Char =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | Datatype s d =>
      have hParts :
          (__smtx_typeof_value
                (__smtx_type_default (SmtType.Datatype s d)) =
              SmtType.Datatype s d ∧
            __smtx_value_canonical_bool
                (__smtx_type_default (SmtType.Datatype s d)) =
              true) ∧
            __smtx_type_wf_rec (SmtType.Datatype s d)
                native_reflist_nil =
              true := by
        simpa [hA, __smtx_type_wf, __smtx_type_wf_component,
          native_inhabited_type, native_and] using hWF
      exact hByRec hA hParts.2
  | USort i =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | Seq A =>
      have hParts :
          (__smtx_typeof_value (__smtx_type_default (SmtType.Seq A)) =
              SmtType.Seq A ∧
            __smtx_value_canonical_bool
                (__smtx_type_default (SmtType.Seq A)) =
              true) ∧
            __smtx_type_wf_rec (SmtType.Seq A) native_reflist_nil =
              true := by
        simpa [hA, __smtx_type_wf, __smtx_type_wf_component,
          native_inhabited_type, native_and] using hWF
      exact hByRec hA hParts.2
  | Map A B =>
      have hParts :
          (__smtx_typeof_value (__smtx_type_default (SmtType.Map A B)) =
              SmtType.Map A B ∧
            __smtx_value_canonical_bool
                (__smtx_type_default (SmtType.Map A B)) =
              true) ∧
            __smtx_type_wf_rec (SmtType.Map A B) native_reflist_nil =
              true := by
        simpa [hA, __smtx_type_wf, __smtx_type_wf_component,
          native_inhabited_type, native_and] using hWF
      exact hByRec hA hParts.2
  | Set A =>
      have hParts :
          (__smtx_typeof_value (__smtx_type_default (SmtType.Set A)) =
              SmtType.Set A ∧
            __smtx_value_canonical_bool
                (__smtx_type_default (SmtType.Set A)) =
              true) ∧
            __smtx_type_wf_rec (SmtType.Set A) native_reflist_nil =
              true := by
        simpa [hA, __smtx_type_wf, __smtx_type_wf_component,
          native_inhabited_type, native_and] using hWF
      exact hByRec hA hParts.2

private theorem eo_is_neg_list_find_setof_cons_head_same_smt_type
    (s : native_String) (T T' xs : Term)
    (hTailVar : eo_var_list xs)
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTy : __eo_to_smt_type T' = __eo_to_smt_type T) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) xs))
          (Term.Var (Term.String s) T')) =
      Term.Boolean false := by
  have hT' : T' = T := eo_to_smt_type_eq_self_of_wf hWF hTy
  subst T'
  exact eo_is_neg_list_find_setof_cons_head s T xs hTailVar

private theorem scannerModelRel_push_nil_of_xs_hit
    (xs : Term) (M : SmtModel) (s : native_String) (T : Term)
    (v : SmtValue)
    (hHit :
      ∀ T',
        __eo_to_smt_type T' = __eo_to_smt_type T ->
          __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T')) = Term.Boolean false) :
    scannerModelRel xs Term.__eo_List_nil M
      (native_model_push M s (__eo_to_smt_type T) v) := by
  refine ⟨?_, ?_⟩
  · exact
      ⟨by
        intro s' U
        simp [native_model_lookup, native_model_key, native_model_push],
      by
        intro fid U V
        simp [native_model_fun_lookup, native_model_key, native_model_push]⟩
  · intro s' T' hAllowed
    by_cases hKey :
        ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
          SmtModelKey) =
          { isVar := true, name := s, ty := __eo_to_smt_type T }
    · have hAllowedSame :
          __eo_ite
              (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s') T')))
              (Term.Boolean false)
              (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons Term.__eo_List_nil
                  (Term.Var (Term.String s') T'))) =
            Term.Boolean false := by
        exact hAllowed
      have hName : s' = s := congrArg SmtModelKey.name hKey
      have hTy : __eo_to_smt_type T' = __eo_to_smt_type T :=
        congrArg SmtModelKey.ty hKey
      subst s'
      rw [hHit T' hTy, eo_is_neg_list_find_nil_var] at hAllowedSame
      simp [__eo_ite, native_ite, native_teq] at hAllowedSame
    · simpa [native_model_var_lookup, native_model_push, hKey]

private theorem scannerModelRel_push_of_xs_hit_bvs_miss
    (xs bvs : Term) (M : SmtModel) (s : native_String) (T : Term)
    (v : SmtValue)
    (hHit :
      ∀ T',
        __eo_to_smt_type T' = __eo_to_smt_type T ->
          __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T')) = Term.Boolean false)
    (hMiss :
      ∀ T',
        __eo_to_smt_type T' = __eo_to_smt_type T ->
          __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs
            (Term.Var (Term.String s) T')) = Term.Boolean true) :
    scannerModelRel xs bvs M
      (native_model_push M s (__eo_to_smt_type T) v) := by
  refine ⟨?_, ?_⟩
  · exact
      ⟨by
        intro s' U
        simp [native_model_lookup, native_model_key, native_model_push],
      by
        intro fid U V
        simp [native_model_fun_lookup, native_model_key, native_model_push]⟩
  · intro s' T' hAllowed
    by_cases hKey :
        ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
          SmtModelKey) =
          { isVar := true, name := s, ty := __eo_to_smt_type T }
    · have hName : s' = s := congrArg SmtModelKey.name hKey
      have hTy : __eo_to_smt_type T' = __eo_to_smt_type T :=
        congrArg SmtModelKey.ty hKey
      subst s'
      rw [hHit T' hTy, hMiss T' hTy] at hAllowed
      simp [__eo_ite, native_ite, native_teq] at hAllowed
    · simpa [native_model_var_lookup, native_model_push, hKey]

private theorem scannerModelRel_push_nil_of_setof_cons_head
    (M : SmtModel) (s : native_String) (T xs : Term) (v : SmtValue)
    (hTailVar : eo_var_list xs)
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true) :
    scannerModelRel
      (__eo_list_setof Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) xs))
      Term.__eo_List_nil M
      (native_model_push M s (__eo_to_smt_type T) v) := by
  exact scannerModelRel_push_nil_of_xs_hit
    (__eo_list_setof Term.__eo_List_cons
      (Term.Apply (Term.Apply Term.__eo_List_cons
        (Term.Var (Term.String s) T)) xs))
    M s T v
    (fun T' hTy =>
      eo_is_neg_list_find_setof_cons_head_same_smt_type
        s T T' xs hTailVar hWF hTy)

private theorem scannerModelRel_push_nil_of_setof_mem
    (M : SmtModel) (s : native_String) (T xs : Term) (v : SmtValue)
    (hVarList : eo_var_list xs)
    (hMem : eo_var_list_mem (Term.Var (Term.String s) T) xs)
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true) :
    scannerModelRel
      (__eo_list_setof Term.__eo_List_cons xs)
      Term.__eo_List_nil M
      (native_model_push M s (__eo_to_smt_type T) v) := by
  exact scannerModelRel_push_nil_of_xs_hit
    (__eo_list_setof Term.__eo_List_cons xs) M s T v
    (fun T' hTy => by
      have hT' : T' = T := eo_to_smt_type_eq_self_of_wf hWF hTy
      subst T'
      exact eo_is_neg_list_find_setof_of_var_list_mem
        hVarList (term_var_string_ne_stuck s T) hMem)

private theorem scannerModelRel_push_same_cons_var
    (xs bvs : Term) (M N : SmtModel)
    (s : native_String) (T : Term) (v : SmtValue)
    (hBvsVar : eo_var_list bvs)
    (hRel : scannerModelRel xs bvs M N) :
    scannerModelRel xs
      (Term.Apply (Term.Apply Term.__eo_List_cons
        (Term.Var (Term.String s) T)) bvs)
      (native_model_push M s (__eo_to_smt_type T) v)
      (native_model_push N s (__eo_to_smt_type T) v) := by
  refine ⟨model_agrees_on_globals_push₂ hRel.globals, ?_⟩
  intro s' T' hAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
        SmtModelKey) =
        { isVar := true, name := s, ty := __eo_to_smt_type T }
  · simpa [native_model_var_lookup, native_model_push, hKey]
  · have hOldAllowed :
        __eo_ite
            (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s') T')))
            (Term.Boolean false)
            (__eo_is_neg (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s') T'))) =
          Term.Boolean false := by
      rcases eo_ite_false_branch_eq_false_cases
          (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s') T')))
          (__eo_is_neg
            (__eo_list_find Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) bvs)
              (Term.Var (Term.String s') T'))) hAllowed with
        hXsMiss | ⟨hXsHit, hBvsNewHit⟩
      · simp [__eo_ite, hXsMiss, native_ite, native_teq]
      · have hTermNe :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s') T' := by
          intro hTerm
          cases hTerm
          exact hKey rfl
        have hBvsHit :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s') T')) =
              Term.Boolean false :=
          eo_is_neg_list_find_tail_of_cons_var_ne
            s s' T T' bvs hBvsVar hTermNe hBvsNewHit
        simp [__eo_ite, hXsHit, hBvsHit, native_ite, native_teq]
    simpa [native_model_var_lookup, native_model_push, hKey]
      using hRel.vars_eq s' T' hOldAllowed

private theorem smtx_model_eval_eo_to_smt_exists_eq_of_scanner_body
    (body : SmtTerm) {binders : Term} {vars : List SmtVarKey}
    (hBinders : EoSmtVarEnv binders vars) :
    ∀ {xs bvs : Term} {M N : SmtModel},
      eo_var_list bvs ->
        scannerModelRel xs bvs M N ->
          (∀ M' N' : SmtModel,
            scannerModelRel xs (__eo_list_concat_rec binders bvs) M' N' ->
              __smtx_model_eval M' body =
                __smtx_model_eval N' body) ->
            __smtx_model_eval M (__eo_to_smt_exists binders body) =
              __smtx_model_eval N (__eo_to_smt_exists binders body) := by
  induction hBinders with
  | nil =>
      intro xs bvs M N hBvsVar hRel hBody
      have hBvsNe : bvs ≠ Term.Stuck := eo_var_list_ne_stuck hBvsVar
      have hRelBody :
          scannerModelRel xs (__eo_list_concat_rec Term.__eo_List_nil bvs)
            M N := by
        simpa [eo_list_concat_rec_nil_left_of_ne hBvsNe] using hRel
      simpa [__eo_to_smt_exists] using hBody M N hRelBody
  | cons hTail ih =>
      intro xs bvs M N hBvsVar hRel hBody
      rename_i s T tail varsTail
      have hTailVar : eo_var_list tail := eo_var_list_of_env hTail
      have hConsBvsVar :
          eo_var_list
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) bvs) := by
        simpa [eo_var_list] using hBvsVar
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail body)) =
          __smtx_model_eval N
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail body))
      exact smtx_model_eval_exists_eq_of_body_eval_eq
        (fun v =>
          ih (xs := xs)
            (bvs := Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) bvs)
            (M := native_model_push M s (__eo_to_smt_type T) v)
            (N := native_model_push N s (__eo_to_smt_type T) v)
            hConsBvsVar
            (scannerModelRel_push_same_cons_var
              xs bvs M N s T v hBvsVar hRel)
            (fun M' N' hRelTail =>
              hBody M' N'
                (scannerModelRel_concat_rec_cons_comm_symm
                  xs tail bvs M' N' s T hTailVar hBvsVar hRelTail)))

private theorem nativeEvalTChoiceNthAux_eq_of_scanner_body_cons
    (body : SmtTerm) (s : native_String) (T tail : Term)
    {varsTail : List SmtVarKey}
    (hTail : EoSmtVarEnv tail varsTail)
    (hBodyNoExists : ∀ s T F, body ≠ SmtTerm.exists s T F) :
    ∀ (n : native_Nat) {xs bvs : Term} {M N : SmtModel},
      eo_var_list bvs ->
        scannerModelRel xs bvs M N ->
          (∀ M' N' : SmtModel,
            scannerModelRel xs
                (__eo_list_concat_rec
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) tail)
                  bvs)
                M' N' ->
              __smtx_model_eval M' body =
                __smtx_model_eval N' body) ->
            nativeEvalTChoiceNthAux M s (__eo_to_smt_type T)
                (__eo_to_smt_exists tail body) n =
              nativeEvalTChoiceNthAux N s (__eo_to_smt_type T)
                (__eo_to_smt_exists tail body) n := by
  intro n
  induction n generalizing s T tail varsTail with
  | zero =>
      intro xs bvs M N hBvsVar hRel hBody
      have hTailVar : eo_var_list tail := eo_var_list_of_env hTail
      have hConsBvsVar :
          eo_var_list
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) bvs) := by
        simpa [eo_var_list] using hBvsVar
      simp [nativeEvalTChoiceNthAux]
      exact native_eval_tchoice_eq_of_body_eval_eq
        (fun v =>
          smtx_model_eval_eo_to_smt_exists_eq_of_scanner_body
            body hTail hConsBvsVar
            (scannerModelRel_push_same_cons_var
              xs bvs M N s T v hBvsVar hRel)
            (fun M' N' hRelTail =>
              hBody M' N'
                (scannerModelRel_concat_rec_cons_comm_symm
                  xs tail bvs M' N' s T hTailVar hBvsVar hRelTail)))
  | succ n ih =>
      intro xs bvs M N hBvsVar hRel hBody
      have hTailVar : eo_var_list tail := eo_var_list_of_env hTail
      have hConsBvsVar :
          eo_var_list
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) bvs) := by
        simpa [eo_var_list] using hBvsVar
      have hChoiceEq :
          native_eval_tchoice M s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail body) =
            native_eval_tchoice N s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail body) :=
        native_eval_tchoice_eq_of_body_eval_eq
          (fun v =>
            smtx_model_eval_eo_to_smt_exists_eq_of_scanner_body
              body hTail hConsBvsVar
              (scannerModelRel_push_same_cons_var
                xs bvs M N s T v hBvsVar hRel)
              (fun M' N' hRelTail =>
                hBody M' N'
                  (scannerModelRel_concat_rec_cons_comm_symm
                    xs tail bvs M' N' s T hTailVar hBvsVar hRelTail)))
      cases hTail with
      | nil =>
          cases body <;>
            simp [__eo_to_smt_exists, nativeEvalTChoiceNthAux]
          case «exists» s' T' body' =>
            exact False.elim (hBodyNoExists s' T' body' rfl)
      | cons hTailTail =>
          rename_i s' T' tail' varsTail'
          have hRelPush :
              scannerModelRel xs
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) bvs)
                (native_model_push M s (__eo_to_smt_type T)
                  (native_eval_tchoice N s (__eo_to_smt_type T)
                    (SmtTerm.exists s' (__eo_to_smt_type T')
                      (__eo_to_smt_exists tail' body))))
                (native_model_push N s (__eo_to_smt_type T)
                  (native_eval_tchoice N s (__eo_to_smt_type T)
                    (SmtTerm.exists s' (__eo_to_smt_type T')
                      (__eo_to_smt_exists tail' body)))) :=
            scannerModelRel_push_same_cons_var
              xs bvs M N s T
              (native_eval_tchoice N s (__eo_to_smt_type T)
                (SmtTerm.exists s' (__eo_to_smt_type T')
                  (__eo_to_smt_exists tail' body)))
              hBvsVar hRel
          have hTailEval :=
            ih (s := s') (T := T') (tail := tail')
              (varsTail := varsTail') hTailTail
              (xs := xs)
              (bvs := Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) bvs)
              (M := native_model_push M s (__eo_to_smt_type T)
                (native_eval_tchoice N s (__eo_to_smt_type T)
                  (SmtTerm.exists s' (__eo_to_smt_type T')
                    (__eo_to_smt_exists tail' body))))
              (N := native_model_push N s (__eo_to_smt_type T)
                (native_eval_tchoice N s (__eo_to_smt_type T)
                  (SmtTerm.exists s' (__eo_to_smt_type T')
                    (__eo_to_smt_exists tail' body))))
              hConsBvsVar hRelPush
              (fun M' N' hRelTail =>
                hBody M' N'
                  (scannerModelRel_concat_rec_cons_comm_symm
                    xs
                    (Term.Apply (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s') T')) tail')
                    bvs M' N' s T hTailVar hBvsVar hRelTail))
          change
            nativeEvalTChoiceNthAux
                (native_model_push M s (__eo_to_smt_type T)
                  (native_eval_tchoice M s (__eo_to_smt_type T)
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s') T')) tail')
                      body)))
                s' (__eo_to_smt_type T') (__eo_to_smt_exists tail' body) n =
              nativeEvalTChoiceNthAux
                (native_model_push N s (__eo_to_smt_type T)
                  (native_eval_tchoice N s (__eo_to_smt_type T)
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s') T')) tail')
                      body)))
                s' (__eo_to_smt_type T') (__eo_to_smt_exists tail' body) n
          rw [hChoiceEq]
          exact hTailEval

private theorem smtx_model_eval_eo_to_smt_quantifiers_skolemize_eq_of_scanner_body
    (body : SmtTerm) {binders : Term} {vars : List SmtVarKey}
    (hBinders : EoSmtVarEnv binders vars)
    (hBodyNoExists : ∀ s T F, body ≠ SmtTerm.exists s T F) :
    ∀ (n : native_Nat) {xs bvs : Term} {M N : SmtModel},
      eo_var_list bvs ->
        scannerModelRel xs bvs M N ->
          (∀ M' N' : SmtModel,
            scannerModelRel xs (__eo_list_concat_rec binders bvs)
              M' N' ->
              __smtx_model_eval M' body =
                __smtx_model_eval N' body) ->
            __smtx_model_eval M
                (__eo_to_smt_quantifiers_skolemize
                  (__eo_to_smt_exists binders body) n) =
              __smtx_model_eval N
                (__eo_to_smt_quantifiers_skolemize
                  (__eo_to_smt_exists binders body) n) := by
  intro n xs bvs M N hBvsVar hRel hBody
  cases hBinders with
  | nil =>
      cases body <;>
        simp [__eo_to_smt_exists, __eo_to_smt_quantifiers_skolemize,
          __smtx_model_eval]
      case «exists» s T body =>
        exact False.elim (hBodyNoExists s T body rfl)
  | cons hTail =>
      rename_i s T tail varsTail
      change
        __smtx_model_eval M
            (SmtTerm.choice_nth s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail body) n) =
          __smtx_model_eval N
            (SmtTerm.choice_nth s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail body) n)
      rw [smtx_model_eval_choice_nth_eq_aux M s (__eo_to_smt_type T)
          (__eo_to_smt_exists tail body) n,
        smtx_model_eval_choice_nth_eq_aux N s (__eo_to_smt_type T)
          (__eo_to_smt_exists tail body) n]
      exact nativeEvalTChoiceNthAux_eq_of_scanner_body_cons
        body s T tail hTail hBodyNoExists n hBvsVar hRel hBody

private theorem body_constant_on_eo_binders_of_scanner_eval_aux
    (body : SmtTerm) (xs bvs binders : Term) {vars : List SmtVarKey}
    (hBinders : EoSmtVarEnv binders vars)
    (hHit :
      ∀ (s : native_String) (T : Term),
        eo_var_list_mem (Term.Var (Term.String s) T) binders ->
          ∀ T',
            __eo_to_smt_type T' = __eo_to_smt_type T ->
              __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) T')) = Term.Boolean false)
    (hMiss :
      ∀ (s : native_String) (T : Term),
        eo_var_list_mem (Term.Var (Term.String s) T) binders ->
          ∀ T',
            __eo_to_smt_type T' = __eo_to_smt_type T ->
              __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs
                (Term.Var (Term.String s) T')) = Term.Boolean true)
    (hEval :
      ∀ M N : SmtModel,
        scannerModelRel xs bvs M N ->
          __smtx_model_eval M body =
            __smtx_model_eval N body) :
    body_constant_on_eo_binders body binders := by
  induction hBinders with
  | nil =>
      trivial
  | cons hTail ih =>
      rename_i s T tail varsTail
      have hHeadMem :
          eo_var_list_mem (Term.Var (Term.String s) T)
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) tail) := by
        exact Or.inl rfl
      constructor
      · intro M v _hvTy _hvCan
        exact
          (hEval M (native_model_push M s (__eo_to_smt_type T) v)
            (scannerModelRel_push_of_xs_hit_bvs_miss
              xs bvs M s T v
              (hHit s T hHeadMem)
              (hMiss s T hHeadMem))).symm
      · apply ih
        · intro s' T' hMemTail
          exact hHit s' T' (Or.inr hMemTail)
        · intro s' T' hMemTail
          exact hMiss s' T' (Or.inr hMemTail)

private theorem body_constant_on_eo_binders_of_scan_setof_aux
    (F orig binders : Term) {vars : List SmtVarKey}
    (hOrigVar : eo_var_list orig)
    (hBinders : EoSmtVarEnv binders vars)
    (hMemOrig :
      ∀ (s : native_String) (T : Term),
        eo_var_list_mem (Term.Var (Term.String s) T) binders ->
          eo_var_list_mem (Term.Var (Term.String s) T) orig)
    (hWf :
      ∀ (s : native_String) (T : Term),
        eo_var_list_mem (Term.Var (Term.String s) T) binders ->
          __smtx_type_wf (__eo_to_smt_type T) = true)
    (hEval :
      ∀ M N : SmtModel,
        scannerModelRel (__eo_list_setof Term.__eo_List_cons orig)
          Term.__eo_List_nil M N ->
          __smtx_model_eval M (__eo_to_smt F) =
            __smtx_model_eval N (__eo_to_smt F)) :
    body_constant_on_eo_binders (__eo_to_smt F) binders := by
  induction hBinders with
  | nil =>
      trivial
  | cons hTail ih =>
      rename_i s T tail varsTail
      have hHeadMem :
          eo_var_list_mem (Term.Var (Term.String s) T)
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) tail) := by
        exact Or.inl rfl
      constructor
      · intro M v _hvTy _hvCan
        exact
          (hEval M (native_model_push M s (__eo_to_smt_type T) v)
            (scannerModelRel_push_nil_of_setof_mem
              M s T orig v hOrigVar (hMemOrig s T hHeadMem)
              (hWf s T hHeadMem))).symm
      · apply ih
        · intro s' T' hMemTail
          exact hMemOrig s' T' (Or.inr hMemTail)
        · intro s' T' hMemTail
          exact hWf s' T' (Or.inr hMemTail)

private theorem smtx_model_eval_none_eq (M : SmtModel) :
    __smtx_model_eval M SmtTerm.None = SmtValue.NotValue := by
  simp [__smtx_model_eval]

private theorem smtx_model_eval_var_eq
    (M : SmtModel) (s : native_String) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.Var s T) =
      native_model_var_lookup M s T := by
  simp [__smtx_model_eval]

private theorem contains_atomic_qterm_body_of_false
    {Q y F xs bvs : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv y vars)
    (hy : y ≠ Term.__eo_List_nil)
    (hQNe : Q ≠ Term.Stuck)
    (hScan :
      __contains_atomic_term_list_free_rec (qterm Q y F) xs bvs =
        Term.Boolean false) :
    __contains_atomic_term_list_free_rec F xs
        (__eo_list_concat Term.__eo_List_cons y bvs) =
      Term.Boolean false := by
  cases hEnv with
  | nil =>
      exact False.elim (hy rfl)
  | cons hTail =>
      rename_i s T tail varsTail
      have hXs : xs ≠ Term.Stuck := by
        intro h
        subst xs
        cases bvs <;> simp [qterm, __contains_atomic_term_list_free_rec] at hScan
      have hBvs : bvs ≠ Term.Stuck := by
        intro h
        subst bvs
        cases xs <;> simp [qterm, __contains_atomic_term_list_free_rec] at hScan
      simp only [qterm] at hScan
      rw [Eo.__contains_atomic_term_list_free_rec.eq_4
        xs bvs Q (Term.Var (Term.String s) T) tail F hXs hBvs] at hScan
      exact hScan

private theorem smtx_model_eval_var_eq_of_scannerModelRel
    (xs bvs : Term) (M N : SmtModel)
    (hRel : scannerModelRel xs bvs M N)
    (s : native_String) (T : Term)
    (hScan :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) xs bvs =
        Term.Boolean false) :
    __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
      __smtx_model_eval N (__eo_to_smt (Term.Var (Term.String s) T)) := by
  rw [TranslationProofs.eo_to_smt_var, smtx_model_eval_var_eq,
    smtx_model_eval_var_eq]
  have hXs : xs ≠ Term.Stuck := by
    intro h
    subst xs
    cases bvs <;> simp [__contains_atomic_term_list_free_rec] at hScan
  have hBvs : bvs ≠ Term.Stuck := by
    intro h
    subst bvs
    cases xs <;> simp [__contains_atomic_term_list_free_rec] at hScan
  rw [Eo.__contains_atomic_term_list_free_rec.eq_6 xs bvs
    (Term.String s) T hXs hBvs] at hScan
  exact hRel.vars_eq s T hScan

private theorem smtx_model_eval_uconst_eq
    (M : SmtModel) (s : native_String) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.UConst s T) =
      native_model_lookup M s T := by
  simp [__smtx_model_eval]

private theorem smtx_model_eval_uconst_eq_of_scannerModelRel
    (xs bvs : Term) (M N : SmtModel)
    (hRel : scannerModelRel xs bvs M N)
    (i : native_Nat) (T : Term) :
    __smtx_model_eval M (__eo_to_smt (Term.UConst i T)) =
      __smtx_model_eval N (__eo_to_smt (Term.UConst i T)) := by
  rw [TranslationProofs.eo_to_smt_uconst, smtx_model_eval_uconst_eq,
    smtx_model_eval_uconst_eq]
  exact hRel.globals.1 (native_uconst_id i) (__eo_to_smt_type T)

private theorem smtx_model_eval_eq_of_closed_nil_scannerModelRel
    {xs bvs : Term} {M N : SmtModel} {t : SmtTerm}
    (hRel : scannerModelRel xs bvs M N)
    (hClosed : SmtTermClosedIn [] t) :
    __smtx_model_eval M t = __smtx_model_eval N t := by
  exact smt_model_eval_eq_of_closedIn t [] M N hClosed
    (model_agrees_on_env_nil_of_globals hRel.globals)

private theorem model_agrees_on_env_of_scannerModelRel_bvs
    {xs bvs : Term} {vars : List SmtVarKey} {M N : SmtModel}
    (hXsVar : eo_var_list xs)
    (hBvsEnv : EoSmtVarEnv bvs vars)
    (hRel : scannerModelRel xs bvs M N) :
    model_agrees_on_env vars M N := by
  refine ⟨hRel.globals, ?_⟩
  intro s T hMem
  rcases eo_smt_var_env_var_list_mem_of_mem hBvsEnv hMem with
    ⟨s', Tm, hKey, hTermMem⟩
  have hs : s = s' := congrArg Prod.fst hKey
  have hT : T = __eo_to_smt_type Tm := congrArg Prod.snd hKey
  subst s
  subst T
  have hBvsVar : eo_var_list bvs :=
    eo_var_list_of_env hBvsEnv
  have hBvsHit :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons bvs
            (Term.Var (Term.String s') Tm)) =
        Term.Boolean false :=
    eo_is_neg_list_find_false_of_var_list_mem
      hBvsVar (term_var_string_ne_stuck s' Tm) hTermMem
  exact hRel.vars_eq s' Tm (by
    by_cases hXsMem :
        eo_var_list_mem (Term.Var (Term.String s') Tm) xs
    · have hXsHit :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s') Tm)) =
            Term.Boolean false :=
        eo_is_neg_list_find_false_of_var_list_mem
          hXsVar (term_var_string_ne_stuck s' Tm) hXsMem
      simp [__eo_ite, hXsHit, hBvsHit, native_ite, native_teq]
    · have hXsMiss :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s') Tm)) =
            Term.Boolean true :=
        eo_is_neg_list_find_true_of_var_list_not_mem
          hXsVar (term_var_string_ne_stuck s' Tm) hXsMem
      simp [__eo_ite, hXsMiss, hBvsHit, native_ite, native_teq])

private theorem smtx_model_eval_apply_eq_of_eval_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (f a : SmtTerm) :
    __smtx_model_eval M f = __smtx_model_eval N f ->
    __smtx_model_eval M a = __smtx_model_eval N a ->
      __smtx_model_eval M (SmtTerm.Apply f a) =
        __smtx_model_eval N (SmtTerm.Apply f a) := by
  intro hf ha
  cases f <;>
    simp [__smtx_model_eval, hf, ha,
      smtx_model_eval_apply_eq_of_globals hAgree,
      smtx_model_eval_dt_sel_eq_of_globals hAgree]

private theorem smtTermClosedIn_eo_to_smt_uop2_at_bv
    (vars : List SmtVarKey) (a b : Term) :
    SmtTermClosedIn vars
      (__eo_to_smt (Term.UOp2 UserOp2._at_bv a b)) := by
  change SmtTermClosedIn vars
    (__eo_to_smt__at_bv (__eo_to_smt a) (__eo_to_smt b))
  cases __eo_to_smt a <;> cases __eo_to_smt b <;> try trivial
  case Numeral.Numeral n w =>
    change SmtTermClosedIn vars
      (native_ite (native_zleq 0 w)
        (SmtTerm.Binary w (native_mod_total n (native_int_pow2 w)))
        SmtTerm.None)
    cases native_zleq 0 w <;> trivial

private theorem smtTermClosedIn_eo_to_smt_uop2_at_bv_nil
    (a b : Term) :
    SmtTermClosedIn []
      (__eo_to_smt (Term.UOp2 UserOp2._at_bv a b)) :=
  smtTermClosedIn_eo_to_smt_uop2_at_bv [] a b

private theorem smtTermClosedIn_eo_to_smt_uop3_witness_string_length
    (vars : List SmtVarKey) (a b c : Term) :
    SmtTermClosedIn vars
      (__eo_to_smt (Term.UOp3 UserOp3._at_witness_string_length a b c)) := by
  change SmtTermClosedIn vars
    (native_ite (__eo_to_smt_nat_is_valid b)
      (native_ite (__eo_to_smt_nat_is_valid c)
        (SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type a)
          (SmtTerm.eq
            (SmtTerm.str_len
              (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type a)))
            (__eo_to_smt b))
          native_nat_zero)
        SmtTerm.None)
      SmtTerm.None)
  cases b <;> try (change SmtTermClosedIn vars SmtTerm.None; trivial)
  case Numeral n =>
    change SmtTermClosedIn vars
      (native_ite (native_zleq 0 n)
        (native_ite (__eo_to_smt_nat_is_valid c)
          (SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type a)
            (SmtTerm.eq
              (SmtTerm.str_len
                (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type a)))
              (SmtTerm.Numeral n))
            native_nat_zero)
          SmtTerm.None)
        SmtTerm.None)
    cases native_zleq 0 n
    · trivial
    · cases c <;> try (change SmtTermClosedIn vars SmtTerm.None; trivial)
      case Numeral m =>
        change SmtTermClosedIn vars
          (native_ite (native_zleq 0 m)
            (SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type a)
              (SmtTerm.eq
                (SmtTerm.str_len
                  (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type a)))
                (SmtTerm.Numeral n))
              native_nat_zero)
            SmtTerm.None)
        cases native_zleq 0 m
        · change SmtTermClosedIn vars SmtTerm.None
          trivial
        · change SmtTermClosedIn vars
            (SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type a)
              (SmtTerm.eq
                (SmtTerm.str_len
                  (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type a)))
                (SmtTerm.Numeral n))
              native_nat_zero)
          simp [SmtTermClosedIn]

private theorem smtTermClosedIn_eo_to_smt_uop3_witness_string_length_nil
    (a b c : Term) :
    SmtTermClosedIn []
      (__eo_to_smt (Term.UOp3 UserOp3._at_witness_string_length a b c)) :=
  smtTermClosedIn_eo_to_smt_uop3_witness_string_length [] a b c

private theorem re_unfold_pos_component_args_of_non_none
    (s r : SmtTerm) (n : native_Nat)
    (hNN :
      term_has_non_none_type
        (__eo_to_smt_re_unfold_pos_component s r n)) :
    __smtx_typeof s = SmtType.Seq SmtType.Char ∧
      __smtx_typeof r = SmtType.RegLan := by
  induction n generalizing s r with
  | zero =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN
      case re_concat r1 r2 =>
        have hTermNN :
            term_has_non_none_type
              (SmtTerm.str_substr s (SmtTerm.Numeral 0)
                (SmtTerm.str_indexof_re_split s r1 r2)) := by
          simpa [__eo_to_smt_re_unfold_pos_component] using hNN
        rcases str_substr_args_of_non_none hTermNN with
          ⟨T, hS, hStart, hLen⟩
        have hSplitNN :
            term_has_non_none_type
              (SmtTerm.str_indexof_re_split s r1 r2) := by
          unfold term_has_non_none_type
          rw [hLen]
          simp
        have hSplitArgs :=
          str_indexof_re_split_args_of_non_none hSplitNN
        have hR :
            __smtx_typeof (SmtTerm.re_concat r1 r2) =
              SmtType.RegLan := by
          rw [typeof_re_concat_eq]
          simp [hSplitArgs.2.1, hSplitArgs.2.2, native_ite,
            native_Teq]
        exact ⟨hSplitArgs.1, hR⟩
      all_goals
        exfalso
        unfold term_has_non_none_type at hNN
        exact hNN TranslationProofs.smtx_typeof_none
  | succ n ih =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN
      case re_concat r1 r2 =>
        let split := SmtTerm.str_indexof_re_split s r1 r2
        let suffix :=
          SmtTerm.str_substr s split
            (SmtTerm.neg (SmtTerm.str_len s) split)
        have hRecArgs :
            __smtx_typeof suffix = SmtType.Seq SmtType.Char ∧
              __smtx_typeof r2 = SmtType.RegLan :=
          ih suffix r2 (by
            simpa [suffix, split, __eo_to_smt_re_unfold_pos_component]
              using hNN)
        have hSuffixNN : term_has_non_none_type suffix := by
          unfold term_has_non_none_type
          rw [hRecArgs.1]
          simp
        rcases str_substr_args_of_non_none hSuffixNN with
          ⟨T, hSRaw, hSplit, hLen⟩
        have hSplitNN : term_has_non_none_type split := by
          unfold term_has_non_none_type
          rw [hSplit]
          simp
        have hSplitArgs :=
          str_indexof_re_split_args_of_non_none hSplitNN
        have hR :
            __smtx_typeof (SmtTerm.re_concat r1 r2) =
              SmtType.RegLan := by
          rw [typeof_re_concat_eq]
          simp [hSplitArgs.2.1, hSplitArgs.2.2, native_ite,
            native_Teq]
        exact ⟨hSplitArgs.1, hR⟩
      all_goals
        exfalso
        unfold term_has_non_none_type at hNN
        exact hNN TranslationProofs.smtx_typeof_none

private theorem contains_atomic_term_list_free_rec_vars_ne_stuck_of_false
    {t xs bvs : Term} :
    __contains_atomic_term_list_free_rec t xs bvs = Term.Boolean false ->
    xs ≠ Term.Stuck := by
  intro h hxs
  subst xs
  cases t <;> cases bvs <;>
    simp [__contains_atomic_term_list_free_rec] at h

private theorem smtx_model_eval_eq_of_contains_atomic_false
    (t xs bvs : Term) :
    eo_var_list bvs ->
    (∀ M N : SmtModel,
      scannerModelRel xs bvs M N ->
      __contains_atomic_term_list_free_rec t xs bvs =
        Term.Boolean false ->
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_model_eval M (__eo_to_smt t) =
        __smtx_model_eval N (__eo_to_smt t)) := by
  induction t, xs, bvs using Eo.__contains_atomic_term_list_free_rec.induct with
  | case1 xs bvs =>
      intro hBvsVar M N hRel hScan hNN
      simp [__contains_atomic_term_list_free_rec] at hScan
  | case2 t bvs ht =>
      intro hBvsVar M N hRel hScan hNN
      simp [__contains_atomic_term_list_free_rec] at hScan
  | case3 t xs ht hxs =>
      intro hBvsVar M N hRel hScan hNN
      simp [__contains_atomic_term_list_free_rec] at hScan
  | case4 q x ys a xs bvs hXs hBvs ih =>
      intro hBvsVar M N hRel hScan hNN
      let binders :=
        Term.Apply (Term.Apply Term.__eo_List_cons x) ys
      have hBindersNonNil : binders ≠ Term.__eo_List_nil := by
        dsimp [binders]
        intro h
        cases h
      have hScanBody :
          __contains_atomic_term_list_free_rec a xs
              (__eo_list_concat Term.__eo_List_cons binders bvs) =
            Term.Boolean false := by
        simpa [binders, __contains_atomic_term_list_free_rec] using hScan
      have hBindersNone :
          __smtx_typeof (__eo_to_smt binders) = SmtType.None := by
        dsimp [binders]
        exact smtx_typeof_eo_to_smt_list_cons_none x ys
      by_cases hQ :
          q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists
      · have hQuantNN :
            __smtx_typeof (__eo_to_smt (qterm q binders a)) ≠
              SmtType.None := by
          simpa [qterm, binders] using hNN
        have hQuantTy :
            __smtx_typeof (__eo_to_smt (qterm q binders a)) =
              SmtType.Bool :=
          qterm_typeof_bool_of_quant_non_none q binders a hQ hQuantNN
        have hBodyTy :
            __smtx_typeof (__eo_to_smt a) = SmtType.Bool :=
          qterm_body_typeof_bool_of_quant_typeof_bool
            q binders a hQ hQuantTy
        have hBodyNN :
            __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
          rw [hBodyTy]
          simp
        rcases qterm_binder_env_of_quant_typeof_bool
            q binders a hQ hQuantTy with
          ⟨binderVars, hBinders⟩
        have hBindersVar : eo_var_list binders :=
          eo_var_list_of_env hBinders
        have hBvsList :
            __eo_is_list Term.__eo_List_cons bvs = Term.Boolean true :=
          eo_var_list_is_list hBvsVar
        have hBindersList :
            __eo_is_list Term.__eo_List_cons binders =
              Term.Boolean true :=
          eo_var_list_is_list hBindersVar
        have hConcatEq :
            __eo_list_concat Term.__eo_List_cons binders bvs =
              __eo_list_concat_rec binders bvs := by
          simp [__eo_list_concat, hBindersList, hBvsList,
            __eo_requires, native_ite, native_teq, native_not,
            SmtEval.native_not]
        have hAllBvsVarTop :
            eo_var_list
              (__eo_list_concat Term.__eo_List_cons binders bvs) :=
          eo_var_list_concat hBindersVar hBvsVar
        have hBodyEval :
            ∀ M' N' : SmtModel,
              scannerModelRel xs (__eo_list_concat_rec binders bvs)
                M' N' ->
                __smtx_model_eval M' (__eo_to_smt a) =
                  __smtx_model_eval N' (__eo_to_smt a) := by
          intro M' N' hRel'
          have hRelTop :
              scannerModelRel xs
                  (__eo_list_concat Term.__eo_List_cons binders bvs)
                  M' N' := by
            simpa [hConcatEq] using hRel'
          exact ih hAllBvsVarTop M' N' hRelTop hScanBody hBodyNN
        rcases hQ with hForall | hExists
        · subst q
          have hExistsEval :
              __smtx_model_eval M
                  (__eo_to_smt_exists binders
                    (SmtTerm.not (__eo_to_smt a))) =
                __smtx_model_eval N
                  (__eo_to_smt_exists binders
                    (SmtTerm.not (__eo_to_smt a))) :=
            smtx_model_eval_eo_to_smt_exists_eq_of_scanner_body
              (SmtTerm.not (__eo_to_smt a)) hBinders
              hBvsVar hRel
              (fun M' N' hRel' =>
                smtx_model_eval_not_eq_of_eval_eq
                  (hBodyEval M' N' hRel'))
          have hForallEval :
              __smtx_model_eval M
                  (SmtTerm.not
                    (__eo_to_smt_exists binders
                      (SmtTerm.not (__eo_to_smt a)))) =
                __smtx_model_eval N
                  (SmtTerm.not
                    (__eo_to_smt_exists binders
                      (SmtTerm.not (__eo_to_smt a)))) :=
            smtx_model_eval_not_eq_of_eval_eq hExistsEval
          change
            __smtx_model_eval M
                (__eo_to_smt
                  (qforall binders a)) =
              __smtx_model_eval N
                (__eo_to_smt
                  (qforall binders a))
          rw [eo_to_smt_forall_eq binders a hBindersNonNil]
          exact hForallEval
        · subst q
          have hExistsEval :
              __smtx_model_eval M
                  (__eo_to_smt_exists binders (__eo_to_smt a)) =
                __smtx_model_eval N
                  (__eo_to_smt_exists binders (__eo_to_smt a)) :=
            smtx_model_eval_eo_to_smt_exists_eq_of_scanner_body
              (__eo_to_smt a) hBinders hBvsVar hRel hBodyEval
          change
            __smtx_model_eval M
                (__eo_to_smt
                  (qexists binders a)) =
              __smtx_model_eval N
                (__eo_to_smt
                  (qexists binders a))
          rw [eo_to_smt_exists_eq binders a hBindersNonNil]
          exact hExistsEval
      · by_cases hNotOp : q = Term.UOp UserOp.not
        · subst q
          exfalso
          apply hNN
          change
            __smtx_typeof
                (SmtTerm.Apply
                  (SmtTerm.not (__eo_to_smt binders))
                  (__eo_to_smt a)) =
              SmtType.None
          exact smtx_typeof_apply_not_head_none
            (__eo_to_smt binders) (__eo_to_smt a)
        · by_cases hPurifyOp : q = Term.UOp UserOp._at_purify
          · subst q
            exfalso
            apply hNN
            change
              __smtx_typeof
                  (SmtTerm.Apply
                    (SmtTerm._at_purify (__eo_to_smt binders))
                    (__eo_to_smt a)) =
                SmtType.None
            exact smtx_typeof_apply_purify_head_none
              (__eo_to_smt binders) (__eo_to_smt a)
              hBindersNone
          · by_cases hIteOp : q = Term.UOp UserOp.ite
            · subst q
              exfalso
              apply hNN
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (SmtTerm.Apply SmtTerm.None (__eo_to_smt binders))
                      (__eo_to_smt a)) =
                  SmtType.None
              exact smtx_typeof_apply_apply_arg_none
                SmtTerm.None (__eo_to_smt binders) (__eo_to_smt a)
                hBindersNone
            · by_cases hBoolOp :
                q = Term.UOp UserOp.or ∨
                  q = Term.UOp UserOp.and ∨
                  q = Term.UOp UserOp.imp ∨
                  q = Term.UOp UserOp.xor ∨
                  q = Term.UOp UserOp.eq
              · rcases hBoolOp with hOr | hAnd | hImp | hXor | hEq
                · subst q
                  exfalso
                  apply hNN
                  change
                    __smtx_typeof
                        (SmtTerm.or (__eo_to_smt binders) (__eo_to_smt a)) =
                      SmtType.None
                  exact smtx_typeof_or_first_arg_none
                    (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                · subst q
                  exfalso
                  apply hNN
                  change
                    __smtx_typeof
                        (SmtTerm.and (__eo_to_smt binders) (__eo_to_smt a)) =
                      SmtType.None
                  exact smtx_typeof_and_first_arg_none
                    (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                · subst q
                  exfalso
                  apply hNN
                  change
                    __smtx_typeof
                        (SmtTerm.imp (__eo_to_smt binders) (__eo_to_smt a)) =
                      SmtType.None
                  exact smtx_typeof_imp_first_arg_none
                    (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                · subst q
                  exfalso
                  apply hNN
                  change
                    __smtx_typeof
                        (SmtTerm.xor (__eo_to_smt binders) (__eo_to_smt a)) =
                      SmtType.None
                  exact smtx_typeof_xor_first_arg_none
                    (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                · subst q
                  exfalso
                  apply hNN
                  change
                    __smtx_typeof
                        (SmtTerm.eq (__eo_to_smt binders) (__eo_to_smt a)) =
                      SmtType.None
                  exact smtx_typeof_eq_first_arg_none
                    (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
              · by_cases hArithOp :
                  q = Term.UOp UserOp.plus ∨
                    q = Term.UOp UserOp.neg ∨
                    q = Term.UOp UserOp.mult ∨
                    q = Term.UOp UserOp.lt ∨
                    q = Term.UOp UserOp.leq ∨
                    q = Term.UOp UserOp.gt ∨
                    q = Term.UOp UserOp.geq
                · rcases hArithOp with
                    hPlus | hNeg | hMult | hLt | hLeq | hGt | hGeq
                  · subst q
                    exfalso
                    apply hNN
                    change
                      __smtx_typeof
                          (SmtTerm.plus (__eo_to_smt binders) (__eo_to_smt a)) =
                        SmtType.None
                    exact smtx_typeof_plus_first_arg_none
                      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                  · subst q
                    exfalso
                    apply hNN
                    change
                      __smtx_typeof
                          (SmtTerm.neg (__eo_to_smt binders) (__eo_to_smt a)) =
                        SmtType.None
                    exact smtx_typeof_neg_first_arg_none
                      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                  · subst q
                    exfalso
                    apply hNN
                    change
                      __smtx_typeof
                          (SmtTerm.mult (__eo_to_smt binders) (__eo_to_smt a)) =
                        SmtType.None
                    exact smtx_typeof_mult_first_arg_none
                      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                  · subst q
                    exfalso
                    apply hNN
                    change
                      __smtx_typeof
                          (SmtTerm.lt (__eo_to_smt binders) (__eo_to_smt a)) =
                        SmtType.None
                    exact smtx_typeof_lt_first_arg_none
                      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                  · subst q
                    exfalso
                    apply hNN
                    change
                      __smtx_typeof
                          (SmtTerm.leq (__eo_to_smt binders) (__eo_to_smt a)) =
                        SmtType.None
                    exact smtx_typeof_leq_first_arg_none
                      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                  · subst q
                    exfalso
                    apply hNN
                    change
                      __smtx_typeof
                          (SmtTerm.gt (__eo_to_smt binders) (__eo_to_smt a)) =
                        SmtType.None
                    exact smtx_typeof_gt_first_arg_none
                      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                  · subst q
                    exfalso
                    apply hNN
                    change
                      __smtx_typeof
                          (SmtTerm.geq (__eo_to_smt binders) (__eo_to_smt a)) =
                        SmtType.None
                    exact smtx_typeof_geq_first_arg_none
                      (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                · by_cases hIntOp :
                    q = Term.UOp UserOp.div ∨
                      q = Term.UOp UserOp.mod ∨
                      q = Term.UOp UserOp.multmult ∨
                      q = Term.UOp UserOp.divisible ∨
                      q = Term.UOp UserOp.div_total ∨
                      q = Term.UOp UserOp.mod_total ∨
                      q = Term.UOp UserOp.multmult_total
                  · rcases hIntOp with
                      hDiv | hMod | hMultmult | hDivisible |
                      hDivTotal | hModTotal | hMultmultTotal
                    · subst q
                      exfalso
                      apply hNN
                      change
                        __smtx_typeof
                            (SmtTerm.div (__eo_to_smt binders) (__eo_to_smt a)) =
                          SmtType.None
                      exact smtx_typeof_div_first_arg_none
                        (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                    · subst q
                      exfalso
                      apply hNN
                      change
                        __smtx_typeof
                            (SmtTerm.mod (__eo_to_smt binders) (__eo_to_smt a)) =
                          SmtType.None
                      exact smtx_typeof_mod_first_arg_none
                        (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                    · subst q
                      exfalso
                      apply hNN
                      change
                        __smtx_typeof
                            (SmtTerm.multmult (__eo_to_smt binders)
                              (__eo_to_smt a)) =
                          SmtType.None
                      exact smtx_typeof_multmult_first_arg_none
                        (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                    · subst q
                      exfalso
                      apply hNN
                      change
                        __smtx_typeof
                            (SmtTerm.divisible (__eo_to_smt binders)
                              (__eo_to_smt a)) =
                          SmtType.None
                      exact smtx_typeof_divisible_first_arg_none
                        (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                    · subst q
                      exfalso
                      apply hNN
                      change
                        __smtx_typeof
                            (SmtTerm.div_total (__eo_to_smt binders)
                              (__eo_to_smt a)) =
                          SmtType.None
                      exact smtx_typeof_div_total_first_arg_none
                        (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                    · subst q
                      exfalso
                      apply hNN
                      change
                        __smtx_typeof
                            (SmtTerm.mod_total (__eo_to_smt binders)
                              (__eo_to_smt a)) =
                          SmtType.None
                      exact smtx_typeof_mod_total_first_arg_none
                        (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                    · subst q
                      exfalso
                      apply hNN
                      change
                        __smtx_typeof
                            (SmtTerm.multmult_total (__eo_to_smt binders)
                              (__eo_to_smt a)) =
                          SmtType.None
                      exact smtx_typeof_multmult_total_first_arg_none
                        (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                  · by_cases hRatOp :
                      q = Term.UOp UserOp.qdiv ∨
                        q = Term.UOp UserOp.qdiv_total
                    · rcases hRatOp with hQdiv | hQdivTotal
                      · subst q
                        exfalso
                        apply hNN
                        change
                          __smtx_typeof
                              (SmtTerm.qdiv (__eo_to_smt binders)
                                (__eo_to_smt a)) =
                            SmtType.None
                        exact smtx_typeof_qdiv_first_arg_none
                          (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                      · subst q
                        exfalso
                        apply hNN
                        change
                          __smtx_typeof
                              (SmtTerm.qdiv_total (__eo_to_smt binders)
                                (__eo_to_smt a)) =
                            SmtType.None
                        exact smtx_typeof_qdiv_total_first_arg_none
                          (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                    · by_cases hArrayBvOp :
                        q = Term.UOp UserOp.select ∨
                          q = Term.UOp UserOp.concat
                      · rcases hArrayBvOp with hSelect | hConcat
                        · subst q
                          exfalso
                          apply hNN
                          change
                            __smtx_typeof
                                (SmtTerm.select (__eo_to_smt binders)
                                  (__eo_to_smt a)) =
                              SmtType.None
                          exact smtx_typeof_select_first_arg_none
                            (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                        · subst q
                          exfalso
                          apply hNN
                          change
                            __smtx_typeof
                                (SmtTerm.concat (__eo_to_smt binders)
                                  (__eo_to_smt a)) =
                              SmtType.None
                          exact smtx_typeof_concat_first_arg_none
                            (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                      · by_cases hStringOp :
                          q = Term.UOp UserOp.str_concat ∨
                            q = Term.UOp UserOp.str_contains ∨
                            q = Term.UOp UserOp.str_at ∨
                            q = Term.UOp UserOp.str_prefixof ∨
                            q = Term.UOp UserOp.str_suffixof ∨
                            q = Term.UOp UserOp.str_lt ∨
                            q = Term.UOp UserOp.str_leq
                        · rcases hStringOp with
                            hStrConcat | hStrContains | hStrAt |
                            hStrPrefixof | hStrSuffixof | hStrLt | hStrLeq
                          · subst q
                            exfalso
                            apply hNN
                            change
                              __smtx_typeof
                                  (SmtTerm.str_concat (__eo_to_smt binders)
                                    (__eo_to_smt a)) =
                                SmtType.None
                            exact smtx_typeof_str_concat_first_arg_none
                              (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                          · subst q
                            exfalso
                            apply hNN
                            change
                              __smtx_typeof
                                  (SmtTerm.str_contains (__eo_to_smt binders)
                                    (__eo_to_smt a)) =
                                SmtType.None
                            exact smtx_typeof_str_contains_first_arg_none
                              (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                          · subst q
                            exfalso
                            apply hNN
                            change
                              __smtx_typeof
                                  (SmtTerm.str_at (__eo_to_smt binders)
                                    (__eo_to_smt a)) =
                                SmtType.None
                            exact smtx_typeof_str_at_first_arg_none
                              (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                          · subst q
                            exfalso
                            apply hNN
                            change
                              __smtx_typeof
                                  (SmtTerm.str_prefixof (__eo_to_smt binders)
                                    (__eo_to_smt a)) =
                                SmtType.None
                            exact smtx_typeof_str_prefixof_first_arg_none
                              (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                          · subst q
                            exfalso
                            apply hNN
                            change
                              __smtx_typeof
                                  (SmtTerm.str_suffixof (__eo_to_smt binders)
                                    (__eo_to_smt a)) =
                                SmtType.None
                            exact smtx_typeof_str_suffixof_first_arg_none
                              (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                          · subst q
                            exfalso
                            apply hNN
                            change
                              __smtx_typeof
                                  (SmtTerm.str_lt (__eo_to_smt binders)
                                    (__eo_to_smt a)) =
                                SmtType.None
                            exact smtx_typeof_str_lt_first_arg_none
                              (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                          · subst q
                            exfalso
                            apply hNN
                            change
                              __smtx_typeof
                                  (SmtTerm.str_leq (__eo_to_smt binders)
                                    (__eo_to_smt a)) =
                                SmtType.None
                            exact smtx_typeof_str_leq_first_arg_none
                              (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                        · by_cases hRegexSeqOp :
                            q = Term.UOp UserOp.re_range ∨
                              q = Term.UOp UserOp.re_concat ∨
                              q = Term.UOp UserOp.re_inter ∨
                              q = Term.UOp UserOp.re_union ∨
                              q = Term.UOp UserOp.re_diff ∨
                              q = Term.UOp UserOp.str_in_re ∨
                              q = Term.UOp UserOp.seq_nth
                          · rcases hRegexSeqOp with
                              hReRange | hReConcat | hReInter |
                              hReUnion | hReDiff | hStrInRe | hSeqNth
                            · subst q
                              exfalso
                              apply hNN
                              change
                                __smtx_typeof
                                    (SmtTerm.re_range (__eo_to_smt binders)
                                      (__eo_to_smt a)) =
                                  SmtType.None
                              exact smtx_typeof_re_range_first_arg_none
                                (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                            · subst q
                              exfalso
                              apply hNN
                              change
                                __smtx_typeof
                                    (SmtTerm.re_concat (__eo_to_smt binders)
                                      (__eo_to_smt a)) =
                                  SmtType.None
                              exact smtx_typeof_re_concat_first_arg_none
                                (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                            · subst q
                              exfalso
                              apply hNN
                              change
                                __smtx_typeof
                                    (SmtTerm.re_inter (__eo_to_smt binders)
                                      (__eo_to_smt a)) =
                                  SmtType.None
                              exact smtx_typeof_re_inter_first_arg_none
                                (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                            · subst q
                              exfalso
                              apply hNN
                              change
                                __smtx_typeof
                                    (SmtTerm.re_union (__eo_to_smt binders)
                                      (__eo_to_smt a)) =
                                  SmtType.None
                              exact smtx_typeof_re_union_first_arg_none
                                (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                            · subst q
                              exfalso
                              apply hNN
                              change
                                __smtx_typeof
                                    (SmtTerm.re_diff (__eo_to_smt binders)
                                      (__eo_to_smt a)) =
                                  SmtType.None
                              exact smtx_typeof_re_diff_first_arg_none
                                (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                            · subst q
                              exfalso
                              apply hNN
                              change
                                __smtx_typeof
                                    (SmtTerm.str_in_re (__eo_to_smt binders)
                                      (__eo_to_smt a)) =
                                  SmtType.None
                              exact smtx_typeof_str_in_re_first_arg_none
                                (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                            · subst q
                              exfalso
                              apply hNN
                              change
                                __smtx_typeof
                                    (SmtTerm.seq_nth (__eo_to_smt binders)
                                      (__eo_to_smt a)) =
                                  SmtType.None
                              exact smtx_typeof_seq_nth_first_arg_none
                                (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                          · by_cases hSetOp :
                                q = Term.UOp UserOp.set_union ∨
                                  q = Term.UOp UserOp.set_inter ∨
                                  q = Term.UOp UserOp.set_minus ∨
                                  q = Term.UOp UserOp.set_subset ∨
                                  q = Term.UOp UserOp.set_singleton ∨
                                  q = Term.UOp UserOp.set_insert
                            · rcases hSetOp with
                                hSetUnion | hSetInter | hSetMinus |
                                hSetSubset | hSetSingleton | hSetInsert
                              · subst q
                                exfalso
                                apply hNN
                                change
                                  __smtx_typeof
                                      (SmtTerm.set_union (__eo_to_smt binders)
                                        (__eo_to_smt a)) =
                                    SmtType.None
                                exact smtx_typeof_set_union_first_arg_none
                                  (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                              · subst q
                                exfalso
                                apply hNN
                                change
                                  __smtx_typeof
                                      (SmtTerm.set_inter (__eo_to_smt binders)
                                        (__eo_to_smt a)) =
                                    SmtType.None
                                exact smtx_typeof_set_inter_first_arg_none
                                  (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                              · subst q
                                exfalso
                                apply hNN
                                change
                                  __smtx_typeof
                                      (SmtTerm.set_minus (__eo_to_smt binders)
                                        (__eo_to_smt a)) =
                                    SmtType.None
                                exact smtx_typeof_set_minus_first_arg_none
                                  (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                              · subst q
                                exfalso
                                apply hNN
                                change
                                  __smtx_typeof
                                      (SmtTerm.set_subset (__eo_to_smt binders)
                                        (__eo_to_smt a)) =
                                    SmtType.None
                                exact smtx_typeof_set_subset_first_arg_none
                                  (__eo_to_smt binders) (__eo_to_smt a) hBindersNone
                              · subst q
                                exfalso
                                apply hNN
                                change
                                  __smtx_typeof
                                      (SmtTerm.Apply
                                        (SmtTerm.set_singleton
                                          (__eo_to_smt binders))
                                        (__eo_to_smt a)) =
                                    SmtType.None
                                exact smtx_typeof_apply_set_singleton_head_none
                                  (__eo_to_smt binders) (__eo_to_smt a)
                                  hBindersNone
                              · subst q
                                exfalso
                                apply hNN
                                exact
                                  smtx_typeof_eo_to_smt_apply_apply_list_set_insert_head_none
                                    x ys a
                            · by_cases hUnaryArithOp : (
                                q = Term.UOp UserOp.to_real ∨
                                  q = Term.UOp UserOp.to_int ∨
                                  q = Term.UOp UserOp.is_int ∨
                                  q = Term.UOp UserOp.abs ∨
                                  q = Term.UOp UserOp.__eoo_neg_2 ∨
                                  q = Term.UOp UserOp.int_pow2 ∨
                                  q = Term.UOp UserOp.int_log2 ∨
                                  q = Term.UOp UserOp.int_ispow2 ∨
                                  q = Term.UOp UserOp._at_int_div_by_zero ∨
                                  q = Term.UOp UserOp._at_mod_by_zero ∨
                                  q = Term.UOp UserOp._at_div_by_zero)
                              · exfalso
                                apply hNN
                                exact
                                  smtx_typeof_eo_to_smt_apply_apply_unary_arith_head_none
                                    q binders a hUnaryArithOp hBindersNone
                              · by_cases hUnaryStringOp : (
                                  q = Term.UOp UserOp.str_len ∨
                                    q = Term.UOp UserOp.str_rev ∨
                                    q = Term.UOp UserOp.str_to_lower ∨
                                    q = Term.UOp UserOp.str_to_upper)
                                · rcases hUnaryStringOp with
                                    hStrLen | hStrRev | hStrToLower |
                                    hStrToUpper
                                  · subst q
                                    exfalso
                                    apply hNN
                                    change
                                      __smtx_typeof
                                          (SmtTerm.Apply
                                            (SmtTerm.str_len
                                              (__eo_to_smt binders))
                                            (__eo_to_smt a)) =
                                        SmtType.None
                                    exact smtx_typeof_apply_str_len_head_none
                                      (__eo_to_smt binders) (__eo_to_smt a)
                                      hBindersNone
                                  · subst q
                                    exfalso
                                    apply hNN
                                    change
                                      __smtx_typeof
                                          (SmtTerm.Apply
                                            (SmtTerm.str_rev
                                              (__eo_to_smt binders))
                                            (__eo_to_smt a)) =
                                        SmtType.None
                                    exact smtx_typeof_apply_str_rev_head_none
                                      (__eo_to_smt binders) (__eo_to_smt a)
                                      hBindersNone
                                  · subst q
                                    exfalso
                                    apply hNN
                                    change
                                      __smtx_typeof
                                          (SmtTerm.Apply
                                            (SmtTerm.str_to_lower
                                              (__eo_to_smt binders))
                                            (__eo_to_smt a)) =
                                        SmtType.None
                                    exact smtx_typeof_apply_str_to_lower_head_none
                                      (__eo_to_smt binders) (__eo_to_smt a)
                                      hBindersNone
                                  · subst q
                                    exfalso
                                    apply hNN
                                    change
                                      __smtx_typeof
                                          (SmtTerm.Apply
                                            (SmtTerm.str_to_upper
                                              (__eo_to_smt binders))
                                            (__eo_to_smt a)) =
                                        SmtType.None
                                    exact smtx_typeof_apply_str_to_upper_head_none
                                      (__eo_to_smt binders) (__eo_to_smt a)
                                      hBindersNone
                                · by_cases hUnaryStringCodeOp :
                                    q = Term.UOp UserOp.str_to_code ∨
                                      q = Term.UOp UserOp.str_from_code ∨
                                      q = Term.UOp UserOp.str_is_digit ∨
                                      q = Term.UOp UserOp.str_to_int ∨
                                      q = Term.UOp UserOp.str_from_int
                                  · rcases hUnaryStringCodeOp with
                                      hStrToCode | hStrFromCode |
                                      hStrIsDigit | hStrToInt | hStrFromInt
                                    · subst q
                                      exfalso
                                      apply hNN
                                      change
                                        __smtx_typeof
                                            (SmtTerm.Apply
                                              (SmtTerm.str_to_code
                                                (__eo_to_smt binders))
                                              (__eo_to_smt a)) =
                                          SmtType.None
                                      exact smtx_typeof_apply_str_to_code_head_none
                                        (__eo_to_smt binders) (__eo_to_smt a)
                                        hBindersNone
                                    · subst q
                                      exfalso
                                      apply hNN
                                      change
                                        __smtx_typeof
                                            (SmtTerm.Apply
                                              (SmtTerm.str_from_code
                                                (__eo_to_smt binders))
                                              (__eo_to_smt a)) =
                                          SmtType.None
                                      exact smtx_typeof_apply_str_from_code_head_none
                                        (__eo_to_smt binders) (__eo_to_smt a)
                                        hBindersNone
                                    · subst q
                                      exfalso
                                      apply hNN
                                      change
                                        __smtx_typeof
                                            (SmtTerm.Apply
                                              (SmtTerm.str_is_digit
                                                (__eo_to_smt binders))
                                              (__eo_to_smt a)) =
                                          SmtType.None
                                      exact smtx_typeof_apply_str_is_digit_head_none
                                        (__eo_to_smt binders) (__eo_to_smt a)
                                        hBindersNone
                                    · subst q
                                      exfalso
                                      apply hNN
                                      change
                                        __smtx_typeof
                                            (SmtTerm.Apply
                                              (SmtTerm.str_to_int
                                                (__eo_to_smt binders))
                                              (__eo_to_smt a)) =
                                          SmtType.None
                                      exact smtx_typeof_apply_str_to_int_head_none
                                        (__eo_to_smt binders) (__eo_to_smt a)
                                        hBindersNone
                                    · subst q
                                      exfalso
                                      apply hNN
                                      change
                                        __smtx_typeof
                                            (SmtTerm.Apply
                                              (SmtTerm.str_from_int
                                                (__eo_to_smt binders))
                                              (__eo_to_smt a)) =
                                          SmtType.None
                                      exact smtx_typeof_apply_str_from_int_head_none
                                        (__eo_to_smt binders) (__eo_to_smt a)
                                        hBindersNone
                                  · by_cases hUnaryRegexOp :
                                      q = Term.UOp UserOp.str_to_re ∨
                                        q = Term.UOp UserOp.re_mult ∨
                                        q = Term.UOp UserOp.re_plus ∨
                                        q = Term.UOp UserOp.re_opt ∨
                                        q = Term.UOp UserOp.re_comp
                                    · rcases hUnaryRegexOp with
                                        hStrToRe | hReMult | hRePlus |
                                        hReOpt | hReComp
                                      · subst q
                                        exfalso
                                        apply hNN
                                        change
                                          __smtx_typeof
                                              (SmtTerm.Apply
                                                (SmtTerm.str_to_re
                                                  (__eo_to_smt binders))
                                                (__eo_to_smt a)) =
                                            SmtType.None
                                        exact smtx_typeof_apply_str_to_re_head_none
                                          (__eo_to_smt binders) (__eo_to_smt a)
                                          hBindersNone
                                      · subst q
                                        exfalso
                                        apply hNN
                                        change
                                          __smtx_typeof
                                              (SmtTerm.Apply
                                                (SmtTerm.re_mult
                                                  (__eo_to_smt binders))
                                                (__eo_to_smt a)) =
                                            SmtType.None
                                        exact smtx_typeof_apply_re_mult_head_none
                                          (__eo_to_smt binders) (__eo_to_smt a)
                                          hBindersNone
                                      · subst q
                                        exfalso
                                        apply hNN
                                        change
                                          __smtx_typeof
                                              (SmtTerm.Apply
                                                (SmtTerm.re_plus
                                                  (__eo_to_smt binders))
                                                (__eo_to_smt a)) =
                                            SmtType.None
                                        exact smtx_typeof_apply_re_plus_head_none
                                          (__eo_to_smt binders) (__eo_to_smt a)
                                          hBindersNone
                                      · subst q
                                        exfalso
                                        apply hNN
                                        change
                                          __smtx_typeof
                                              (SmtTerm.Apply
                                                (SmtTerm.re_opt
                                                  (__eo_to_smt binders))
                                                (__eo_to_smt a)) =
                                            SmtType.None
                                        exact smtx_typeof_apply_re_opt_head_none
                                          (__eo_to_smt binders) (__eo_to_smt a)
                                          hBindersNone
                                      · subst q
                                        exfalso
                                        apply hNN
                                        change
                                          __smtx_typeof
                                              (SmtTerm.Apply
                                                (SmtTerm.re_comp
                                                  (__eo_to_smt binders))
                                                (__eo_to_smt a)) =
                                            SmtType.None
                                        exact smtx_typeof_apply_re_comp_head_none
                                          (__eo_to_smt binders) (__eo_to_smt a)
                                          hBindersNone
                                    · by_cases hUnarySeqBvIntOp :
                                        q = Term.UOp UserOp.seq_unit ∨
                                          q = Term.UOp UserOp.ubv_to_int ∨
                                          q = Term.UOp UserOp.sbv_to_int
                                      · rcases hUnarySeqBvIntOp with
                                          hSeqUnit | hUbvToInt | hSbvToInt
                                        · subst q
                                          exfalso
                                          apply hNN
                                          change
                                            __smtx_typeof
                                                (SmtTerm.Apply
                                                  (SmtTerm.seq_unit
                                                    (__eo_to_smt binders))
                                                  (__eo_to_smt a)) =
                                              SmtType.None
                                          exact smtx_typeof_apply_seq_unit_head_none
                                            (__eo_to_smt binders) (__eo_to_smt a)
                                            hBindersNone
                                        · subst q
                                          exfalso
                                          apply hNN
                                          change
                                            __smtx_typeof
                                                (SmtTerm.Apply
                                                  (SmtTerm.ubv_to_int
                                                    (__eo_to_smt binders))
                                                  (__eo_to_smt a)) =
                                              SmtType.None
                                          exact smtx_typeof_apply_ubv_to_int_head_none
                                            (__eo_to_smt binders) (__eo_to_smt a)
                                            hBindersNone
                                        · subst q
                                          exfalso
                                          apply hNN
                                          change
                                            __smtx_typeof
                                                (SmtTerm.Apply
                                                  (SmtTerm.sbv_to_int
                                                    (__eo_to_smt binders))
                                                  (__eo_to_smt a)) =
                                              SmtType.None
                                          exact smtx_typeof_apply_sbv_to_int_head_none
                                            (__eo_to_smt binders) (__eo_to_smt a)
                                            hBindersNone
                                      · by_cases hUnarySetDerivedOp :
                                          q = Term.UOp UserOp.set_choose ∨
                                            q = Term.UOp UserOp.set_is_empty ∨
                                            q = Term.UOp UserOp.set_is_singleton
                                        · rcases hUnarySetDerivedOp with
                                            hSetChoose | hSetIsEmpty |
                                              hSetIsSingleton
                                          · subst q
                                            exfalso
                                            apply hNN
                                            change
                                              __smtx_typeof
                                                  (SmtTerm.Apply
                                                    (SmtTerm.map_diff
                                                      (__eo_to_smt binders)
                                                      (SmtTerm.set_empty
                                                        (__eo_to_smt_set_elem_type
                                                          (__smtx_typeof
                                                            (__eo_to_smt binders)))))
                                                    (__eo_to_smt a)) =
                                                SmtType.None
                                            exact
                                              smtx_typeof_apply_set_choose_head_none
                                                (__eo_to_smt binders)
                                                (__eo_to_smt a) hBindersNone
                                          · subst q
                                            exfalso
                                            apply hNN
                                            change
                                              __smtx_typeof
                                                  (SmtTerm.Apply
                                                    (SmtTerm.eq
                                                      (__eo_to_smt binders)
                                                      (SmtTerm.set_empty
                                                        (__smtx_typeof
                                                          (__eo_to_smt binders))))
                                                    (__eo_to_smt a)) =
                                                SmtType.None
                                            exact
                                              smtx_typeof_apply_set_is_empty_head_none
                                                (__eo_to_smt binders)
                                                (__eo_to_smt a) hBindersNone
                                          · subst q
                                            exfalso
                                            apply hNN
                                            change
                                              __smtx_typeof
                                                  (SmtTerm.Apply
                                                    (SmtTerm.eq
                                                      (__eo_to_smt binders)
                                                      (SmtTerm.set_singleton
                                                        (SmtTerm.map_diff
                                                          (__eo_to_smt binders)
                                                          (SmtTerm.set_empty
                                                            (__eo_to_smt_set_elem_type
                                                              (__smtx_typeof
                                                                (__eo_to_smt binders)))))))
                                                    (__eo_to_smt a)) =
                                                SmtType.None
                                            exact
                                              smtx_typeof_apply_set_is_singleton_head_none
                                                (__eo_to_smt binders)
                                                (__eo_to_smt a) hBindersNone
                                        · by_cases hUnaryBvOp :
                                            q = Term.UOp UserOp.bvnot ∨
                                              q = Term.UOp UserOp.bvneg ∨
                                              q = Term.UOp UserOp.bvnego ∨
                                              q = Term.UOp UserOp.bvredand ∨
                                              q = Term.UOp UserOp.bvredor
                                          · rcases hUnaryBvOp with
                                              hBvnot | hBvneg | hBvnego |
                                                hBvredand | hBvredor
                                            · subst q
                                              exfalso
                                              apply hNN
                                              change
                                                __smtx_typeof
                                                    (SmtTerm.Apply
                                                      (SmtTerm.bvnot
                                                        (__eo_to_smt binders))
                                                      (__eo_to_smt a)) =
                                                  SmtType.None
                                              exact smtx_typeof_apply_bvnot_head_none
                                                (__eo_to_smt binders)
                                                (__eo_to_smt a) hBindersNone
                                            · subst q
                                              exfalso
                                              apply hNN
                                              change
                                                __smtx_typeof
                                                    (SmtTerm.Apply
                                                      (SmtTerm.bvneg
                                                        (__eo_to_smt binders))
                                                      (__eo_to_smt a)) =
                                                  SmtType.None
                                              exact smtx_typeof_apply_bvneg_head_none
                                                (__eo_to_smt binders)
                                                (__eo_to_smt a) hBindersNone
                                            · subst q
                                              exfalso
                                              apply hNN
                                              change
                                                __smtx_typeof
                                                    (SmtTerm.Apply
                                                      (SmtTerm.bvnego
                                                        (__eo_to_smt binders))
                                                      (__eo_to_smt a)) =
                                                  SmtType.None
                                              exact smtx_typeof_apply_bvnego_head_none
                                                (__eo_to_smt binders)
                                                (__eo_to_smt a) hBindersNone
                                            · subst q
                                              exfalso
                                              apply hNN
                                              change
                                                __smtx_typeof
                                                    (SmtTerm.Apply
                                                      (SmtTerm.bvcomp
                                                        (__eo_to_smt binders)
                                                        (SmtTerm.bvnot
                                                          (SmtTerm.Binary
                                                            (__smtx_bv_sizeof_type
                                                              (__smtx_typeof
                                                                (__eo_to_smt binders)))
                                                            0)))
                                                      (__eo_to_smt a)) =
                                                  SmtType.None
                                              exact
                                                smtx_typeof_apply_bvredand_head_none
                                                  (__eo_to_smt binders)
                                                  (__eo_to_smt a) hBindersNone
                                            · subst q
                                              exfalso
                                              apply hNN
                                              change
                                                __smtx_typeof
                                                    (SmtTerm.Apply
                                                      (SmtTerm.bvnot
                                                        (SmtTerm.bvcomp
                                                          (__eo_to_smt binders)
                                                          (SmtTerm.Binary
                                                            (__smtx_bv_sizeof_type
                                                              (__smtx_typeof
                                                                (__eo_to_smt binders)))
                                                            0)))
                                                      (__eo_to_smt a)) =
                                                  SmtType.None
                                              exact
                                                smtx_typeof_apply_bvredor_head_none
                                                  (__eo_to_smt binders)
                                                  (__eo_to_smt a) hBindersNone
                                          · by_cases hBitwiseBvOp :
                                              q = Term.UOp UserOp.bvand ∨
                                                q = Term.UOp UserOp.bvor ∨
                                                q = Term.UOp UserOp.bvnand ∨
                                                q = Term.UOp UserOp.bvnor ∨
                                                q = Term.UOp UserOp.bvxor ∨
                                                q = Term.UOp UserOp.bvxnor ∨
                                                q = Term.UOp UserOp.bvcomp
                                            · rcases hBitwiseBvOp with
                                                hBvand | hBvor | hBvnand |
                                                hBvnor | hBvxor | hBvxnor |
                                                hBvcomp
                                              · subst q
                                                exfalso
                                                apply hNN
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.bvand
                                                        (__eo_to_smt binders)
                                                        (__eo_to_smt a)) =
                                                    SmtType.None
                                                exact smtx_typeof_bvand_first_arg_none
                                                  (__eo_to_smt binders)
                                                  (__eo_to_smt a) hBindersNone
                                              · subst q
                                                exfalso
                                                apply hNN
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.bvor
                                                        (__eo_to_smt binders)
                                                        (__eo_to_smt a)) =
                                                    SmtType.None
                                                exact smtx_typeof_bvor_first_arg_none
                                                  (__eo_to_smt binders)
                                                  (__eo_to_smt a) hBindersNone
                                              · subst q
                                                exfalso
                                                apply hNN
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.bvnand
                                                        (__eo_to_smt binders)
                                                        (__eo_to_smt a)) =
                                                    SmtType.None
                                                exact smtx_typeof_bvnand_first_arg_none
                                                  (__eo_to_smt binders)
                                                  (__eo_to_smt a) hBindersNone
                                              · subst q
                                                exfalso
                                                apply hNN
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.bvnor
                                                        (__eo_to_smt binders)
                                                        (__eo_to_smt a)) =
                                                    SmtType.None
                                                exact smtx_typeof_bvnor_first_arg_none
                                                  (__eo_to_smt binders)
                                                  (__eo_to_smt a) hBindersNone
                                              · subst q
                                                exfalso
                                                apply hNN
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.bvxor
                                                        (__eo_to_smt binders)
                                                        (__eo_to_smt a)) =
                                                    SmtType.None
                                                exact smtx_typeof_bvxor_first_arg_none
                                                  (__eo_to_smt binders)
                                                  (__eo_to_smt a) hBindersNone
                                              · subst q
                                                exfalso
                                                apply hNN
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.bvxnor
                                                        (__eo_to_smt binders)
                                                        (__eo_to_smt a)) =
                                                    SmtType.None
                                                exact smtx_typeof_bvxnor_first_arg_none
                                                  (__eo_to_smt binders)
                                                  (__eo_to_smt a) hBindersNone
                                              · subst q
                                                exfalso
                                                apply hNN
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.bvcomp
                                                        (__eo_to_smt binders)
                                                        (__eo_to_smt a)) =
                                                    SmtType.None
                                                exact smtx_typeof_bvcomp_first_arg_none
                                                  (__eo_to_smt binders)
                                                  (__eo_to_smt a) hBindersNone
                                            · by_cases hArithBvOp :
                                                q = Term.UOp UserOp.bvadd ∨
                                                  q = Term.UOp UserOp.bvmul ∨
                                                  q = Term.UOp UserOp.bvudiv ∨
                                                  q = Term.UOp UserOp.bvurem ∨
                                                  q = Term.UOp UserOp.bvsub ∨
                                                  q = Term.UOp UserOp.bvsdiv ∨
                                                  q = Term.UOp UserOp.bvsrem ∨
                                                  q = Term.UOp UserOp.bvsmod
                                              · rcases hArithBvOp with
                                                  hBvadd | hBvmul | hBvudiv |
                                                  hBvurem | hBvsub | hBvsdiv |
                                                  hBvsrem | hBvsmod
                                                · subst q
                                                  exfalso
                                                  apply hNN
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.bvadd
                                                          (__eo_to_smt binders)
                                                          (__eo_to_smt a)) =
                                                      SmtType.None
                                                  exact smtx_typeof_bvadd_first_arg_none
                                                    (__eo_to_smt binders)
                                                    (__eo_to_smt a) hBindersNone
                                                · subst q
                                                  exfalso
                                                  apply hNN
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.bvmul
                                                          (__eo_to_smt binders)
                                                          (__eo_to_smt a)) =
                                                      SmtType.None
                                                  exact smtx_typeof_bvmul_first_arg_none
                                                    (__eo_to_smt binders)
                                                    (__eo_to_smt a) hBindersNone
                                                · subst q
                                                  exfalso
                                                  apply hNN
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.bvudiv
                                                          (__eo_to_smt binders)
                                                          (__eo_to_smt a)) =
                                                      SmtType.None
                                                  exact smtx_typeof_bvudiv_first_arg_none
                                                    (__eo_to_smt binders)
                                                    (__eo_to_smt a) hBindersNone
                                                · subst q
                                                  exfalso
                                                  apply hNN
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.bvurem
                                                          (__eo_to_smt binders)
                                                          (__eo_to_smt a)) =
                                                      SmtType.None
                                                  exact smtx_typeof_bvurem_first_arg_none
                                                    (__eo_to_smt binders)
                                                    (__eo_to_smt a) hBindersNone
                                                · subst q
                                                  exfalso
                                                  apply hNN
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.bvsub
                                                          (__eo_to_smt binders)
                                                          (__eo_to_smt a)) =
                                                      SmtType.None
                                                  exact smtx_typeof_bvsub_first_arg_none
                                                    (__eo_to_smt binders)
                                                    (__eo_to_smt a) hBindersNone
                                                · subst q
                                                  exfalso
                                                  apply hNN
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.bvsdiv
                                                          (__eo_to_smt binders)
                                                          (__eo_to_smt a)) =
                                                      SmtType.None
                                                  exact smtx_typeof_bvsdiv_first_arg_none
                                                    (__eo_to_smt binders)
                                                    (__eo_to_smt a) hBindersNone
                                                · subst q
                                                  exfalso
                                                  apply hNN
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.bvsrem
                                                          (__eo_to_smt binders)
                                                          (__eo_to_smt a)) =
                                                      SmtType.None
                                                  exact smtx_typeof_bvsrem_first_arg_none
                                                    (__eo_to_smt binders)
                                                    (__eo_to_smt a) hBindersNone
                                                · subst q
                                                  exfalso
                                                  apply hNN
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.bvsmod
                                                          (__eo_to_smt binders)
                                                          (__eo_to_smt a)) =
                                                      SmtType.None
                                                  exact smtx_typeof_bvsmod_first_arg_none
                                                    (__eo_to_smt binders)
                                                    (__eo_to_smt a) hBindersNone
                                              · by_cases hShiftBvOp :
                                                  q = Term.UOp UserOp.bvshl ∨
                                                    q = Term.UOp UserOp.bvlshr ∨
                                                    q = Term.UOp UserOp.bvashr
                                                · exfalso
                                                  apply hNN
                                                  exact
                                                    smtx_typeof_eo_to_smt_apply_apply_bv_shift_head_none
                                                      q binders a hShiftBvOp
                                                      hBindersNone
                                                · by_cases hCompareBvOp :
                                                    q = Term.UOp UserOp.bvult ∨
                                                      q = Term.UOp UserOp.bvule ∨
                                                      q = Term.UOp UserOp.bvugt ∨
                                                      q = Term.UOp UserOp.bvuge ∨
                                                      q = Term.UOp UserOp.bvslt ∨
                                                      q = Term.UOp UserOp.bvsle ∨
                                                      q = Term.UOp UserOp.bvsgt ∨
                                                      q = Term.UOp UserOp.bvsge
                                                  · exfalso
                                                    apply hNN
                                                    exact
                                                      smtx_typeof_eo_to_smt_apply_apply_bv_compare_head_none
                                                        q binders a hCompareBvOp
                                                        hBindersNone
                                                  · by_cases hOverflowBvOp :
                                                      q = Term.UOp UserOp.bvuaddo ∨
                                                        q = Term.UOp UserOp.bvsaddo ∨
                                                        q = Term.UOp UserOp.bvumulo ∨
                                                        q = Term.UOp UserOp.bvsmulo ∨
                                                        q = Term.UOp UserOp.bvusubo ∨
                                                        q = Term.UOp UserOp.bvssubo ∨
                                                        q = Term.UOp UserOp.bvsdivo
                                                    · exfalso
                                                      apply hNN
                                                      exact
                                                        smtx_typeof_eo_to_smt_apply_apply_bv_overflow_head_none
                                                          q binders a
                                                          hOverflowBvOp
                                                          hBindersNone
                                                    · by_cases hPredToBvOp :
                                                        q = Term.UOp UserOp.bvultbv ∨
                                                          q = Term.UOp UserOp.bvsltbv
                                                      · exfalso
                                                        apply hNN
                                                        exact
                                                          smtx_typeof_eo_to_smt_apply_apply_bv_pred_to_bv_head_none
                                                            q binders a
                                                            hPredToBvOp
                                                            hBindersNone
                                                      · by_cases hDeqDiffOp :
                                                          q =
                                                              Term.UOp
                                                                UserOp._at_array_deq_diff ∨
                                                            q =
                                                              Term.UOp
                                                                UserOp._at_sets_deq_diff
                                                        · exfalso
                                                          apply hNN
                                                          exact
                                                            smtx_typeof_eo_to_smt_apply_apply_deq_diff_head_none
                                                              q binders a
                                                              hDeqDiffOp
                                                              hBindersNone
                                                        · by_cases
                                                            hStringsDeqDiffOp :
                                                            q =
                                                              Term.UOp
                                                                UserOp._at_strings_deq_diff
                                                          · subst q
                                                            exfalso
                                                            apply hNN
                                                            exact
                                                              smtx_typeof_eo_to_smt_apply_apply_strings_deq_diff_head_none
                                                                binders a
                                                                hBindersNone
                                                          · by_cases
                                                              hStringResultOp :
                                                              q =
                                                                  Term.UOp
                                                                    UserOp._at_strings_stoi_result ∨
                                                                q =
                                                                  Term.UOp
                                                                    UserOp._at_strings_itos_result ∨
                                                                q =
                                                                  Term.UOp
                                                                    UserOp._at_strings_num_occur
                                                            · exfalso
                                                              apply hNN
                                                              exact
                                                                smtx_typeof_eo_to_smt_apply_apply_string_result_head_none
                                                                  q binders a
                                                                  hStringResultOp
                                                                  hBindersNone
                                                            · by_cases
                                                                hTernaryMiddleOp :
                                                                ∃ z : Term,
                                                                  q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.ite)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.bvite)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.store)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.str_substr)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.str_replace)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.str_indexof)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.str_update)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.str_replace_all)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.str_replace_re)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.str_replace_re_all)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.str_indexof_re)
                                                                        z ∨
                                                                    q =
                                                                      Term.Apply
                                                                        (Term.UOp
                                                                          UserOp.str_indexof_re_split)
                                                                        z
                                                              · exfalso
                                                                apply hNN
                                                                exact
                                                                  smtx_typeof_eo_to_smt_apply_apply_ternary_middle_head_none
                                                                    q binders a
                                                                    hTernaryMiddleOp
                                                                    hBindersNone
                                                              · by_cases
                                                                  hIndexedUnaryOp :
                                                                  (∃ z : Term,
                                                                    q =
                                                                      Term.UOp1
                                                                        UserOp1.repeat
                                                                        z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.zero_extend
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.sign_extend
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.rotate_left
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.rotate_right
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1._at_bit
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.re_exp
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.int_to_bv
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.seq_empty
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.set_empty
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.is
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.tuple_select
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.update
                                                                          z) ∨
                                                                    (∃ z : Term,
                                                                      q =
                                                                        Term.UOp1
                                                                          UserOp1.tuple_update
                                                                          z)
                                                                · exfalso
                                                                  apply hNN
                                                                  exact
                                                                    smtx_typeof_eo_to_smt_apply_apply_indexed_unary_head_none
                                                                      q binders a
                                                                      hIndexedUnaryOp
                                                                      hBindersNone
                                                                · by_cases
                                                                    hUOp2 :
                                                                    ∃ op z w,
                                                                      q =
                                                                        Term.UOp2
                                                                          op z w
                                                                  · exfalso
                                                                    apply hNN
                                                                    exact
                                                                      smtx_typeof_eo_to_smt_apply_apply_uop2_head_none
                                                                        q binders a
                                                                        hUOp2
                                                                        hBindersNone
                                                                  · by_cases
                                                                      hUOp3 :
                                                                      ∃ op x y z,
                                                                        q =
                                                                          Term.UOp3
                                                                            op x y z
                                                                    · exfalso
                                                                      apply hNN
                                                                      exact
                                                                        smtx_typeof_eo_to_smt_apply_apply_uop3_head_none
                                                                          q binders a
                                                                          hUOp3
                                                                          hBindersNone
                                                                    · by_cases hDistinctOp :
                                                                        q =
                                                                          Term.UOp
                                                                            UserOp.distinct
                                                                      · subst q
                                                                        exfalso
                                                                        apply hNN
                                                                        exact
                                                                          smtx_typeof_eo_to_smt_apply_apply_distinct_head_none
                                                                            binders a
                                                                            (by
                                                                              dsimp [binders]
                                                                              simp [
                                                                                __eo_to_smt_typed_list_elem_type])
                                                                      · by_cases hBvsizeOp :
                                                                          q =
                                                                            Term.UOp
                                                                              UserOp._at_bvsize
                                                                        · subst q
                                                                          exfalso
                                                                          apply hNN
                                                                          exact
                                                                            smtx_typeof_eo_to_smt_apply_apply_bvsize_head_none
                                                                              binders a
                                                                              hBindersNone
                                                                        · by_cases
                                                                            hFromBoolsOp :
                                                                            q =
                                                                              Term.UOp
                                                                                UserOp._at_from_bools
                                                                          · subst q
                                                                            exfalso
                                                                            apply hNN
                                                                            exact
                                                                              smtx_typeof_eo_to_smt_apply_apply_from_bools_head_none
                                                                                binders a
                                                                                hBindersNone
                                                                          · by_cases
                                                                              hStoiNonDigitOp :
                                                                              q =
                                                                                Term.UOp
                                                                                  UserOp._at_strings_stoi_non_digit
                                                                            · subst q
                                                                              exfalso
                                                                              apply hNN
                                                                              change
                                                                                __smtx_typeof
                                                                                    (SmtTerm.Apply
                                                                                      (SmtTerm.str_indexof_re
                                                                                        (__eo_to_smt binders)
                                                                                        (SmtTerm.re_comp
                                                                                          (SmtTerm.re_range
                                                                                            (SmtTerm.String
                                                                                              (native_string_lit "0"))
                                                                                            (SmtTerm.String
                                                                                              (native_string_lit "9"))))
                                                                                        (SmtTerm.Numeral 0))
                                                                                      (__eo_to_smt a)) =
                                                                                  SmtType.None
                                                                              exact
                                                                                smtx_typeof_apply_str_indexof_re_head_none
                                                                                  (__eo_to_smt binders)
                                                                                  (SmtTerm.re_comp
                                                                                    (SmtTerm.re_range
                                                                                      (SmtTerm.String
                                                                                        (native_string_lit "0"))
                                                                                      (SmtTerm.String
                                                                                        (native_string_lit "9"))))
                                                                                  (SmtTerm.Numeral 0)
                                                                                  (__eo_to_smt a)
                                                                                  hBindersNone
                                                                            · by_cases hTupleOp :
                                                                                q =
                                                                                  Term.UOp
                                                                                    UserOp.tuple
                                                                              · subst q
                                                                                exfalso
                                                                                apply hNN
                                                                                change
                                                                                  __smtx_typeof
                                                                                      (__eo_to_smt_tuple_prepend
                                                                                        (__eo_to_smt binders)
                                                                                        (__smtx_typeof
                                                                                          (__eo_to_smt binders))
                                                                                        (__eo_to_smt a)) =
                                                                                    SmtType.None
                                                                                exact
                                                                                  smtx_typeof_eo_to_smt_tuple_prepend_head_none
                                                                                    (__eo_to_smt binders)
                                                                                    (__eo_to_smt a)
                                                                                    hBindersNone
                                                                              · by_cases
                                                                                  hSetMemberOp :
                                                                                  q =
                                                                                    Term.UOp
                                                                                      UserOp.set_member
                                                                                · subst q
                                                                                  exfalso
                                                                                  apply hNN
                                                                                  change
                                                                                    __smtx_typeof
                                                                                        (SmtTerm.set_member
                                                                                          (__eo_to_smt binders)
                                                                                          (__eo_to_smt a)) =
                                                                                      SmtType.None
                                                                                  exact
                                                                                    smtx_typeof_set_member_first_arg_none
                                                                                      (__eo_to_smt binders)
                                                                                      (__eo_to_smt a)
                                                                                      hBindersNone
                                                                                · cases q with
                                                                                  | UOp op =>
                                                                                      cases op <;>
                                                                                        first
                                                                                        | exfalso
                                                                                          apply hNN
                                                                                          exact
                                                                                            smtx_typeof_eo_to_smt_apply_apply_generic_head_none
                                                                                              _ binders a
                                                                                              (by
                                                                                                rfl)
                                                                                              hBindersNone
                                                                                        | exfalso
                                                                                          simp_all
                                                                                  | UOp1 op z =>
                                                                                      exfalso
                                                                                      cases op <;>
                                                                                        simp at hIndexedUnaryOp
                                                                                  | UOp2 op z w =>
                                                                                      exfalso
                                                                                      exact hUOp2
                                                                                        ⟨op, z, w, rfl⟩
                                                                                  | UOp3 op x y z =>
                                                                                      exfalso
                                                                                      exact hUOp3
                                                                                        ⟨op, x, y, z, rfl⟩
                                                                                  | Apply f z =>
                                                                                      by_cases
                                                                                        hBinaryArithApplyOp :
                                                                                        ∃ w : Term,
                                                                                          Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.plus)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.neg)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.mult)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.lt)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.leq)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.gt)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.geq)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.div)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.mod)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.multmult)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.divisible)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.div_total)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.mod_total)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.multmult_total)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.qdiv)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.qdiv_total)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.select)
                                                                                                w ∨
                                                                                            Term.Apply f z =
                                                                                              Term.Apply
                                                                                                (Term.UOp
                                                                                                  UserOp.concat)
                                                                                                w
                                                                                      · exfalso
                                                                                        apply hNN
                                                                                        exact
                                                                                          smtx_typeof_eo_to_smt_apply_apply_binary_arith_second_head_none
                                                                                            (Term.Apply f z)
                                                                                            binders a
                                                                                            hBinaryArithApplyOp
                                                                                            hBindersNone
                                                                                      · cases f with
                                                                                      | UOp op =>
                                                                                          by_cases
                                                                                            hBoolApplyOp :
                                                                                            op =
                                                                                                UserOp.or ∨
                                                                                              op =
                                                                                                UserOp.and ∨
                                                                                              op =
                                                                                                UserOp.imp ∨
                                                                                              op =
                                                                                                UserOp.xor ∨
                                                                                              op =
                                                                                                UserOp.eq
                                                                                          · rcases hBoolApplyOp with
                                                                                              hOr | hAnd | hImp | hXor | hEq
                                                                                            · subst op
                                                                                              exfalso
                                                                                              apply hNN
                                                                                              change
                                                                                                __smtx_typeof
                                                                                                    (SmtTerm.Apply
                                                                                                      (SmtTerm.or
                                                                                                        (__eo_to_smt z)
                                                                                                        (__eo_to_smt binders))
                                                                                                      (__eo_to_smt a)) =
                                                                                                  SmtType.None
                                                                                              apply
                                                                                                smtx_typeof_apply_head_none_of_non_datatype_head
                                                                                              · intro s d i j h
                                                                                                cases h
                                                                                              · intro s d i h
                                                                                                cases h
                                                                                              · exact
                                                                                                  smtx_typeof_or_second_arg_none
                                                                                                    (__eo_to_smt z)
                                                                                                    (__eo_to_smt binders)
                                                                                                    hBindersNone
                                                                                            · subst op
                                                                                              exfalso
                                                                                              apply hNN
                                                                                              change
                                                                                                __smtx_typeof
                                                                                                    (SmtTerm.Apply
                                                                                                      (SmtTerm.and
                                                                                                        (__eo_to_smt z)
                                                                                                        (__eo_to_smt binders))
                                                                                                      (__eo_to_smt a)) =
                                                                                                  SmtType.None
                                                                                              apply
                                                                                                smtx_typeof_apply_head_none_of_non_datatype_head
                                                                                              · intro s d i j h
                                                                                                cases h
                                                                                              · intro s d i h
                                                                                                cases h
                                                                                              · exact
                                                                                                  smtx_typeof_and_second_arg_none
                                                                                                    (__eo_to_smt z)
                                                                                                    (__eo_to_smt binders)
                                                                                                    hBindersNone
                                                                                            · subst op
                                                                                              exfalso
                                                                                              apply hNN
                                                                                              change
                                                                                                __smtx_typeof
                                                                                                    (SmtTerm.Apply
                                                                                                      (SmtTerm.imp
                                                                                                        (__eo_to_smt z)
                                                                                                        (__eo_to_smt binders))
                                                                                                      (__eo_to_smt a)) =
                                                                                                  SmtType.None
                                                                                              apply
                                                                                                smtx_typeof_apply_head_none_of_non_datatype_head
                                                                                              · intro s d i j h
                                                                                                cases h
                                                                                              · intro s d i h
                                                                                                cases h
                                                                                              · exact
                                                                                                  smtx_typeof_imp_second_arg_none
                                                                                                    (__eo_to_smt z)
                                                                                                    (__eo_to_smt binders)
                                                                                                    hBindersNone
                                                                                            · subst op
                                                                                              exfalso
                                                                                              apply hNN
                                                                                              change
                                                                                                __smtx_typeof
                                                                                                    (SmtTerm.Apply
                                                                                                      (SmtTerm.xor
                                                                                                        (__eo_to_smt z)
                                                                                                        (__eo_to_smt binders))
                                                                                                      (__eo_to_smt a)) =
                                                                                                  SmtType.None
                                                                                              apply
                                                                                                smtx_typeof_apply_head_none_of_non_datatype_head
                                                                                              · intro s d i j h
                                                                                                cases h
                                                                                              · intro s d i h
                                                                                                cases h
                                                                                              · exact
                                                                                                  smtx_typeof_xor_second_arg_none
                                                                                                    (__eo_to_smt z)
                                                                                                    (__eo_to_smt binders)
                                                                                                    hBindersNone
                                                                                            · subst op
                                                                                              exfalso
                                                                                              apply hNN
                                                                                              change
                                                                                                __smtx_typeof
                                                                                                    (SmtTerm.Apply
                                                                                                      (SmtTerm.eq
                                                                                                        (__eo_to_smt z)
                                                                                                        (__eo_to_smt binders))
                                                                                                      (__eo_to_smt a)) =
                                                                                                  SmtType.None
                                                                                              apply
                                                                                                smtx_typeof_apply_head_none_of_non_datatype_head
                                                                                              · intro s d i j h
                                                                                                cases h
                                                                                              · intro s d i h
                                                                                                cases h
                                                                                              · exact
                                                                                                  smtx_typeof_eq_second_arg_none
                                                                                                    (__eo_to_smt z)
                                                                                                    (__eo_to_smt binders)
                                                                                                    hBindersNone
                                                                                          · by_cases
                                                                                              hBinarySeqSetApplyOp :
                                                                                              ∃ w : Term,
                                                                                                Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.str_concat) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.str_contains) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.str_at) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.str_prefixof) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.str_suffixof) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.str_lt) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.str_leq) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.re_range) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.re_concat) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.re_inter) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.re_union) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.re_diff) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.str_in_re) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.seq_nth) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.set_union) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.set_inter) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.set_minus) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.set_member) w ∨
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                    Term.Apply (Term.UOp UserOp.set_subset) w
                                                                                            · exfalso
                                                                                              apply hNN
                                                                                              exact
                                                                                                smtx_typeof_eo_to_smt_apply_apply_binary_seq_set_second_head_none
                                                                                                  (Term.Apply (Term.UOp op) z)
                                                                                                  binders a
                                                                                                  hBinarySeqSetApplyOp
                                                                                                  hBindersNone
                                                                                            · by_cases
                                                                                                hBinaryBvBitwiseApplyOp :
                                                                                                ∃ w : Term,
                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                      Term.Apply (Term.UOp UserOp.bvand) w ∨
                                                                                                    Term.Apply (Term.UOp op) z =
                                                                                                      Term.Apply (Term.UOp UserOp.bvor) w ∨
                                                                                                    Term.Apply (Term.UOp op) z =
                                                                                                      Term.Apply (Term.UOp UserOp.bvnand) w ∨
                                                                                                    Term.Apply (Term.UOp op) z =
                                                                                                      Term.Apply (Term.UOp UserOp.bvnor) w ∨
                                                                                                    Term.Apply (Term.UOp op) z =
                                                                                                      Term.Apply (Term.UOp UserOp.bvxor) w ∨
                                                                                                    Term.Apply (Term.UOp op) z =
                                                                                                      Term.Apply (Term.UOp UserOp.bvxnor) w ∨
                                                                                                    Term.Apply (Term.UOp op) z =
                                                                                                      Term.Apply (Term.UOp UserOp.bvcomp) w
                                                                                              · exfalso
                                                                                                apply hNN
                                                                                                exact
                                                                                                  smtx_typeof_eo_to_smt_apply_apply_bv_bitwise_second_head_none
                                                                                                    (Term.Apply (Term.UOp op) z)
                                                                                                    binders a
                                                                                                    hBinaryBvBitwiseApplyOp
                                                                                                    hBindersNone
                                                                                              · by_cases
                                                                                                  hBinaryBvArithShiftApplyOp :
                                                                                                  ∃ w : Term,
                                                                                                    Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvadd) w ∨
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvmul) w ∨
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvudiv) w ∨
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvurem) w ∨
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvsub) w ∨
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvsdiv) w ∨
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvsrem) w ∨
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvsmod) w ∨
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvshl) w ∨
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvlshr) w ∨
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                        Term.Apply (Term.UOp UserOp.bvashr) w
                                                                                                · exfalso
                                                                                                  apply hNN
                                                                                                  exact
                                                                                                    smtx_typeof_eo_to_smt_apply_apply_bv_arith_shift_second_head_none
                                                                                                      (Term.Apply (Term.UOp op) z)
                                                                                                      binders a
                                                                                                      hBinaryBvArithShiftApplyOp
                                                                                                      hBindersNone
                                                                                                · by_cases
                                                                                                    hBinaryBvCompareApplyOp :
                                                                                                    ∃ w : Term,
                                                                                                      Term.Apply (Term.UOp op) z =
                                                                                                          Term.Apply (Term.UOp UserOp.bvult) w ∨
                                                                                                        Term.Apply (Term.UOp op) z =
                                                                                                          Term.Apply (Term.UOp UserOp.bvule) w ∨
                                                                                                        Term.Apply (Term.UOp op) z =
                                                                                                          Term.Apply (Term.UOp UserOp.bvugt) w ∨
                                                                                                        Term.Apply (Term.UOp op) z =
                                                                                                          Term.Apply (Term.UOp UserOp.bvuge) w ∨
                                                                                                        Term.Apply (Term.UOp op) z =
                                                                                                          Term.Apply (Term.UOp UserOp.bvslt) w ∨
                                                                                                        Term.Apply (Term.UOp op) z =
                                                                                                          Term.Apply (Term.UOp UserOp.bvsle) w ∨
                                                                                                        Term.Apply (Term.UOp op) z =
                                                                                                          Term.Apply (Term.UOp UserOp.bvsgt) w ∨
                                                                                                        Term.Apply (Term.UOp op) z =
                                                                                                          Term.Apply (Term.UOp UserOp.bvsge) w
                                                                                                  · exfalso
                                                                                                    apply hNN
                                                                                                    exact
                                                                                                      smtx_typeof_eo_to_smt_apply_apply_bv_compare_second_head_none
                                                                                                        (Term.Apply (Term.UOp op) z)
                                                                                                        binders a
                                                                                                        hBinaryBvCompareApplyOp
                                                                                                        hBindersNone
                                                                                                  · by_cases
                                                                                                      hBinaryBvOverflowApplyOp :
                                                                                                      ∃ w : Term,
                                                                                                        Term.Apply (Term.UOp op) z =
                                                                                                            Term.Apply (Term.UOp UserOp.bvuaddo) w ∨
                                                                                                          Term.Apply (Term.UOp op) z =
                                                                                                            Term.Apply (Term.UOp UserOp.bvsaddo) w ∨
                                                                                                          Term.Apply (Term.UOp op) z =
                                                                                                            Term.Apply (Term.UOp UserOp.bvumulo) w ∨
                                                                                                          Term.Apply (Term.UOp op) z =
                                                                                                            Term.Apply (Term.UOp UserOp.bvsmulo) w ∨
                                                                                                          Term.Apply (Term.UOp op) z =
                                                                                                            Term.Apply (Term.UOp UserOp.bvusubo) w ∨
                                                                                                          Term.Apply (Term.UOp op) z =
                                                                                                            Term.Apply (Term.UOp UserOp.bvssubo) w ∨
                                                                                                          Term.Apply (Term.UOp op) z =
                                                                                                            Term.Apply (Term.UOp UserOp.bvsdivo) w
                                                                                                    · exfalso
                                                                                                      apply hNN
                                                                                                      exact
                                                                                                        smtx_typeof_eo_to_smt_apply_apply_bv_overflow_second_head_none
                                                                                                          (Term.Apply (Term.UOp op) z)
                                                                                                          binders a
                                                                                                          hBinaryBvOverflowApplyOp
                                                                                                          hBindersNone
                                                                                                    · by_cases
                                                                                                        hBinaryBvPredToBvApplyOp :
                                                                                                        ∃ w : Term,
                                                                                                          Term.Apply (Term.UOp op) z =
                                                                                                              Term.Apply (Term.UOp UserOp.bvultbv) w ∨
                                                                                                            Term.Apply (Term.UOp op) z =
                                                                                                              Term.Apply (Term.UOp UserOp.bvsltbv) w
                                                                                                      · exfalso
                                                                                                        apply hNN
                                                                                                        exact
                                                                                                          smtx_typeof_eo_to_smt_apply_apply_bv_pred_to_bv_second_head_none
                                                                                                            (Term.Apply (Term.UOp op) z)
                                                                                                            binders a
                                                                                                            hBinaryBvPredToBvApplyOp
                                                                                                            hBindersNone
                                                                                                      · by_cases
                                                                                                          hMiscSecondApplyOp :
                                                                                                          ∃ w : Term,
                                                                                                            Term.Apply (Term.UOp op) z =
                                                                                                                Term.Apply
                                                                                                                  (Term.UOp
                                                                                                                    UserOp._at_from_bools)
                                                                                                                  w ∨
                                                                                                              Term.Apply (Term.UOp op) z =
                                                                                                                Term.Apply
                                                                                                                  (Term.UOp
                                                                                                                    UserOp._at_array_deq_diff)
                                                                                                                  w ∨
                                                                                                              Term.Apply (Term.UOp op) z =
                                                                                                                Term.Apply
                                                                                                                  (Term.UOp
                                                                                                                    UserOp._at_sets_deq_diff)
                                                                                                                  w ∨
                                                                                                              Term.Apply (Term.UOp op) z =
                                                                                                                Term.Apply
                                                                                                                  (Term.UOp
                                                                                                                    UserOp._at_strings_deq_diff)
                                                                                                                  w ∨
                                                                                                              Term.Apply (Term.UOp op) z =
                                                                                                                Term.Apply
                                                                                                                  (Term.UOp
                                                                                                                    UserOp._at_strings_stoi_result)
                                                                                                                  w ∨
                                                                                                              Term.Apply (Term.UOp op) z =
                                                                                                                Term.Apply
                                                                                                                  (Term.UOp
                                                                                                                    UserOp._at_strings_itos_result)
                                                                                                                  w ∨
                                                                                                              Term.Apply (Term.UOp op) z =
                                                                                                                Term.Apply
                                                                                                                  (Term.UOp
                                                                                                                    UserOp._at_strings_num_occur)
                                                                                                                  w
                                                                                                        · exfalso
                                                                                                          apply hNN
                                                                                                          exact
                                                                                                            smtx_typeof_eo_to_smt_apply_apply_misc_second_head_none
                                                                                                              (Term.Apply (Term.UOp op) z)
                                                                                                              binders a
                                                                                                              hMiscSecondApplyOp
                                                                                                              hBindersNone
                                                                                                        · by_cases
                                                                                                            hTupleSecondApplyOp :
                                                                                                            ∃ w : Term,
                                                                                                              Term.Apply (Term.UOp op) z =
                                                                                                                Term.Apply
                                                                                                                  (Term.UOp UserOp.tuple)
                                                                                                                  w
                                                                                                          · exfalso
                                                                                                            apply hNN
                                                                                                            exact
                                                                                                              smtx_typeof_eo_to_smt_apply_apply_tuple_second_head_none
                                                                                                                (Term.Apply (Term.UOp op) z)
                                                                                                                binders a
                                                                                                                hTupleSecondApplyOp
                                                                                                                hBindersNone
                                                                                                          · by_cases
                                                                                                              hSetInsertSecondApplyOp :
                                                                                                              ∃ w : Term,
                                                                                                                Term.Apply (Term.UOp op) z =
                                                                                                                  Term.Apply
                                                                                                                    (Term.UOp
                                                                                                                      UserOp.set_insert)
                                                                                                                    w
                                                                                                            · exfalso
                                                                                                              apply hNN
                                                                                                              exact
                                                                                                                smtx_typeof_eo_to_smt_apply_apply_set_insert_second_head_none
                                                                                                                  (Term.Apply (Term.UOp op) z)
                                                                                                                  binders a
                                                                                                                  hSetInsertSecondApplyOp
                                                                                                                  hBindersNone
                                                                                                                  (by
                                                                                                                    dsimp [binders]
                                                                                                                    intro s d i j h
                                                                                                                    cases h)
                                                                                                                  (by
                                                                                                                    dsimp [binders]
                                                                                                                    intro s d i h
                                                                                                                    cases h)
                                                                                                            · by_cases
                                                                                                                hQuantSecondApplyOp :
                                                                                                                ∃ w : Term,
                                                                                                                  Term.Apply (Term.UOp op) z =
                                                                                                                      Term.Apply
                                                                                                                        (Term.UOp
                                                                                                                          UserOp.forall)
                                                                                                                        w ∨
                                                                                                                    Term.Apply (Term.UOp op) z =
                                                                                                                      Term.Apply
                                                                                                                        (Term.UOp
                                                                                                                          UserOp.exists)
                                                                                                                        w
                                                                                                              · exfalso
                                                                                                                apply hNN
                                                                                                                exact
                                                                                                                  smtx_typeof_eo_to_smt_apply_apply_quant_second_head_none
                                                                                                                    (Term.Apply (Term.UOp op) z)
                                                                                                                    binders a
                                                                                                                    hQuantSecondApplyOp
                                                                                                                    hBindersNone
                                                                                                                    (by
                                                                                                                      dsimp [binders]
                                                                                                                      intro s d i j h
                                                                                                                      cases h)
                                                                                                                    (by
                                                                                                                      dsimp [binders]
                                                                                                                      intro s d i h
                                                                                                                      cases h)
                                                                                                              · exfalso
                                                                                                                apply hNN
                                                                                                                exact
                                                                                                                  smtx_typeof_eo_to_smt_apply_apply_generic_head_none
                                                                                                                    (Term.Apply (Term.UOp op) z)
                                                                                                                    binders a
                                                                                                                    (by
                                                                                                                      cases op <;>
                                                                                                                        first
                                                                                                                        | rfl
                                                                                                                        | simp_all)
                                                                                                                    hBindersNone
                                                                                      | UOp1 op idx =>
                                                                                          by_cases
                                                                                            hUpdate :
                                                                                            op =
                                                                                              UserOp1.update
                                                                                          · subst op
                                                                                            exfalso
                                                                                            apply hNN
                                                                                            exact
                                                                                              smtx_typeof_eo_to_smt_apply_apply_uop1_update_second_head_none
                                                                                                idx z binders a
                                                                                                hBindersNone
                                                                                          · by_cases
                                                                                              hTupleUpdate :
                                                                                              op =
                                                                                                UserOp1.tuple_update
                                                                                            · subst op
                                                                                              exfalso
                                                                                              apply hNN
                                                                                              exact
                                                                                                smtx_typeof_eo_to_smt_apply_apply_uop1_tuple_update_second_head_none
                                                                                                  idx z binders a
                                                                                                  hBindersNone
                                                                                            · cases op <;>
                                                                                                first
                                                                                                | contradiction
                                                                                                | exfalso
                                                                                                  apply hNN
                                                                                                  exact
                                                                                                    smtx_typeof_eo_to_smt_apply_apply_generic_head_none
                                                                                                      _ binders a
                                                                                                      (by
                                                                                                        rfl)
                                                                                                      hBindersNone
                                                                                      | Apply g y =>
                                                                                          by_cases
                                                                                            hTernaryLastOp :
                                                                                            ∃ u v : Term,
                                                                                              Term.Apply
                                                                                                    (Term.Apply g y)
                                                                                                    z =
                                                                                                  Term.Apply
                                                                                                    (Term.Apply
                                                                                                      (Term.UOp
                                                                                                        UserOp.ite)
                                                                                                      u)
                                                                                                    v ∨
                                                                                                Term.Apply
                                                                                                      (Term.Apply g y)
                                                                                                      z =
                                                                                                    Term.Apply
                                                                                                      (Term.Apply
                                                                                                        (Term.UOp
                                                                                                          UserOp.bvite)
                                                                                                        u)
                                                                                                      v ∨
                                                                                                  Term.Apply
                                                                                                        (Term.Apply g y)
                                                                                                        z =
                                                                                                      Term.Apply
                                                                                                        (Term.Apply
                                                                                                          (Term.UOp
                                                                                                            UserOp.store)
                                                                                                          u)
                                                                                                        v ∨
                                                                                                    Term.Apply
                                                                                                          (Term.Apply g y)
                                                                                                          z =
                                                                                                        Term.Apply
                                                                                                          (Term.Apply
                                                                                                            (Term.UOp
                                                                                                              UserOp.str_substr)
                                                                                                            u)
                                                                                                          v ∨
                                                                                                      Term.Apply
                                                                                                            (Term.Apply g y)
                                                                                                            z =
                                                                                                          Term.Apply
                                                                                                            (Term.Apply
                                                                                                              (Term.UOp
                                                                                                                UserOp.str_replace)
                                                                                                              u)
                                                                                                            v ∨
                                                                                                        Term.Apply
                                                                                                              (Term.Apply g y)
                                                                                                              z =
                                                                                                            Term.Apply
                                                                                                              (Term.Apply
                                                                                                                (Term.UOp
                                                                                                                  UserOp.str_indexof)
                                                                                                                u)
                                                                                                              v ∨
                                                                                                          Term.Apply
                                                                                                                (Term.Apply g y)
                                                                                                                z =
                                                                                                              Term.Apply
                                                                                                                (Term.Apply
                                                                                                                  (Term.UOp
                                                                                                                    UserOp.str_update)
                                                                                                                  u)
                                                                                                                v ∨
                                                                                                            Term.Apply
                                                                                                                  (Term.Apply g y)
                                                                                                                  z =
                                                                                                                Term.Apply
                                                                                                                  (Term.Apply
                                                                                                                    (Term.UOp
                                                                                                                      UserOp.str_replace_all)
                                                                                                                    u)
                                                                                                                  v ∨
                                                                                                              Term.Apply
                                                                                                                    (Term.Apply g y)
                                                                                                                    z =
                                                                                                                  Term.Apply
                                                                                                                    (Term.Apply
                                                                                                                      (Term.UOp
                                                                                                                        UserOp.str_replace_re)
                                                                                                                      u)
                                                                                                                    v ∨
                                                                                                                Term.Apply
                                                                                                                      (Term.Apply g y)
                                                                                                                      z =
                                                                                                                    Term.Apply
                                                                                                                      (Term.Apply
                                                                                                                        (Term.UOp
                                                                                                                          UserOp.str_replace_re_all)
                                                                                                                        u)
                                                                                                                      v ∨
                                                                                                                  Term.Apply
                                                                                                                        (Term.Apply g y)
                                                                                                                        z =
                                                                                                                      Term.Apply
                                                                                                                        (Term.Apply
                                                                                                                          (Term.UOp
                                                                                                                            UserOp.str_indexof_re)
                                                                                                                          u)
                                                                                                                        v ∨
                                                                                                                    Term.Apply
                                                                                                                          (Term.Apply g y)
                                                                                                                          z =
                                                                                                                        Term.Apply
                                                                                                                          (Term.Apply
                                                                                                                            (Term.UOp
                                                                                                                              UserOp.str_indexof_re_split)
                                                                                                                            u)
                                                                                                                          v
                                                                                          · exfalso
                                                                                            apply hNN
                                                                                            exact
                                                                                              smtx_typeof_eo_to_smt_apply_apply_ternary_last_head_none
                                                                                                (Term.Apply
                                                                                                  (Term.Apply g y)
                                                                                                  z)
                                                                                                binders a
                                                                                                hTernaryLastOp
                                                                                                hBindersNone
                                                                                          · exfalso
                                                                                            apply hNN
                                                                                            exact
                                                                                              smtx_typeof_eo_to_smt_apply_apply_generic_head_none
                                                                                                (Term.Apply
                                                                                                  (Term.Apply g y)
                                                                                                  z)
                                                                                                binders a
                                                                                                (by
                                                                                                  cases g with
                                                                                                  | UOp op =>
                                                                                                      cases op
                                                                                                      case ite =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case bvite =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case store =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case str_substr =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case str_replace =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case str_indexof =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case str_update =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case str_replace_all =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case str_replace_re =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case str_replace_re_all =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case str_indexof_re =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      case str_indexof_re_split =>
                                                                                                        exfalso
                                                                                                        apply hTernaryLastOp
                                                                                                        exact ⟨y, z, by simp⟩
                                                                                                      all_goals rfl
                                                                                                  | _ =>
                                                                                                      rfl)
                                                                                                hBindersNone
                                                                                      | _ =>
                                                                                          exfalso
                                                                                          apply hNN
                                                                                          exact
                                                                                            smtx_typeof_eo_to_smt_apply_apply_generic_head_none
                                                                                              _ binders a
                                                                                              (by
                                                                                                rfl)
                                                                                              hBindersNone
                                                                                  | _ =>
                                                                                      exfalso
                                                                                      apply hNN
                                                                                      exact
                                                                                        smtx_typeof_eo_to_smt_apply_apply_generic_head_none
                                                                                          _ binders a
                                                                                          (by
                                                                                            rfl)
                                                                                          hBindersNone
  | case5 f a xs bvs hXs hBvs hNotQuant ihF ihA =>
      intro hBvsVar M N hRel hScan hNN
      have hScan' :
          __eo_ite (__contains_atomic_term_list_free_rec f xs bvs)
              (Term.Boolean true)
              (__contains_atomic_term_list_free_rec a xs bvs) =
            Term.Boolean false := by
        simpa [__contains_atomic_term_list_free_rec] using hScan
      rcases eo_ite_true_branch_eq_false_cases
          (__contains_atomic_term_list_free_rec f xs bvs)
          (__contains_atomic_term_list_free_rec a xs bvs) hScan' with
        ⟨hFScan, hAScan⟩
      by_cases hWholeNone :
          __eo_to_smt (Term.Apply f a) = SmtTerm.None
      · exfalso
        apply hNN
        rw [hWholeNone]
        exact TranslationProofs.smtx_typeof_none
      · by_cases hGeneric :
            __eo_to_smt (Term.Apply f a) =
              SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)
        · by_cases hFNN :
              __smtx_typeof (__eo_to_smt f) ≠ SmtType.None
          · have hANN :
                __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
              intro hArgNone
              apply hNN
              rw [hGeneric]
              exact smtx_typeof_apply_arg_none
                (__eo_to_smt f) (__eo_to_smt a) hArgNone
            have hFEval :
                __smtx_model_eval M (__eo_to_smt f) =
                  __smtx_model_eval N (__eo_to_smt f) :=
              ihF hBvsVar M N hRel hFScan hFNN
            have hAEval :
                __smtx_model_eval M (__eo_to_smt a) =
                  __smtx_model_eval N (__eo_to_smt a) :=
              ihA hBvsVar M N hRel hAScan hANN
            rw [hGeneric]
            exact smtx_model_eval_apply_eq_of_eval_eq_of_globals
              hRel.globals (__eo_to_smt f) (__eo_to_smt a)
              hFEval hAEval
          · by_cases hSelHead :
              ∃ s d i j, __eo_to_smt f = SmtTerm.DtSel s d i j
            · rcases hSelHead with ⟨s, d, i, j, hSelEq⟩
              have hANN :
                  __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                intro hArgNone
                apply hNN
                rw [hGeneric]
                exact smtx_typeof_apply_arg_none
                  (__eo_to_smt f) (__eo_to_smt a) hArgNone
              have hFEval :
                  __smtx_model_eval M (__eo_to_smt f) =
                    __smtx_model_eval N (__eo_to_smt f) := by
                rw [hSelEq]
                simp [__smtx_model_eval]
              have hAEval :
                  __smtx_model_eval M (__eo_to_smt a) =
                    __smtx_model_eval N (__eo_to_smt a) :=
                ihA hBvsVar M N hRel hAScan hANN
              rw [hGeneric]
              exact smtx_model_eval_apply_eq_of_eval_eq_of_globals
                hRel.globals (__eo_to_smt f) (__eo_to_smt a)
                hFEval hAEval
            · by_cases hTesterHead :
                ∃ s d i, __eo_to_smt f = SmtTerm.DtTester s d i
              · rcases hTesterHead with ⟨s, d, i, hTesterEq⟩
                have hANN :
                    __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                  intro hArgNone
                  apply hNN
                  rw [hGeneric]
                  exact smtx_typeof_apply_arg_none
                    (__eo_to_smt f) (__eo_to_smt a) hArgNone
                have hFEval :
                    __smtx_model_eval M (__eo_to_smt f) =
                      __smtx_model_eval N (__eo_to_smt f) := by
                  rw [hTesterEq]
                  simp [__smtx_model_eval]
                have hAEval :
                    __smtx_model_eval M (__eo_to_smt a) =
                      __smtx_model_eval N (__eo_to_smt a) :=
                  ihA hBvsVar M N hRel hAScan hANN
                rw [hGeneric]
                exact smtx_model_eval_apply_eq_of_eval_eq_of_globals
                  hRel.globals (__eo_to_smt f) (__eo_to_smt a)
                  hFEval hAEval
              · exfalso
                apply hFNN
                apply smtx_typeof_apply_head_non_none_of_generic_non_none
                · intro s d i j hEq
                  exact hSelHead ⟨s, d, i, j, hEq⟩
                · intro s d i hEq
                  exact hTesterHead ⟨s, d, i, hEq⟩
                · intro hAppNone
                  apply hNN
                  rw [hGeneric]
                  exact hAppNone
        · by_cases hFNot : f = Term.UOp UserOp.not
          · subst f
            have hANN :
                __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
              intro hArgNone
              apply hNN
              change
                __smtx_typeof (SmtTerm.not (__eo_to_smt a)) =
                  SmtType.None
              exact smtx_typeof_not_arg_none (__eo_to_smt a) hArgNone
            have hAEval :
                __smtx_model_eval M (__eo_to_smt a) =
                  __smtx_model_eval N (__eo_to_smt a) :=
              ihA hBvsVar M N hRel hAScan hANN
            change
              __smtx_model_eval M (SmtTerm.not (__eo_to_smt a)) =
                __smtx_model_eval N (SmtTerm.not (__eo_to_smt a))
            exact smtx_model_eval_not_eq_of_eval_eq hAEval
          · by_cases hFPurify : f = Term.UOp UserOp._at_purify
            · subst f
              have hANN :
                  __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                intro hArgNone
                apply hNN
                change
                  __smtx_typeof
                      (SmtTerm._at_purify (__eo_to_smt a)) =
                    SmtType.None
                simpa [__smtx_typeof] using hArgNone
              have hAEval :
                  __smtx_model_eval M (__eo_to_smt a) =
                    __smtx_model_eval N (__eo_to_smt a) :=
                ihA hBvsVar M N hRel hAScan hANN
              change
                __smtx_model_eval M
                    (SmtTerm._at_purify (__eo_to_smt a)) =
                  __smtx_model_eval N
                    (SmtTerm._at_purify (__eo_to_smt a))
              simpa [__smtx_model_eval, __smtx_model_eval__at_purify]
                using congrArg __smtx_model_eval__at_purify hAEval
            · by_cases hFToReal : f = Term.UOp UserOp.to_real
              · subst f
                have hANN :
                    __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                  intro hArgNone
                  apply hNN
                  change
                    __smtx_typeof (SmtTerm.to_real (__eo_to_smt a)) =
                      SmtType.None
                  rw [typeof_to_real_eq, hArgNone]
                  rfl
                have hAEval :
                    __smtx_model_eval M (__eo_to_smt a) =
                      __smtx_model_eval N (__eo_to_smt a) :=
                  ihA hBvsVar M N hRel hAScan hANN
                change
                  __smtx_model_eval M (SmtTerm.to_real (__eo_to_smt a)) =
                    __smtx_model_eval N (SmtTerm.to_real (__eo_to_smt a))
                simpa [__smtx_model_eval, hAEval]
              · by_cases hFToInt : f = Term.UOp UserOp.to_int
                · subst f
                  have hANN :
                      __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                    intro hArgNone
                    apply hNN
                    change
                      __smtx_typeof (SmtTerm.to_int (__eo_to_smt a)) =
                        SmtType.None
                    rw [typeof_to_int_eq, hArgNone]
                    rfl
                  have hAEval :
                      __smtx_model_eval M (__eo_to_smt a) =
                        __smtx_model_eval N (__eo_to_smt a) :=
                    ihA hBvsVar M N hRel hAScan hANN
                  change
                    __smtx_model_eval M (SmtTerm.to_int (__eo_to_smt a)) =
                      __smtx_model_eval N (SmtTerm.to_int (__eo_to_smt a))
                  simpa [__smtx_model_eval, hAEval]
                · by_cases hFIsInt : f = Term.UOp UserOp.is_int
                  · subst f
                    have hANN :
                        __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                      intro hArgNone
                      apply hNN
                      change
                        __smtx_typeof (SmtTerm.is_int (__eo_to_smt a)) =
                          SmtType.None
                      rw [typeof_is_int_eq, hArgNone]
                      rfl
                    have hAEval :
                        __smtx_model_eval M (__eo_to_smt a) =
                          __smtx_model_eval N (__eo_to_smt a) :=
                      ihA hBvsVar M N hRel hAScan hANN
                    change
                      __smtx_model_eval M (SmtTerm.is_int (__eo_to_smt a)) =
                        __smtx_model_eval N (SmtTerm.is_int (__eo_to_smt a))
                    simpa [__smtx_model_eval, hAEval]
                  · by_cases hFAbs : f = Term.UOp UserOp.abs
                    · subst f
                      have hANN :
                          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                        intro hArgNone
                        apply hNN
                        change
                          __smtx_typeof (SmtTerm.abs (__eo_to_smt a)) =
                            SmtType.None
                        rw [typeof_abs_eq, hArgNone]
                        rfl
                      have hAEval :
                          __smtx_model_eval M (__eo_to_smt a) =
                            __smtx_model_eval N (__eo_to_smt a) :=
                        ihA hBvsVar M N hRel hAScan hANN
                      change
                        __smtx_model_eval M (SmtTerm.abs (__eo_to_smt a)) =
                          __smtx_model_eval N (SmtTerm.abs (__eo_to_smt a))
                      simpa [__smtx_model_eval, hAEval]
                    · by_cases hFUneg :
                        f = Term.UOp UserOp.__eoo_neg_2
                      · subst f
                        have hANN :
                            __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                          intro hArgNone
                          apply hNN
                          change
                            __smtx_typeof (SmtTerm.uneg (__eo_to_smt a)) =
                              SmtType.None
                          rw [typeof_uneg_eq, hArgNone]
                          rfl
                        have hAEval :
                            __smtx_model_eval M (__eo_to_smt a) =
                              __smtx_model_eval N (__eo_to_smt a) :=
                          ihA hBvsVar M N hRel hAScan hANN
                        change
                          __smtx_model_eval M
                              (SmtTerm.uneg (__eo_to_smt a)) =
                            __smtx_model_eval N
                              (SmtTerm.uneg (__eo_to_smt a))
                        simpa [__smtx_model_eval, hAEval]
                      · by_cases hFIntPow2 :
                          f = Term.UOp UserOp.int_pow2
                        · subst f
                          have hANN :
                              __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                            intro hArgNone
                            apply hNN
                            change
                              __smtx_typeof
                                  (SmtTerm.int_pow2 (__eo_to_smt a)) =
                                SmtType.None
                            rw [typeof_int_pow2_eq, hArgNone]
                            rfl
                          have hAEval :
                              __smtx_model_eval M (__eo_to_smt a) =
                                __smtx_model_eval N (__eo_to_smt a) :=
                            ihA hBvsVar M N hRel hAScan hANN
                          change
                            __smtx_model_eval M
                                (SmtTerm.int_pow2 (__eo_to_smt a)) =
                              __smtx_model_eval N
                                (SmtTerm.int_pow2 (__eo_to_smt a))
                          simpa [__smtx_model_eval, hAEval]
                        · by_cases hFIntLog2 :
                            f = Term.UOp UserOp.int_log2
                          · subst f
                            have hANN :
                                __smtx_typeof (__eo_to_smt a) ≠
                                  SmtType.None := by
                              intro hArgNone
                              apply hNN
                              change
                                __smtx_typeof
                                    (SmtTerm.int_log2 (__eo_to_smt a)) =
                                  SmtType.None
                              rw [typeof_int_log2_eq, hArgNone]
                              rfl
                            have hAEval :
                                __smtx_model_eval M (__eo_to_smt a) =
                                  __smtx_model_eval N (__eo_to_smt a) :=
                              ihA hBvsVar M N hRel hAScan hANN
                            change
                              __smtx_model_eval M
                                  (SmtTerm.int_log2 (__eo_to_smt a)) =
                                __smtx_model_eval N
                                  (SmtTerm.int_log2 (__eo_to_smt a))
                            simpa [__smtx_model_eval, hAEval]
                          · by_cases hFStrLen :
                              f = Term.UOp UserOp.str_len
                            · subst f
                              have hANN :
                                  __smtx_typeof (__eo_to_smt a) ≠
                                    SmtType.None := by
                                intro hArgNone
                                apply hNN
                                change
                                  __smtx_typeof
                                      (SmtTerm.str_len (__eo_to_smt a)) =
                                    SmtType.None
                                rw [typeof_str_len_eq, hArgNone]
                                rfl
                              have hAEval :
                                  __smtx_model_eval M (__eo_to_smt a) =
                                    __smtx_model_eval N (__eo_to_smt a) :=
                                ihA hBvsVar M N hRel hAScan hANN
                              change
                                __smtx_model_eval M
                                    (SmtTerm.str_len (__eo_to_smt a)) =
                                  __smtx_model_eval N
                                    (SmtTerm.str_len (__eo_to_smt a))
                              simpa [__smtx_model_eval, hAEval]
                            · by_cases hFStrRev :
                                f = Term.UOp UserOp.str_rev
                              · subst f
                                have hANN :
                                    __smtx_typeof (__eo_to_smt a) ≠
                                      SmtType.None := by
                                  intro hArgNone
                                  apply hNN
                                  change
                                    __smtx_typeof
                                        (SmtTerm.str_rev (__eo_to_smt a)) =
                                      SmtType.None
                                  rw [typeof_str_rev_eq, hArgNone]
                                  rfl
                                have hAEval :
                                    __smtx_model_eval M (__eo_to_smt a) =
                                      __smtx_model_eval N (__eo_to_smt a) :=
                                  ihA hBvsVar M N hRel hAScan hANN
                                change
                                  __smtx_model_eval M
                                      (SmtTerm.str_rev (__eo_to_smt a)) =
                                    __smtx_model_eval N
                                      (SmtTerm.str_rev (__eo_to_smt a))
                                simpa [__smtx_model_eval, hAEval]
                              · by_cases hFStrToCode :
                                  f = Term.UOp UserOp.str_to_code
                                · subst f
                                  have hANN :
                                      __smtx_typeof (__eo_to_smt a) ≠
                                        SmtType.None := by
                                    intro hArgNone
                                    apply hNN
                                    change
                                      __smtx_typeof
                                          (SmtTerm.str_to_code
                                            (__eo_to_smt a)) =
                                        SmtType.None
                                    rw [typeof_str_to_code_eq, hArgNone]
                                    rfl
                                  have hAEval :
                                      __smtx_model_eval M (__eo_to_smt a) =
                                        __smtx_model_eval N (__eo_to_smt a) :=
                                    ihA hBvsVar M N hRel hAScan hANN
                                  change
                                    __smtx_model_eval M
                                        (SmtTerm.str_to_code
                                          (__eo_to_smt a)) =
                                      __smtx_model_eval N
                                        (SmtTerm.str_to_code
                                          (__eo_to_smt a))
                                  simpa [__smtx_model_eval, hAEval]
                                · by_cases hFStrFromCode :
                                    f = Term.UOp UserOp.str_from_code
                                  · subst f
                                    have hANN :
                                        __smtx_typeof (__eo_to_smt a) ≠
                                          SmtType.None := by
                                      intro hArgNone
                                      apply hNN
                                      change
                                        __smtx_typeof
                                            (SmtTerm.str_from_code
                                              (__eo_to_smt a)) =
                                          SmtType.None
                                      rw [typeof_str_from_code_eq, hArgNone]
                                      rfl
                                    have hAEval :
                                        __smtx_model_eval M (__eo_to_smt a) =
                                          __smtx_model_eval N
                                            (__eo_to_smt a) :=
                                      ihA hBvsVar M N hRel hAScan hANN
                                    change
                                      __smtx_model_eval M
                                          (SmtTerm.str_from_code
                                            (__eo_to_smt a)) =
                                        __smtx_model_eval N
                                          (SmtTerm.str_from_code
                                            (__eo_to_smt a))
                                    simpa [__smtx_model_eval, hAEval]
                                  · by_cases hFStrToInt :
                                      f = Term.UOp UserOp.str_to_int
                                    · subst f
                                      have hANN :
                                          __smtx_typeof (__eo_to_smt a) ≠
                                            SmtType.None := by
                                        intro hArgNone
                                        apply hNN
                                        change
                                          __smtx_typeof
                                              (SmtTerm.str_to_int
                                                (__eo_to_smt a)) =
                                            SmtType.None
                                        rw [typeof_str_to_int_eq, hArgNone]
                                        rfl
                                      have hAEval :
                                          __smtx_model_eval M
                                              (__eo_to_smt a) =
                                            __smtx_model_eval N
                                              (__eo_to_smt a) :=
                                        ihA hBvsVar M N hRel hAScan hANN
                                      change
                                        __smtx_model_eval M
                                            (SmtTerm.str_to_int
                                              (__eo_to_smt a)) =
                                          __smtx_model_eval N
                                            (SmtTerm.str_to_int
                                              (__eo_to_smt a))
                                      simpa [__smtx_model_eval, hAEval]
                                    · by_cases hFStrToRe :
                                        f = Term.UOp UserOp.str_to_re
                                      · subst f
                                        have hANN :
                                            __smtx_typeof (__eo_to_smt a) ≠
                                              SmtType.None := by
                                          intro hArgNone
                                          apply hNN
                                          change
                                            __smtx_typeof
                                                (SmtTerm.str_to_re
                                                  (__eo_to_smt a)) =
                                              SmtType.None
                                          rw [typeof_str_to_re_eq, hArgNone]
                                          rfl
                                        have hAEval :
                                            __smtx_model_eval M
                                                (__eo_to_smt a) =
                                              __smtx_model_eval N
                                                (__eo_to_smt a) :=
                                          ihA hBvsVar M N hRel hAScan hANN
                                        change
                                          __smtx_model_eval M
                                              (SmtTerm.str_to_re
                                                (__eo_to_smt a)) =
                                            __smtx_model_eval N
                                              (SmtTerm.str_to_re
                                                (__eo_to_smt a))
                                        simpa [__smtx_model_eval, hAEval]
                                      · by_cases hFReMult :
                                          f = Term.UOp UserOp.re_mult
                                        · subst f
                                          have hANN :
                                              __smtx_typeof (__eo_to_smt a) ≠
                                                SmtType.None := by
                                            intro hArgNone
                                            apply hNN
                                            change
                                              __smtx_typeof
                                                  (SmtTerm.re_mult
                                                    (__eo_to_smt a)) =
                                                SmtType.None
                                            rw [typeof_re_mult_eq, hArgNone]
                                            rfl
                                          have hAEval :
                                              __smtx_model_eval M
                                                  (__eo_to_smt a) =
                                                __smtx_model_eval N
                                                  (__eo_to_smt a) :=
                                            ihA hBvsVar M N hRel hAScan hANN
                                          change
                                            __smtx_model_eval M
                                                (SmtTerm.re_mult
                                                  (__eo_to_smt a)) =
                                              __smtx_model_eval N
                                                (SmtTerm.re_mult
                                                  (__eo_to_smt a))
                                          simpa [__smtx_model_eval, hAEval]
                                        · by_cases hFRePlus :
                                            f = Term.UOp UserOp.re_plus
                                          · subst f
                                            have hANN :
                                                __smtx_typeof
                                                    (__eo_to_smt a) ≠
                                                  SmtType.None := by
                                              intro hArgNone
                                              apply hNN
                                              change
                                                __smtx_typeof
                                                    (SmtTerm.re_plus
                                                      (__eo_to_smt a)) =
                                                  SmtType.None
                                              rw [typeof_re_plus_eq, hArgNone]
                                              rfl
                                            have hAEval :
                                                __smtx_model_eval M
                                                    (__eo_to_smt a) =
                                                  __smtx_model_eval N
                                                    (__eo_to_smt a) :=
                                              ihA hBvsVar M N hRel hAScan hANN
                                            change
                                              __smtx_model_eval M
                                                  (SmtTerm.re_plus
                                                    (__eo_to_smt a)) =
                                                __smtx_model_eval N
                                                  (SmtTerm.re_plus
                                                    (__eo_to_smt a))
                                            simpa [__smtx_model_eval, hAEval]
                                          · by_cases hFReOpt :
                                              f = Term.UOp UserOp.re_opt
                                            · subst f
                                              have hANN :
                                                  __smtx_typeof
                                                      (__eo_to_smt a) ≠
                                                    SmtType.None := by
                                                intro hArgNone
                                                apply hNN
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.re_opt
                                                        (__eo_to_smt a)) =
                                                    SmtType.None
                                                rw [typeof_re_opt_eq, hArgNone]
                                                rfl
                                              have hAEval :
                                                  __smtx_model_eval M
                                                      (__eo_to_smt a) =
                                                    __smtx_model_eval N
                                                      (__eo_to_smt a) :=
                                                ihA hBvsVar M N hRel hAScan hANN
                                              change
                                                __smtx_model_eval M
                                                    (SmtTerm.re_opt
                                                      (__eo_to_smt a)) =
                                                  __smtx_model_eval N
                                                    (SmtTerm.re_opt
                                                      (__eo_to_smt a))
                                              simpa [__smtx_model_eval, hAEval]
                                            · by_cases hFReComp :
                                                f = Term.UOp UserOp.re_comp
                                              · subst f
                                                have hANN :
                                                    __smtx_typeof
                                                        (__eo_to_smt a) ≠
                                                      SmtType.None := by
                                                  intro hArgNone
                                                  apply hNN
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.re_comp
                                                          (__eo_to_smt a)) =
                                                      SmtType.None
                                                  rw [typeof_re_comp_eq,
                                                    hArgNone]
                                                  rfl
                                                have hAEval :
                                                    __smtx_model_eval M
                                                        (__eo_to_smt a) =
                                                      __smtx_model_eval N
                                                        (__eo_to_smt a) :=
                                                  ihA hBvsVar M N hRel
                                                    hAScan hANN
                                                change
                                                  __smtx_model_eval M
                                                      (SmtTerm.re_comp
                                                        (__eo_to_smt a)) =
                                                    __smtx_model_eval N
                                                      (SmtTerm.re_comp
                                                        (__eo_to_smt a))
                                                simpa [__smtx_model_eval,
                                                  hAEval]
                                              · by_cases hFBvNot :
                                                  f = Term.UOp UserOp.bvnot
                                                · subst f
                                                  have hANN :
                                                      __smtx_typeof
                                                          (__eo_to_smt a) ≠
                                                        SmtType.None := by
                                                    intro hArgNone
                                                    apply hNN
                                                    change
                                                      __smtx_typeof
                                                          (SmtTerm.bvnot
                                                            (__eo_to_smt a)) =
                                                        SmtType.None
                                                    exact
                                                      smtx_typeof_bvnot_arg_none
                                                        (__eo_to_smt a)
                                                        hArgNone
                                                  have hAEval :
                                                      __smtx_model_eval M
                                                          (__eo_to_smt a) =
                                                        __smtx_model_eval N
                                                          (__eo_to_smt a) :=
                                                    ihA hBvsVar M N hRel
                                                      hAScan hANN
                                                  change
                                                    __smtx_model_eval M
                                                        (SmtTerm.bvnot
                                                          (__eo_to_smt a)) =
                                                      __smtx_model_eval N
                                                        (SmtTerm.bvnot
                                                          (__eo_to_smt a))
                                                  simpa [__smtx_model_eval,
                                                    hAEval]
                                                · by_cases hFBvNeg :
                                                    f = Term.UOp UserOp.bvneg
                                                  · subst f
                                                    have hANN :
                                                        __smtx_typeof
                                                            (__eo_to_smt a) ≠
                                                          SmtType.None := by
                                                      intro hArgNone
                                                      apply hNN
                                                      change
                                                        __smtx_typeof
                                                            (SmtTerm.bvneg
                                                              (__eo_to_smt a)) =
                                                          SmtType.None
                                                      exact
                                                        smtx_typeof_bvneg_arg_none
                                                          (__eo_to_smt a)
                                                          hArgNone
                                                    have hAEval :
                                                        __smtx_model_eval M
                                                            (__eo_to_smt a) =
                                                          __smtx_model_eval N
                                                            (__eo_to_smt a) :=
                                                      ihA hBvsVar M N hRel
                                                        hAScan hANN
                                                    change
                                                      __smtx_model_eval M
                                                          (SmtTerm.bvneg
                                                            (__eo_to_smt a)) =
                                                        __smtx_model_eval N
                                                          (SmtTerm.bvneg
                                                            (__eo_to_smt a))
                                                    simpa [__smtx_model_eval,
                                                      hAEval]
                                                  · by_cases hFBvNego :
                                                      f = Term.UOp UserOp.bvnego
                                                    · subst f
                                                      have hANN :
                                                          __smtx_typeof
                                                              (__eo_to_smt a) ≠
                                                            SmtType.None := by
                                                        intro hArgNone
                                                        apply hNN
                                                        change
                                                          __smtx_typeof
                                                              (SmtTerm.bvnego
                                                                (__eo_to_smt a)) =
                                                            SmtType.None
                                                        exact
                                                          smtx_typeof_bvnego_arg_none
                                                            (__eo_to_smt a)
                                                            hArgNone
                                                      have hAEval :
                                                          __smtx_model_eval M
                                                              (__eo_to_smt a) =
                                                            __smtx_model_eval N
                                                              (__eo_to_smt a) :=
                                                        ihA hBvsVar M N hRel
                                                          hAScan hANN
                                                      change
                                                        __smtx_model_eval M
                                                            (SmtTerm.bvnego
                                                              (__eo_to_smt a)) =
                                                          __smtx_model_eval N
                                                            (SmtTerm.bvnego
                                                              (__eo_to_smt a))
                                                      simpa [__smtx_model_eval,
                                                        hAEval]
                                                    · by_cases hFSeqUnit :
                                                        f = Term.UOp
                                                          UserOp.seq_unit
                                                      · subst f
                                                        have hANN :
                                                            __smtx_typeof
                                                                (__eo_to_smt a) ≠
                                                              SmtType.None := by
                                                          intro hArgNone
                                                          apply hNN
                                                          change
                                                            __smtx_typeof
                                                                (SmtTerm.seq_unit
                                                                  (__eo_to_smt a)) =
                                                              SmtType.None
                                                          exact
                                                            smtx_typeof_seq_unit_arg_none
                                                              (__eo_to_smt a)
                                                              hArgNone
                                                        have hAEval :
                                                            __smtx_model_eval M
                                                                (__eo_to_smt a) =
                                                              __smtx_model_eval N
                                                                (__eo_to_smt a) :=
                                                          ihA hBvsVar M N hRel
                                                            hAScan hANN
                                                        change
                                                          __smtx_model_eval M
                                                              (SmtTerm.seq_unit
                                                                (__eo_to_smt a)) =
                                                            __smtx_model_eval N
                                                              (SmtTerm.seq_unit
                                                                (__eo_to_smt a))
                                                        simpa [__smtx_model_eval,
                                                          hAEval]
                                                      · by_cases hFSetSingleton :
                                                          f = Term.UOp
                                                            UserOp.set_singleton
                                                        · subst f
                                                          have hANN :
                                                              __smtx_typeof
                                                                  (__eo_to_smt a) ≠
                                                                SmtType.None := by
                                                            intro hArgNone
                                                            apply hNN
                                                            change
                                                              __smtx_typeof
                                                                  (SmtTerm.set_singleton
                                                                    (__eo_to_smt a)) =
                                                                SmtType.None
                                                            exact
                                                              smtx_typeof_set_singleton_arg_none
                                                                (__eo_to_smt a)
                                                                hArgNone
                                                          have hAEval :
                                                              __smtx_model_eval M
                                                                  (__eo_to_smt a) =
                                                                __smtx_model_eval N
                                                                  (__eo_to_smt a) :=
                                                            ihA hBvsVar M N hRel
                                                              hAScan hANN
                                                          change
                                                            __smtx_model_eval M
                                                                (SmtTerm.set_singleton
                                                                  (__eo_to_smt a)) =
                                                              __smtx_model_eval N
                                                                (SmtTerm.set_singleton
                                                                  (__eo_to_smt a))
                                                          simpa [__smtx_model_eval,
                                                            hAEval]
                                                        · by_cases hFUbvToInt :
                                                            f = Term.UOp
                                                              UserOp.ubv_to_int
                                                          · subst f
                                                            have hANN :
                                                                __smtx_typeof
                                                                    (__eo_to_smt a) ≠
                                                                  SmtType.None := by
                                                              intro hArgNone
                                                              apply hNN
                                                              change
                                                                __smtx_typeof
                                                                    (SmtTerm.ubv_to_int
                                                                      (__eo_to_smt a)) =
                                                                  SmtType.None
                                                              rw [smtx_typeof_ubv_to_int_term_eq,
                                                                hArgNone]
                                                              rfl
                                                            have hAEval :
                                                                __smtx_model_eval M
                                                                    (__eo_to_smt a) =
                                                                  __smtx_model_eval N
                                                                    (__eo_to_smt a) :=
                                                              ihA hBvsVar M N hRel
                                                                hAScan hANN
                                                            change
                                                              __smtx_model_eval M
                                                                  (SmtTerm.ubv_to_int
                                                                    (__eo_to_smt a)) =
                                                                __smtx_model_eval N
                                                                  (SmtTerm.ubv_to_int
                                                                    (__eo_to_smt a))
                                                            simpa [__smtx_model_eval,
                                                              hAEval]
                                                          · by_cases hFSbvToInt :
                                                              f = Term.UOp
                                                                UserOp.sbv_to_int
                                                            · subst f
                                                              have hANN :
                                                                  __smtx_typeof
                                                                      (__eo_to_smt a) ≠
                                                                    SmtType.None := by
                                                                intro hArgNone
                                                                apply hNN
                                                                change
                                                                  __smtx_typeof
                                                                      (SmtTerm.sbv_to_int
                                                                        (__eo_to_smt a)) =
                                                                    SmtType.None
                                                                rw [smtx_typeof_sbv_to_int_term_eq_local,
                                                                  hArgNone]
                                                                rfl
                                                              have hAEval :
                                                                  __smtx_model_eval M
                                                                      (__eo_to_smt a) =
                                                                    __smtx_model_eval N
                                                                      (__eo_to_smt a) :=
                                                                ihA hBvsVar M N hRel
                                                                  hAScan hANN
                                                              change
                                                                __smtx_model_eval M
                                                                    (SmtTerm.sbv_to_int
                                                                      (__eo_to_smt a)) =
                                                                  __smtx_model_eval N
                                                                    (SmtTerm.sbv_to_int
                                                                      (__eo_to_smt a))
                                                              simpa [__smtx_model_eval,
                                                                hAEval]
                                                            · by_cases hFStrToLower :
                                                                f = Term.UOp
                                                                  UserOp.str_to_lower
                                                              · subst f
                                                                have hANN :
                                                                    __smtx_typeof
                                                                        (__eo_to_smt a) ≠
                                                                      SmtType.None := by
                                                                  intro hArgNone
                                                                  apply hNN
                                                                  change
                                                                    __smtx_typeof
                                                                        (SmtTerm.str_to_lower
                                                                          (__eo_to_smt a)) =
                                                                      SmtType.None
                                                                  rw [typeof_str_to_lower_eq,
                                                                    hArgNone]
                                                                  rfl
                                                                have hAEval :
                                                                    __smtx_model_eval M
                                                                        (__eo_to_smt a) =
                                                                      __smtx_model_eval N
                                                                        (__eo_to_smt a) :=
                                                                  ihA hBvsVar M N hRel
                                                                    hAScan hANN
                                                                change
                                                                  __smtx_model_eval M
                                                                      (SmtTerm.str_to_lower
                                                                        (__eo_to_smt a)) =
                                                                    __smtx_model_eval N
                                                                      (SmtTerm.str_to_lower
                                                                        (__eo_to_smt a))
                                                                simpa [__smtx_model_eval,
                                                                  hAEval]
                                                              · by_cases hFStrToUpper :
                                                                  f = Term.UOp
                                                                    UserOp.str_to_upper
                                                                · subst f
                                                                  have hANN :
                                                                      __smtx_typeof
                                                                          (__eo_to_smt a) ≠
                                                                        SmtType.None := by
                                                                    intro hArgNone
                                                                    apply hNN
                                                                    change
                                                                      __smtx_typeof
                                                                          (SmtTerm.str_to_upper
                                                                            (__eo_to_smt a)) =
                                                                        SmtType.None
                                                                    rw [typeof_str_to_upper_eq,
                                                                      hArgNone]
                                                                    rfl
                                                                  have hAEval :
                                                                      __smtx_model_eval M
                                                                          (__eo_to_smt a) =
                                                                        __smtx_model_eval N
                                                                          (__eo_to_smt a) :=
                                                                    ihA hBvsVar M N hRel
                                                                      hAScan hANN
                                                                  change
                                                                    __smtx_model_eval M
                                                                        (SmtTerm.str_to_upper
                                                                          (__eo_to_smt a)) =
                                                                      __smtx_model_eval N
                                                                        (SmtTerm.str_to_upper
                                                                          (__eo_to_smt a))
                                                                  simpa [__smtx_model_eval,
                                                                    hAEval]
                                                                · by_cases hFStrIsDigit :
                                                                    f = Term.UOp
                                                                      UserOp.str_is_digit
                                                                  · subst f
                                                                    have hANN :
                                                                        __smtx_typeof
                                                                            (__eo_to_smt a) ≠
                                                                          SmtType.None := by
                                                                      intro hArgNone
                                                                      apply hNN
                                                                      change
                                                                        __smtx_typeof
                                                                            (SmtTerm.str_is_digit
                                                                              (__eo_to_smt a)) =
                                                                          SmtType.None
                                                                      rw [typeof_str_is_digit_eq,
                                                                        hArgNone]
                                                                      rfl
                                                                    have hAEval :
                                                                        __smtx_model_eval M
                                                                            (__eo_to_smt a) =
                                                                          __smtx_model_eval N
                                                                            (__eo_to_smt a) :=
                                                                      ihA hBvsVar M N hRel
                                                                        hAScan hANN
                                                                    change
                                                                      __smtx_model_eval M
                                                                          (SmtTerm.str_is_digit
                                                                            (__eo_to_smt a)) =
                                                                        __smtx_model_eval N
                                                                          (SmtTerm.str_is_digit
                                                                            (__eo_to_smt a))
                                                                    simpa [__smtx_model_eval,
                                                                      hAEval]
                                                                  · by_cases hFStrFromInt :
                                                                      f = Term.UOp
                                                                        UserOp.str_from_int
                                                                    · subst f
                                                                      have hANN :
                                                                          __smtx_typeof
                                                                              (__eo_to_smt a) ≠
                                                                            SmtType.None := by
                                                                        intro hArgNone
                                                                        apply hNN
                                                                        change
                                                                          __smtx_typeof
                                                                              (SmtTerm.str_from_int
                                                                                (__eo_to_smt a)) =
                                                                            SmtType.None
                                                                        rw [typeof_str_from_int_eq,
                                                                          hArgNone]
                                                                        rfl
                                                                      have hAEval :
                                                                          __smtx_model_eval M
                                                                              (__eo_to_smt a) =
                                                                            __smtx_model_eval N
                                                                              (__eo_to_smt a) :=
                                                                        ihA hBvsVar M N hRel
                                                                          hAScan hANN
                                                                      change
                                                                        __smtx_model_eval M
                                                                            (SmtTerm.str_from_int
                                                                              (__eo_to_smt a)) =
                                                                          __smtx_model_eval N
                                                                            (SmtTerm.str_from_int
                                                                              (__eo_to_smt a))
                                                                      simpa [__smtx_model_eval,
                                                                        hAEval]
                                                                    · by_cases hFIntIsPow2 :
                                                                        f = Term.UOp
                                                                          UserOp.int_ispow2
                                                                      · subst f
                                                                        have hANN :
                                                                            __smtx_typeof
                                                                                (__eo_to_smt a) ≠
                                                                              SmtType.None := by
                                                                          intro hArgNone
                                                                          apply hNN
                                                                          change
                                                                            __smtx_typeof
                                                                                (SmtTerm.and
                                                                                  (SmtTerm.geq
                                                                                    (__eo_to_smt a)
                                                                                    (SmtTerm.Numeral 0))
                                                                                  (SmtTerm.eq
                                                                                    (__eo_to_smt a)
                                                                                    (SmtTerm.int_pow2
                                                                                      (SmtTerm.int_log2
                                                                                        (__eo_to_smt a))))) =
                                                                              SmtType.None
                                                                          exact
                                                                            smtx_typeof_and_first_arg_none
                                                                              (SmtTerm.geq
                                                                                (__eo_to_smt a)
                                                                                (SmtTerm.Numeral 0))
                                                                              (SmtTerm.eq
                                                                                (__eo_to_smt a)
                                                                                (SmtTerm.int_pow2
                                                                                  (SmtTerm.int_log2
                                                                                    (__eo_to_smt a))))
                                                                              (smtx_typeof_geq_first_arg_none
                                                                                (__eo_to_smt a)
                                                                                (SmtTerm.Numeral 0)
                                                                                hArgNone)
                                                                        have hAEval :
                                                                            __smtx_model_eval M
                                                                                (__eo_to_smt a) =
                                                                              __smtx_model_eval N
                                                                                (__eo_to_smt a) :=
                                                                          ihA hBvsVar M N hRel
                                                                            hAScan hANN
                                                                        change
                                                                          __smtx_model_eval M
                                                                              (SmtTerm.and
                                                                                (SmtTerm.geq
                                                                                  (__eo_to_smt a)
                                                                                  (SmtTerm.Numeral 0))
                                                                                (SmtTerm.eq
                                                                                  (__eo_to_smt a)
                                                                                  (SmtTerm.int_pow2
                                                                                    (SmtTerm.int_log2
                                                                                      (__eo_to_smt a))))) =
                                                                            __smtx_model_eval N
                                                                              (SmtTerm.and
                                                                                (SmtTerm.geq
                                                                                  (__eo_to_smt a)
                                                                                  (SmtTerm.Numeral 0))
                                                                                (SmtTerm.eq
                                                                                  (__eo_to_smt a)
                                                                                  (SmtTerm.int_pow2
                                                                                    (SmtTerm.int_log2
                                                                                      (__eo_to_smt a)))))
                                                                        simpa [__smtx_model_eval,
                                                                          hAEval]
                                                                      · by_cases hFIntDivByZero :
                                                                          f = Term.UOp
                                                                            UserOp._at_int_div_by_zero
                                                                        · subst f
                                                                          have hANN :
                                                                              __smtx_typeof
                                                                                  (__eo_to_smt a) ≠
                                                                                SmtType.None := by
                                                                            intro hArgNone
                                                                            apply hNN
                                                                            change
                                                                              __smtx_typeof
                                                                                  (SmtTerm.div
                                                                                    (__eo_to_smt a)
                                                                                    (SmtTerm.Numeral 0)) =
                                                                                SmtType.None
                                                                            exact
                                                                              smtx_typeof_div_first_arg_none
                                                                                (__eo_to_smt a)
                                                                                (SmtTerm.Numeral 0)
                                                                                hArgNone
                                                                          have hAEval :
                                                                              __smtx_model_eval M
                                                                                  (__eo_to_smt a) =
                                                                                __smtx_model_eval N
                                                                                  (__eo_to_smt a) :=
                                                                            ihA hBvsVar M N hRel
                                                                              hAScan hANN
                                                                          change
                                                                            __smtx_model_eval M
                                                                                (SmtTerm.div
                                                                                  (__eo_to_smt a)
                                                                                  (SmtTerm.Numeral 0)) =
                                                                              __smtx_model_eval N
                                                                                (SmtTerm.div
                                                                                  (__eo_to_smt a)
                                                                                  (SmtTerm.Numeral 0))
                                                                          simpa [__smtx_model_eval,
                                                                            hAEval,
                                                                            hRel.globals.1
                                                                              native_div_by_zero_id
                                                                              (SmtType.FunType SmtType.Int
                                                                                SmtType.Int),
                                                                            smtx_model_eval_apply_eq_of_globals
                                                                              hRel.globals]
                                                                        · by_cases hFModByZero :
                                                                            f = Term.UOp
                                                                              UserOp._at_mod_by_zero
                                                                          · subst f
                                                                            have hANN :
                                                                                __smtx_typeof
                                                                                    (__eo_to_smt a) ≠
                                                                                  SmtType.None := by
                                                                              intro hArgNone
                                                                              apply hNN
                                                                              change
                                                                                __smtx_typeof
                                                                                    (SmtTerm.mod
                                                                                      (__eo_to_smt a)
                                                                                      (SmtTerm.Numeral 0)) =
                                                                                  SmtType.None
                                                                              exact
                                                                                smtx_typeof_mod_first_arg_none
                                                                                  (__eo_to_smt a)
                                                                                  (SmtTerm.Numeral 0)
                                                                                  hArgNone
                                                                            have hAEval :
                                                                                __smtx_model_eval M
                                                                                    (__eo_to_smt a) =
                                                                                  __smtx_model_eval N
                                                                                    (__eo_to_smt a) :=
                                                                              ihA hBvsVar M N hRel
                                                                                hAScan hANN
                                                                            change
                                                                              __smtx_model_eval M
                                                                                  (SmtTerm.mod
                                                                                    (__eo_to_smt a)
                                                                                    (SmtTerm.Numeral 0)) =
                                                                                __smtx_model_eval N
                                                                                  (SmtTerm.mod
                                                                                    (__eo_to_smt a)
                                                                                    (SmtTerm.Numeral 0))
                                                                            simpa [__smtx_model_eval,
                                                                              hAEval,
                                                                              hRel.globals.1
                                                                                native_mod_by_zero_id
                                                                                (SmtType.FunType SmtType.Int
                                                                                  SmtType.Int),
                                                                              smtx_model_eval_apply_eq_of_globals
                                                                                hRel.globals]
                                                                          · by_cases hFDivByZero :
                                                                              f = Term.UOp
                                                                                UserOp._at_div_by_zero
                                                                            · subst f
                                                                              have hANN :
                                                                                  __smtx_typeof
                                                                                      (__eo_to_smt a) ≠
                                                                                    SmtType.None := by
                                                                                intro hArgNone
                                                                                apply hNN
                                                                                change
                                                                                  __smtx_typeof
                                                                                      (SmtTerm.qdiv
                                                                                        (__eo_to_smt a)
                                                                                        (SmtTerm.Rational
                                                                                          (native_mk_rational 0 1))) =
                                                                                    SmtType.None
                                                                                exact
                                                                                  smtx_typeof_qdiv_first_arg_none
                                                                                    (__eo_to_smt a)
                                                                                    (SmtTerm.Rational
                                                                                      (native_mk_rational 0 1))
                                                                                    hArgNone
                                                                              have hAEval :
                                                                                  __smtx_model_eval M
                                                                                      (__eo_to_smt a) =
                                                                                    __smtx_model_eval N
                                                                                      (__eo_to_smt a) :=
                                                                                ihA hBvsVar M N hRel
                                                                                  hAScan hANN
                                                                              change
                                                                                __smtx_model_eval M
                                                                                    (SmtTerm.qdiv
                                                                                      (__eo_to_smt a)
                                                                                      (SmtTerm.Rational
                                                                                        (native_mk_rational 0 1))) =
                                                                                  __smtx_model_eval N
                                                                                    (SmtTerm.qdiv
                                                                                      (__eo_to_smt a)
                                                                                      (SmtTerm.Rational
                                                                                        (native_mk_rational 0 1)))
                                                                              simpa [__smtx_model_eval,
                                                                                hAEval,
                                                                                hRel.globals.1
                                                                                  native_qdiv_by_zero_id
                                                                                  (SmtType.FunType SmtType.Real
                                                                                    SmtType.Real),
                                                                                smtx_model_eval_apply_eq_of_globals
                                                                                  hRel.globals]
                                                                            · by_cases hFSetChoose :
                                                                                f = Term.UOp
                                                                                  UserOp.set_choose
                                                                              · subst f
                                                                                have hANN :
                                                                                    __smtx_typeof
                                                                                        (__eo_to_smt a) ≠
                                                                                      SmtType.None := by
                                                                                  intro hArgNone
                                                                                  apply hNN
                                                                                  change
                                                                                    __smtx_typeof
                                                                                        (SmtTerm.map_diff
                                                                                          (__eo_to_smt a)
                                                                                          (SmtTerm.set_empty
                                                                                            (__eo_to_smt_set_elem_type
                                                                                              (__smtx_typeof
                                                                                                (__eo_to_smt a))))) =
                                                                                      SmtType.None
                                                                                  exact
                                                                                    smtx_typeof_set_choose_arg_none
                                                                                      (__eo_to_smt a)
                                                                                      hArgNone
                                                                                have hAEval :
                                                                                    __smtx_model_eval M
                                                                                        (__eo_to_smt a) =
                                                                                      __smtx_model_eval N
                                                                                        (__eo_to_smt a) :=
                                                                                  ihA hBvsVar M N hRel
                                                                                    hAScan hANN
                                                                                change
                                                                                  __smtx_model_eval M
                                                                                      (SmtTerm.map_diff
                                                                                        (__eo_to_smt a)
                                                                                        (SmtTerm.set_empty
                                                                                          (__eo_to_smt_set_elem_type
                                                                                            (__smtx_typeof
                                                                                              (__eo_to_smt a))))) =
                                                                                    __smtx_model_eval N
                                                                                      (SmtTerm.map_diff
                                                                                        (__eo_to_smt a)
                                                                                        (SmtTerm.set_empty
                                                                                          (__eo_to_smt_set_elem_type
                                                                                            (__smtx_typeof
                                                                                              (__eo_to_smt a)))))
                                                                                simpa [__smtx_model_eval,
                                                                                  hAEval]
                                                                              · by_cases hFSetIsEmpty :
                                                                                  f = Term.UOp
                                                                                    UserOp.set_is_empty
                                                                                · subst f
                                                                                  have hANN :
                                                                                      __smtx_typeof
                                                                                          (__eo_to_smt a) ≠
                                                                                        SmtType.None := by
                                                                                    intro hArgNone
                                                                                    apply hNN
                                                                                    change
                                                                                      __smtx_typeof
                                                                                          (SmtTerm.eq
                                                                                            (__eo_to_smt a)
                                                                                            (SmtTerm.set_empty
                                                                                              (__smtx_typeof
                                                                                                (__eo_to_smt a)))) =
                                                                                        SmtType.None
                                                                                    exact
                                                                                      smtx_typeof_eq_first_arg_none
                                                                                        (__eo_to_smt a)
                                                                                        (SmtTerm.set_empty
                                                                                          (__smtx_typeof
                                                                                            (__eo_to_smt a)))
                                                                                        hArgNone
                                                                                  have hAEval :
                                                                                      __smtx_model_eval M
                                                                                          (__eo_to_smt a) =
                                                                                        __smtx_model_eval N
                                                                                          (__eo_to_smt a) :=
                                                                                    ihA hBvsVar M N hRel
                                                                                      hAScan hANN
                                                                                  change
                                                                                    __smtx_model_eval M
                                                                                        (SmtTerm.eq
                                                                                          (__eo_to_smt a)
                                                                                          (SmtTerm.set_empty
                                                                                            (__smtx_typeof
                                                                                              (__eo_to_smt a)))) =
                                                                                      __smtx_model_eval N
                                                                                        (SmtTerm.eq
                                                                                          (__eo_to_smt a)
                                                                                          (SmtTerm.set_empty
                                                                                            (__smtx_typeof
                                                                                              (__eo_to_smt a))))
                                                                                  simpa [__smtx_model_eval,
                                                                                    hAEval]
                                                                                · by_cases hFSetIsSingleton :
                                                                                    f = Term.UOp
                                                                                      UserOp.set_is_singleton
                                                                                  · subst f
                                                                                    have hANN :
                                                                                        __smtx_typeof
                                                                                            (__eo_to_smt a) ≠
                                                                                          SmtType.None := by
                                                                                      intro hArgNone
                                                                                      apply hNN
                                                                                      change
                                                                                        __smtx_typeof
                                                                                            (SmtTerm.eq
                                                                                              (__eo_to_smt a)
                                                                                              (SmtTerm.set_singleton
                                                                                                (SmtTerm.map_diff
                                                                                                  (__eo_to_smt a)
                                                                                                  (SmtTerm.set_empty
                                                                                                    (__eo_to_smt_set_elem_type
                                                                                                      (__smtx_typeof
                                                                                                        (__eo_to_smt a))))))) =
                                                                                          SmtType.None
                                                                                      exact
                                                                                        smtx_typeof_eq_first_arg_none
                                                                                          (__eo_to_smt a)
                                                                                          (SmtTerm.set_singleton
                                                                                            (SmtTerm.map_diff
                                                                                              (__eo_to_smt a)
                                                                                              (SmtTerm.set_empty
                                                                                                (__eo_to_smt_set_elem_type
                                                                                                  (__smtx_typeof
                                                                                                    (__eo_to_smt a))))))
                                                                                          hArgNone
                                                                                    have hAEval :
                                                                                        __smtx_model_eval M
                                                                                            (__eo_to_smt a) =
                                                                                          __smtx_model_eval N
                                                                                            (__eo_to_smt a) :=
                                                                                      ihA hBvsVar M N hRel
                                                                                        hAScan hANN
                                                                                    change
                                                                                      __smtx_model_eval M
                                                                                          (SmtTerm.eq
                                                                                            (__eo_to_smt a)
                                                                                            (SmtTerm.set_singleton
                                                                                              (SmtTerm.map_diff
                                                                                                (__eo_to_smt a)
                                                                                                (SmtTerm.set_empty
                                                                                                  (__eo_to_smt_set_elem_type
                                                                                                    (__smtx_typeof
                                                                                                      (__eo_to_smt a))))))) =
                                                                                        __smtx_model_eval N
                                                                                          (SmtTerm.eq
                                                                                            (__eo_to_smt a)
                                                                                            (SmtTerm.set_singleton
                                                                                              (SmtTerm.map_diff
                                                                                                (__eo_to_smt a)
                                                                                                (SmtTerm.set_empty
                                                                                                  (__eo_to_smt_set_elem_type
                                                                                                    (__smtx_typeof
                                                                                                      (__eo_to_smt a)))))))
                                                                                    simpa [__smtx_model_eval,
                                                                                      hAEval]
                                                                                  · by_cases hFBvredand :
                                                                                      f = Term.UOp
                                                                                        UserOp.bvredand
                                                                                    · subst f
                                                                                      have hANN :
                                                                                          __smtx_typeof
                                                                                              (__eo_to_smt a) ≠
                                                                                            SmtType.None := by
                                                                                        intro hArgNone
                                                                                        apply hNN
                                                                                        change
                                                                                          __smtx_typeof
                                                                                              (SmtTerm.bvcomp
                                                                                                (__eo_to_smt a)
                                                                                                (SmtTerm.bvnot
                                                                                                  (SmtTerm.Binary
                                                                                                    (__smtx_bv_sizeof_type
                                                                                                      (__smtx_typeof
                                                                                                        (__eo_to_smt a)))
                                                                                                    0))) =
                                                                                            SmtType.None
                                                                                        exact
                                                                                          smtx_typeof_bvcomp_first_arg_none
                                                                                            (__eo_to_smt a)
                                                                                            (SmtTerm.bvnot
                                                                                              (SmtTerm.Binary
                                                                                                (__smtx_bv_sizeof_type
                                                                                                  (__smtx_typeof
                                                                                                    (__eo_to_smt a)))
                                                                                                0))
                                                                                            hArgNone
                                                                                      have hAEval :
                                                                                          __smtx_model_eval M
                                                                                              (__eo_to_smt a) =
                                                                                            __smtx_model_eval N
                                                                                              (__eo_to_smt a) :=
                                                                                        ihA hBvsVar M N hRel
                                                                                          hAScan hANN
                                                                                      change
                                                                                        __smtx_model_eval M
                                                                                            (SmtTerm.bvcomp
                                                                                              (__eo_to_smt a)
                                                                                              (SmtTerm.bvnot
                                                                                                (SmtTerm.Binary
                                                                                                  (__smtx_bv_sizeof_type
                                                                                                    (__smtx_typeof
                                                                                                      (__eo_to_smt a)))
                                                                                                  0))) =
                                                                                          __smtx_model_eval N
                                                                                            (SmtTerm.bvcomp
                                                                                              (__eo_to_smt a)
                                                                                              (SmtTerm.bvnot
                                                                                                (SmtTerm.Binary
                                                                                                  (__smtx_bv_sizeof_type
                                                                                                    (__smtx_typeof
                                                                                                      (__eo_to_smt a)))
                                                                                                  0)))
                                                                                      simpa [__smtx_model_eval,
                                                                                        hAEval]
                                                                                    · by_cases hFBvredor :
                                                                                        f = Term.UOp
                                                                                          UserOp.bvredor
                                                                                      · subst f
                                                                                        have hANN :
                                                                                            __smtx_typeof
                                                                                                (__eo_to_smt a) ≠
                                                                                              SmtType.None := by
                                                                                          intro hArgNone
                                                                                          apply hNN
                                                                                          change
                                                                                            __smtx_typeof
                                                                                                (SmtTerm.bvnot
                                                                                                  (SmtTerm.bvcomp
                                                                                                    (__eo_to_smt a)
                                                                                                    (SmtTerm.Binary
                                                                                                      (__smtx_bv_sizeof_type
                                                                                                        (__smtx_typeof
                                                                                                          (__eo_to_smt a)))
                                                                                                      0))) =
                                                                                              SmtType.None
                                                                                          apply smtx_typeof_bvnot_arg_none
                                                                                          exact
                                                                                            smtx_typeof_bvcomp_first_arg_none
                                                                                              (__eo_to_smt a)
                                                                                              (SmtTerm.Binary
                                                                                                (__smtx_bv_sizeof_type
                                                                                                  (__smtx_typeof
                                                                                                    (__eo_to_smt a)))
                                                                                                0)
                                                                                              hArgNone
                                                                                        have hAEval :
                                                                                            __smtx_model_eval M
                                                                                                (__eo_to_smt a) =
                                                                                              __smtx_model_eval N
                                                                                                (__eo_to_smt a) :=
                                                                                          ihA hBvsVar M N hRel
                                                                                            hAScan hANN
                                                                                        change
                                                                                          __smtx_model_eval M
                                                                                              (SmtTerm.bvnot
                                                                                                (SmtTerm.bvcomp
                                                                                                  (__eo_to_smt a)
                                                                                                  (SmtTerm.Binary
                                                                                                    (__smtx_bv_sizeof_type
                                                                                                      (__smtx_typeof
                                                                                                        (__eo_to_smt a)))
                                                                                                    0))) =
                                                                                            __smtx_model_eval N
                                                                                              (SmtTerm.bvnot
                                                                                                (SmtTerm.bvcomp
                                                                                                  (__eo_to_smt a)
                                                                                                  (SmtTerm.Binary
                                                                                                    (__smtx_bv_sizeof_type
                                                                                                      (__smtx_typeof
                                                                                                        (__eo_to_smt a)))
                                                                                            0)))
                                                                                        simpa [__smtx_model_eval,
                                                                                          hAEval]
                                                                                      · by_cases hFBvsize :
                                                                                          f = Term.UOp
                                                                                            UserOp._at_bvsize
                                                                                        · subst f
                                                                                          exact
                                                                                            smtx_model_eval_eq_of_closed_nil_scannerModelRel
                                                                                              hRel
                                                                                              (smtTermClosedIn_eo_to_smt_bvsize
                                                                                                [] a)
                                                                                        · sorry
  | case6 name T xs bvs hXs hBvs =>
      intro hBvsVar M N hRel hScan hNN
      cases name with
      | String s =>
          exact smtx_model_eval_var_eq_of_scannerModelRel
            xs bvs M N hRel s T hScan
      | _ =>
          exfalso
          exact hNN TranslationProofs.smtx_typeof_none
  | case7 x xs bvs hx hXs hBvs hNotQuant hNotApp hNotVar =>
      intro hBvsVar M N hRel hScan hNN
      cases x with
      | UOp op =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_uop [] op)
      | UOp1 op a =>
          cases op
          case seq_empty =>
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (smtTermClosedIn_eo_to_smt_seq_empty [] a)
          case set_empty =>
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (smtTermClosedIn_eo_to_smt_set_empty [] a)
          all_goals
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | UOp2 op a b =>
          cases op
          case _at_bv =>
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (smtTermClosedIn_eo_to_smt_uop2_at_bv_nil a b)
          case _at_quantifiers_skolemize =>
            have hReq :
                __eo_requires
                    (__is_closed_rec
                      (Term.UOp2 UserOp2._at_quantifiers_skolemize a b)
                      Term.__eo_List_nil)
                    (Term.Boolean true) (Term.Boolean false) =
                  Term.Boolean false := by
              simpa [__contains_atomic_term_list_free_rec] using hScan
            have hClosedA :
                __is_closed_rec a Term.__eo_List_nil =
                  Term.Boolean true := by
              have hClosedMarker :=
                condition_true_of_requires_true_false_eq_false hReq
              simpa [__is_closed_rec] using hClosedMarker
            by_cases hForall : ∃ binders body, a = qforall binders body
            · rcases hForall with ⟨binders, body, rfl⟩
              cases hNat : __eo_to_smt_nat_is_valid b
              · rw [eo_to_smt_quantifiers_skolemize_invalid_nat_none
                  binders body b hNat]
                simp [__smtx_model_eval]
              · by_cases hExistsShape :
                  ∃ s T F,
                    __eo_to_smt_exists binders
                        (SmtTerm.not (__eo_to_smt body)) =
                      SmtTerm.exists s T F
                · sorry
                · rw [eo_to_smt_quantifiers_skolemize_forall_non_exists_none
                    binders body b hNat hExistsShape]
                  simp [__smtx_model_eval]
            · rw [eo_to_smt_quantifiers_skolemize_non_forall_none
                a b hForall]
              simp [__smtx_model_eval]
          all_goals
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | UOp3 op a b c =>
          cases op
          case _at_re_unfold_pos_component =>
            have hReq :
                __eo_requires
                    (__is_closed_rec
                      (Term.UOp3 UserOp3._at_re_unfold_pos_component a b c)
                      Term.__eo_List_nil)
                    (Term.Boolean true) (Term.Boolean false) =
                  Term.Boolean false := by
              simpa [__contains_atomic_term_list_free_rec] using hScan
            have hClosedAB :
                __eo_and (__is_closed_rec a Term.__eo_List_nil)
                    (__is_closed_rec b Term.__eo_List_nil) =
                  Term.Boolean true := by
              have hClosedMarker :=
                condition_true_of_requires_true_false_eq_false hReq
              simpa [__is_closed_rec] using hClosedMarker
            rcases eo_and_eq_true_cases hClosedAB with
              ⟨hClosedA, hClosedB⟩
            cases hNat : __eo_to_smt_nat_is_valid c
            · rw [eo_to_smt_re_unfold_pos_component_invalid_nat_none
                a b c hNat]
              simp [__smtx_model_eval]
            · by_cases hConcat :
                ∃ r1 r2, __eo_to_smt b = SmtTerm.re_concat r1 r2
              · rcases hConcat with ⟨r1, r2, hConcatEq⟩
                have hCoreNN :
                    term_has_non_none_type
                      (__eo_to_smt_re_unfold_pos_component
                        (__eo_to_smt a) (__eo_to_smt b)
                        (__eo_to_smt_nat c)) := by
                  unfold term_has_non_none_type
                  intro hCoreNone
                  apply hNN
                  change
                    __smtx_typeof
                        (native_ite (__eo_to_smt_nat_is_valid c)
                          (__eo_to_smt_re_unfold_pos_component
                            (__eo_to_smt a) (__eo_to_smt b)
                            (__eo_to_smt_nat c))
                          SmtTerm.None) =
                      SmtType.None
                  simp [hNat, native_ite, hCoreNone]
                have hArgTypes :=
                  re_unfold_pos_component_args_of_non_none
                    (__eo_to_smt a) (__eo_to_smt b)
                    (__eo_to_smt_nat c) hCoreNN
                have hANN :
                    __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                  rw [hArgTypes.1]
                  simp
                have hBNN :
                    __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
                  rw [hArgTypes.2]
                  simp
                sorry
              · rw [eo_to_smt_re_unfold_pos_component_non_concat_none
                  a b c hNat hConcat]
                simp [__smtx_model_eval]
          case _at_witness_string_length =>
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (smtTermClosedIn_eo_to_smt_uop3_witness_string_length_nil
                a b c)
      | __eo_List =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | __eo_List_nil =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | __eo_List_cons =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | Bool =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | Boolean b =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_boolean [] b)
      | Numeral n =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_numeral [] n)
      | Rational r =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_rational [] r)
      | String s =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_string [] s)
      | Binary w n =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_binary [] w n)
      | «Type» =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | Stuck =>
          exact False.elim (hx rfl)
      | Apply f a =>
          exact False.elim (hNotApp f a rfl)
      | FunType =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | Var name T =>
          exact False.elim (hNotVar name T rfl)
      | DatatypeType s d =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | DatatypeTypeRef s =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | DtcAppType A B =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | DtCons s d i =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_dtcons [] s d i)
      | DtSel s d i j =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_dtsel [] s d i j)
      | USort i =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | UConst i T =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_uconst [] i T)

private theorem get_unused_vars_ne_stuck_of_contains_false
    {Q x F G : Term} :
    __contains_atomic_term_list_free_rec G
        (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
      Term.Boolean false ->
    __get_unused_vars (qterm Q x F) G ≠ Term.Stuck :=
  contains_atomic_term_list_free_rec_vars_ne_stuck_of_false

private theorem get_unused_vars_fallback_shape_of_not_stuck
    (Q x F G : Term) :
    __eo_l_1___get_unused_vars (qterm Q x F) G ≠ Term.Stuck ->
    G = F ∧
      __eo_l_1___get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x := by
  intro hGet
  by_cases hGStuck : G = Term.Stuck
  · subst G
    simp [__eo_l_1___get_unused_vars] at hGet
  · have hReq :
        __eo_requires (__eo_eq F G) (Term.Boolean true)
            (__eo_list_setof Term.__eo_List_cons x) ≠
          Term.Stuck := by
      cases G <;>
        simp_all [qterm, __eo_l_1___get_unused_vars]
    have hG : G = F :=
      RuleProofs.eq_of_requires_eq_true_not_stuck F G
        (__eo_list_setof Term.__eo_List_cons x) hReq
    subst G
    constructor
    · rfl
    · simp [qterm, __eo_l_1___get_unused_vars, __eo_eq, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]

private theorem get_unused_vars_shape_of_not_stuck
    (Q x F G : Term) :
    __get_unused_vars (qterm Q x F) G ≠ Term.Stuck ->
    (G = F ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x) ∨
    ∃ y,
      G = qterm Q y F ∧
      __eo_list_minclude Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y =
        Term.Boolean true ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_diff Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y := by
  intro hGet
  let G0 := G
  cases G with
  | Apply g F2 =>
      let G1 := Term.Apply g F2
      cases g with
      | Apply Q2 y =>
          let sx := __eo_list_setof Term.__eo_List_cons x
          let guard := __eo_and (__eo_eq Q Q2) (__eo_eq F F2)
          let branch :=
            __eo_requires (__eo_list_minclude Term.__eo_List_cons sx y)
              (Term.Boolean true)
              (__eo_list_diff Term.__eo_List_cons sx y)
          by_cases hGuardTrue : guard = Term.Boolean true
          · have hGetEqBranch :
                __get_unused_vars (qterm Q x F) ((Q2.Apply y).Apply F2) =
                  branch := by
              simp [__get_unused_vars, qterm, sx, guard, branch,
                hGuardTrue, __eo_ite, native_ite, native_teq]
            have hBranchNe : branch ≠ Term.Stuck := by
              intro hBranch
              exact hGet (by rw [hGetEqBranch, hBranch])
            have hIncl :
                __eo_list_minclude Term.__eo_List_cons sx y =
                  Term.Boolean true :=
              eq_of_requires_ne_stuck hBranchNe
            rcases eo_and_eq_true_cases_local
                (__eo_eq Q Q2) (__eo_eq F F2) hGuardTrue with
              ⟨hQ, hF⟩
            have hQ2 : Q2 = Q :=
              RuleProofs.eq_of_eo_eq_true Q Q2 hQ
            have hF2 : F2 = F :=
              RuleProofs.eq_of_eo_eq_true F F2 hF
            subst Q2
            subst F2
            right
            refine ⟨y, rfl, ?_, ?_⟩
            · simpa [sx] using hIncl
            · rw [hGetEqBranch]
              simp [branch, sx, hIncl, __eo_requires, native_ite, native_teq,
                native_not, SmtEval.native_not]
          · by_cases hGuardFalse : guard = Term.Boolean false
            · have hGetEqFallback :
                  __get_unused_vars (qterm Q x F) ((Q2.Apply y).Apply F2) =
                    __eo_l_1___get_unused_vars (qterm Q x F)
                      ((Q2.Apply y).Apply F2) := by
                simp [__get_unused_vars, qterm, guard,
                  hGuardFalse, __eo_ite, native_ite, native_teq]
              have hFallbackNe :
                  __eo_l_1___get_unused_vars (qterm Q x F)
                      ((Q2.Apply y).Apply F2) ≠
                    Term.Stuck := by
                intro hFallback
                exact hGet (by rw [hGetEqFallback, hFallback])
              rcases get_unused_vars_fallback_shape_of_not_stuck
                  Q x F ((Q2.Apply y).Apply F2) hFallbackNe with
                ⟨hGF, hFallbackEq⟩
              left
              refine ⟨hGF, ?_⟩
              rw [hGetEqFallback]
              exact hFallbackEq
            · have hGetStuck :
                  __get_unused_vars (qterm Q x F) ((Q2.Apply y).Apply F2) =
                    Term.Stuck := by
                simp [__get_unused_vars, qterm, guard,
                  hGuardTrue, hGuardFalse, __eo_ite, native_ite, native_teq]
              exact False.elim (hGet hGetStuck)
      | _ =>
          have hFallbackNe :
              __eo_l_1___get_unused_vars (qterm Q x F) G1 ≠
                Term.Stuck := by
            simpa [G1, __get_unused_vars, qterm] using hGet
          rcases get_unused_vars_fallback_shape_of_not_stuck
              Q x F G1 hFallbackNe with
            ⟨hGF, hFallbackEq⟩
          left
          refine ⟨by simpa [G1] using hGF, ?_⟩
          simpa [G1, __get_unused_vars, qterm] using hFallbackEq
  | _ =>
      have hFallbackNe :
          __eo_l_1___get_unused_vars (qterm Q x F) G0 ≠ Term.Stuck := by
        simpa [G0, __get_unused_vars, qterm] using hGet
      rcases get_unused_vars_fallback_shape_of_not_stuck Q x F G0 hFallbackNe with
        ⟨hGF, hFallbackEq⟩
      left
      refine ⟨by simpa [G0] using hGF, ?_⟩
      simpa [G0, __get_unused_vars, qterm] using hFallbackEq

private theorem quant_unused_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = qeq (qterm Q x F) G ∧
      (Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists) ∧
      __contains_atomic_term_list_free_rec G
        (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
          Term.Boolean false ∧
      __eo_prog_quant_unused_vars x1 = qeq (qterm Q x F) G := by
  intro hProg
  cases x1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply qHead F =>
                      cases qHead with
                      | Apply Q x =>
                          let v0 := qterm Q x F
                          let noFree :=
                            __contains_atomic_term_list_free_rec G
                              (__get_unused_vars v0 G) Term.__eo_List_nil
                          let inner :=
                            __eo_requires noFree (Term.Boolean false)
                              (qeq v0 G)
                          have hReq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner ≠ Term.Stuck := by
                            simpa [qeq, qterm, v0, noFree, inner,
                              __eo_prog_quant_unused_vars] using hProg
                          have hGuard :
                              __eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                  (__eo_eq Q (Term.UOp UserOp.exists)) =
                                Term.Boolean true :=
                            eq_of_requires_ne_stuck hReq
                          have hInnerNe : inner ≠ Term.Stuck :=
                            body_ne_stuck_of_requires_ne_stuck hReq
                          have hNoFree :
                              noFree = Term.Boolean false :=
                            eq_of_requires_ne_stuck hInnerNe
                          rcases eo_or_eq_true_cases_local
                              (__eo_eq Q (Term.UOp UserOp.forall))
                              (__eo_eq Q (Term.UOp UserOp.exists)) hGuard with
                            hForall | hExists
                          · have hQ : Q = Term.UOp UserOp.forall :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.forall) hForall).symm
                            subst Q
                            refine ⟨Term.UOp UserOp.forall, x, F, G, rfl,
                              Or.inl rfl, ?_, ?_⟩
                            · simpa [v0, qterm, noFree] using hNoFree
                            · change __eo_prog_quant_unused_vars
                                (qeq (qterm (Term.UOp UserOp.forall) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.forall) x F) G
                              have hGuard' :
                                  __eo_or
                                      (__eo_eq (Term.UOp UserOp.forall)
                                        (Term.UOp UserOp.forall))
                                      (__eo_eq (Term.UOp UserOp.forall)
                                        (Term.UOp UserOp.exists)) =
                                    Term.Boolean true := by
                                simp [__eo_or, __eo_eq, native_or, native_teq]
                              have hNoFree' :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (qterm (Term.UOp UserOp.forall) x F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [v0, qterm, noFree] using hNoFree
                              have hNoFreeRaw :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (((Term.UOp UserOp.forall).Apply x).Apply F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [qterm] using hNoFree'
                              simp [qeq, qterm, __eo_prog_quant_unused_vars,
                                hGuard', hNoFreeRaw, __eo_requires, native_ite,
                                native_teq, native_not, SmtEval.native_not]
                          · have hQ : Q = Term.UOp UserOp.exists :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.exists) hExists).symm
                            subst Q
                            refine ⟨Term.UOp UserOp.exists, x, F, G, rfl,
                              Or.inr rfl, ?_, ?_⟩
                            · simpa [v0, qterm, noFree] using hNoFree
                            · change __eo_prog_quant_unused_vars
                                (qeq (qterm (Term.UOp UserOp.exists) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.exists) x F) G
                              have hGuard' :
                                  __eo_or
                                      (__eo_eq (Term.UOp UserOp.exists)
                                        (Term.UOp UserOp.forall))
                                      (__eo_eq (Term.UOp UserOp.exists)
                                        (Term.UOp UserOp.exists)) =
                                    Term.Boolean true := by
                                simp [__eo_or, __eo_eq, native_or, native_teq]
                              have hNoFree' :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (qterm (Term.UOp UserOp.exists) x F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [v0, qterm, noFree] using hNoFree
                              have hNoFreeRaw :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (((Term.UOp UserOp.exists).Apply x).Apply F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [qterm] using hNoFree'
                              simp [qeq, qterm, __eo_prog_quant_unused_vars,
                                hGuard', hNoFreeRaw, __eo_requires, native_ite,
                                native_teq, native_not, SmtEval.native_not]
                      | _ =>
                          simp [__eo_prog_quant_unused_vars] at hProg
                  | _ =>
                      simp [__eo_prog_quant_unused_vars] at hProg
              | _ =>
                  simp [__eo_prog_quant_unused_vars] at hProg
          | _ =>
              simp [__eo_prog_quant_unused_vars] at hProg
      | _ =>
          simp [__eo_prog_quant_unused_vars] at hProg
  | _ =>
      simp [__eo_prog_quant_unused_vars] at hProg

private theorem quant_unused_vars_has_smt_translation
    (A : Term)
    (hTransA : RuleProofs.eo_has_smt_translation A)
    (hTy : __eo_typeof (__eo_prog_quant_unused_vars A) = Term.Bool) :
    RuleProofs.eo_has_smt_translation (__eo_prog_quant_unused_vars A) := by
  have hProg : __eo_prog_quant_unused_vars A ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases quant_unused_shape_of_not_stuck A hProg with
    ⟨Q, x, F, G, hA, _hQ, _hNoFree, hProgEq⟩
  rw [hProgEq]
  simpa [hA] using hTransA

private theorem quant_unused_eval
    (M : SmtModel) (hM : model_total_typed M)
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
        (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
          Term.Boolean false)
    (hBool : RuleProofs.eo_has_bool_type (qeq (qterm Q x F) G)) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M (__eo_to_smt G) := by
  have hGetNe :
      __get_unused_vars (qterm Q x F) G ≠ Term.Stuck :=
    get_unused_vars_ne_stuck_of_contains_false hNoFree
  rcases get_unused_vars_shape_of_not_stuck Q x F G hGetNe with
    hSame | hQuant
  · rcases hSame with ⟨hG, hUnused⟩
    subst G
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (qterm Q x F) F hBool with
      ⟨hSameTy, hQuantNN⟩
    have hQuantTy :
        __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool :=
      qterm_typeof_bool_of_quant_non_none Q x F hQ hQuantNN
    have hBodyTy :
        __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
      qterm_body_typeof_bool_of_quant_typeof_bool Q x F hQ hQuantTy
    rcases smt_model_eval_bool_is_boolean M hM (__eo_to_smt F) hBodyTy with
      ⟨b, hBodyEval⟩
    have hConst : body_constant_on_eo_binders (__eo_to_smt F) x := by
      rcases qterm_binder_env_of_quant_typeof_bool Q x F hQ hQuantTy with
        ⟨vars, hBinders⟩
      have hBinderVarList : eo_var_list x := eo_var_list_of_env hBinders
      have hScanSetof :
          __contains_atomic_term_list_free_rec F
              (__eo_list_setof Term.__eo_List_cons x)
              Term.__eo_List_nil =
            Term.Boolean false := by
        simpa [hUnused] using hNoFree
      have hExistsTyForBinders :
          ∃ body : SmtTerm,
            __smtx_typeof (__eo_to_smt_exists x body) =
              SmtType.Bool := by
        rcases hQ with hForall | hExists
        · subst Q
          have hTyForall :
              __smtx_typeof (__eo_to_smt (qforall x F)) =
                SmtType.Bool := by
            simpa [qforall, qterm] using hQuantTy
          have hx : x ≠ Term.__eo_List_nil :=
            qforall_non_nil_of_non_none x F hQuantNN
          refine ⟨SmtTerm.not (__eo_to_smt F), ?_⟩
          rw [eo_to_smt_forall_eq x F hx] at hTyForall
          exact smtx_typeof_not_arg_of_bool _ hTyForall
        · subst Q
          have hTyExists :
              __smtx_typeof (__eo_to_smt (qexists x F)) =
                SmtType.Bool := by
            simpa [qexists, qterm] using hQuantTy
          have hx : x ≠ Term.__eo_List_nil :=
            qexists_non_nil_of_non_none x F hQuantNN
          refine ⟨__eo_to_smt F, ?_⟩
          simpa [eo_to_smt_exists_eq x F hx] using hTyExists
      rcases hExistsTyForBinders with ⟨binderBody, hExistsTy⟩
      have hWfAll :
          ∀ (s : native_String) (T : Term),
            eo_var_list_mem (Term.Var (Term.String s) T) x ->
              __smtx_type_wf (__eo_to_smt_type T) = true :=
        eo_smt_var_env_mem_wf_of_exists_bool hBinders hExistsTy
      exact body_constant_on_eo_binders_of_scan_setof_aux
        F x x hBinderVarList hBinders
        (fun _ _ hMem => hMem) hWfAll
        (fun M' N' hRel => by
          exact
            smtx_model_eval_eq_of_contains_atomic_false F
              (__eo_list_setof Term.__eo_List_cons x)
              Term.__eo_List_nil (by trivial) M' N' hRel hScanSetof
              (by rw [hBodyTy]; simp))
    rcases hQ with hForall | hExists
    · subst Q
      have hx : x ≠ Term.__eo_List_nil :=
        qforall_non_nil_of_non_none x F hQuantNN
      exact
        (smtx_model_eval_qforall_eq_of_body_constant_on_binders
          x F M b hx hQuantTy hBodyEval hConst).trans hBodyEval.symm
    · subst Q
      have hx : x ≠ Term.__eo_List_nil :=
        qexists_non_nil_of_non_none x F hQuantNN
      exact
        (smtx_model_eval_qexists_eq_of_body_constant_on_binders
          x F M b hx hQuantTy hBodyEval hConst).trans hBodyEval.symm
  · rcases hQuant with ⟨y, hG, hInclude, hUnused⟩
    subst G
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (qterm Q x F) (qterm Q y F) hBool with
      ⟨hSameTy, hQuantNN⟩
    have hLeftTy :
        __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool :=
      qterm_typeof_bool_of_quant_non_none Q x F hQ hQuantNN
    have hBodyTy :
        __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
      qterm_body_typeof_bool_of_quant_typeof_bool Q x F hQ hLeftTy
    have hRightTy :
        __smtx_typeof (__eo_to_smt (qterm Q y F)) = SmtType.Bool := by
      rw [← hSameTy]
      exact hLeftTy
    rcases qterm_binder_env_of_quant_typeof_bool Q x F hQ hLeftTy with
      ⟨xVars, hXBinders⟩
    rcases qterm_binder_env_of_quant_typeof_bool Q y F hQ hRightTy with
      ⟨yVars, hYBinders⟩
    have hXVarList : eo_var_list x := eo_var_list_of_env hXBinders
    have hYVarList : eo_var_list y := eo_var_list_of_env hYBinders
    have hUnusedVarList :
        eo_var_list
          (__eo_list_diff Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y) :=
      eo_var_list_diff (eo_var_list_setof hXVarList) hYVarList
    rcases eo_smt_var_env_of_var_list hUnusedVarList with
      ⟨unusedVars, hUnusedBinders⟩
    let unused :=
      __eo_list_diff Term.__eo_List_cons
        (__eo_list_setof Term.__eo_List_cons x) y
    have hYNonNil : y ≠ Term.__eo_List_nil := by
      have hRightNN :
          __smtx_typeof (__eo_to_smt (qterm Q y F)) ≠ SmtType.None := by
        rw [hRightTy]
        simp
      rcases hQ with hForall | hExists
      · subst Q
        exact qforall_non_nil_of_non_none y F hRightNN
      · subst Q
        exact qexists_non_nil_of_non_none y F hRightNN
    have hQNe : Q ≠ Term.Stuck := by
      rcases hQ with hForall | hExists
      · subst Q
        intro h
        cases h
      · subst Q
        intro h
        cases h
    have hScanRight :
        __contains_atomic_term_list_free_rec (qterm Q y F)
            unused Term.__eo_List_nil =
          Term.Boolean false := by
      simpa [unused, hUnused] using hNoFree
    have hScanBody :
        __contains_atomic_term_list_free_rec F unused
            (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil) =
          Term.Boolean false :=
      contains_atomic_qterm_body_of_false hYBinders hYNonNil hQNe hScanRight
    have hConcatY :
        __eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil = y :=
      eo_list_concat_nil_eq_of_var_list hYVarList
    have hScanBodyY :
        __contains_atomic_term_list_free_rec F unused y =
          Term.Boolean false := by
      simpa [hConcatY] using hScanBody
    have hBodyStable :
        ∀ M' N' : SmtModel,
          scannerModelRel unused y M' N' ->
            __smtx_model_eval M' (__eo_to_smt F) =
              __smtx_model_eval N' (__eo_to_smt F) := by
      intro M' N' hRel
      exact
        smtx_model_eval_eq_of_contains_atomic_false F unused y
          hYVarList M' N' hRel hScanBodyY
          (by rw [hBodyTy]; simp)
    have hExistsTyForX :
        ∃ body : SmtTerm,
          __smtx_typeof (__eo_to_smt_exists x body) =
            SmtType.Bool := by
      rcases hQ with hForall | hExists
      · subst Q
        have hTyForall :
            __smtx_typeof (__eo_to_smt (qforall x F)) =
              SmtType.Bool := by
          simpa [qforall, qterm] using hLeftTy
        have hx : x ≠ Term.__eo_List_nil :=
          qforall_non_nil_of_non_none x F (by rw [hTyForall]; simp)
        refine ⟨SmtTerm.not (__eo_to_smt F), ?_⟩
        rw [eo_to_smt_forall_eq x F hx] at hTyForall
        exact smtx_typeof_not_arg_of_bool _ hTyForall
      · subst Q
        have hTyExists :
            __smtx_typeof (__eo_to_smt (qexists x F)) =
              SmtType.Bool := by
          simpa [qexists, qterm] using hLeftTy
        have hx : x ≠ Term.__eo_List_nil :=
          qexists_non_nil_of_non_none x F (by rw [hTyExists]; simp)
        refine ⟨__eo_to_smt F, ?_⟩
        simpa [eo_to_smt_exists_eq x F hx] using hTyExists
    rcases hExistsTyForX with ⟨binderBodyX, hExistsTyX⟩
    have hWfX :
        ∀ (s : native_String) (T : Term),
          eo_var_list_mem (Term.Var (Term.String s) T) x ->
            __smtx_type_wf (__eo_to_smt_type T) = true :=
      eo_smt_var_env_mem_wf_of_exists_bool hXBinders hExistsTyX
    have hWfUnused :
        ∀ (s : native_String) (T : Term),
          eo_var_list_mem (Term.Var (Term.String s) T) unused ->
            __smtx_type_wf (__eo_to_smt_type T) = true := by
      intro s T hMemUnused
      have hMemDiff :
          eo_var_list_mem (Term.Var (Term.String s) T)
            (__eo_list_diff Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y) := by
        simpa [unused] using hMemUnused
      have hMemSetof :
          eo_var_list_mem (Term.Var (Term.String s) T)
            (__eo_list_setof Term.__eo_List_cons x) :=
        eo_var_list_mem_of_mem_diff_left
          (eo_var_list_setof hXVarList) hYVarList
          (term_var_string_ne_stuck s T) hMemDiff
      have hMemX :
          eo_var_list_mem (Term.Var (Term.String s) T) x :=
        eo_var_list_mem_of_mem_setof hXVarList
          (term_var_string_ne_stuck s T) hMemSetof
      exact hWfX s T hMemX
    have hHitUnused :
        ∀ (s : native_String) (T : Term),
          eo_var_list_mem (Term.Var (Term.String s) T) unused ->
            ∀ T',
              __eo_to_smt_type T' = __eo_to_smt_type T ->
                __eo_is_neg (__eo_list_find Term.__eo_List_cons unused
                  (Term.Var (Term.String s) T')) =
                  Term.Boolean false := by
      intro s T hMemUnused T' hTy
      have hT' : T' = T :=
        eo_to_smt_type_eq_self_of_wf (hWfUnused s T hMemUnused) hTy
      subst T'
      exact eo_is_neg_list_find_false_of_var_list_mem
        hUnusedVarList (term_var_string_ne_stuck s T) hMemUnused
    have hMissUnused :
        ∀ (s : native_String) (T : Term),
          eo_var_list_mem (Term.Var (Term.String s) T) unused ->
            ∀ T',
              __eo_to_smt_type T' = __eo_to_smt_type T ->
                __eo_is_neg (__eo_list_find Term.__eo_List_cons y
                  (Term.Var (Term.String s) T')) =
                  Term.Boolean true := by
      intro s T hMemUnused T' hTy
      have hT' : T' = T :=
        eo_to_smt_type_eq_self_of_wf (hWfUnused s T hMemUnused) hTy
      subst T'
      have hMemDiff :
          eo_var_list_mem (Term.Var (Term.String s) T)
            (__eo_list_diff Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y) := by
        simpa [unused] using hMemUnused
      have hNotMemY :
          ¬ eo_var_list_mem (Term.Var (Term.String s) T) y :=
        eo_var_list_not_mem_of_mem_diff
          (eo_var_list_setof hXVarList) hYVarList
          (eo_var_list_nodup_setof hXVarList)
          (term_var_string_ne_stuck s T) hMemDiff
      exact eo_is_neg_list_find_true_of_var_list_not_mem
        hYVarList (term_var_string_ne_stuck s T) hNotMemY
    have hBodyConstUnused :
        body_constant_on_eo_binders (__eo_to_smt F) unused :=
      body_constant_on_eo_binders_of_scanner_eval_aux
        (__eo_to_smt F) unused y unused hUnusedBinders
        hHitUnused hMissUnused hBodyStable
    let yUnused := __eo_list_concat_rec y unused
    have hConcatBinders :
        EoSmtVarEnv yUnused (yVars ++ unusedVars) := by
      dsimp [yUnused]
      exact EoSmtVarEnv.concat_rec hYBinders hUnusedBinders
    have hBinderMemIff :
        ∀ key : SmtVarKey, key ∈ xVars ↔ key ∈ yVars ++ unusedVars := by
      intro key
      constructor
      · intro hKey
        rcases eo_smt_var_env_var_list_mem_of_mem hXBinders hKey with
          ⟨s, T, hKeyEq, hMemX⟩
        subst key
        by_cases hMemY :
            eo_var_list_mem (Term.Var (Term.String s) T) y
        · exact List.mem_append.2
            (Or.inl
              (eo_smt_var_env_mem_of_var_list_mem hYBinders hMemY))
        · have hMemSetof :
              eo_var_list_mem (Term.Var (Term.String s) T)
                (__eo_list_setof Term.__eo_List_cons x) :=
            eo_var_list_mem_setof_of_mem hXVarList
              (term_var_string_ne_stuck s T) hMemX
          have hMemUnused :
              eo_var_list_mem (Term.Var (Term.String s) T) unused := by
            simpa [unused] using
              eo_var_list_mem_diff_of_mem_left_not_mem_right
                (eo_var_list_setof hXVarList) hYVarList
                (term_var_string_ne_stuck s T) hMemSetof hMemY
          exact List.mem_append.2
            (Or.inr
              (eo_smt_var_env_mem_of_var_list_mem hUnusedBinders
                hMemUnused))
      · intro hKey
        rcases List.mem_append.1 hKey with hKeyY | hKeyUnused
        · rcases eo_smt_var_env_var_list_mem_of_mem hYBinders hKeyY with
            ⟨s, T, hKeyEq, hMemY⟩
          subst key
          exact eo_smt_var_env_mem_of_var_list_mem hXBinders
            (eo_var_list_mem_left_of_minclude_setof
              hXVarList hYVarList (term_var_string_ne_stuck s T)
              hInclude hMemY)
        · rcases eo_smt_var_env_var_list_mem_of_mem hUnusedBinders
            hKeyUnused with
            ⟨s, T, hKeyEq, hMemUnused⟩
          subst key
          have hMemDiff :
              eo_var_list_mem (Term.Var (Term.String s) T)
                (__eo_list_diff Term.__eo_List_cons
                  (__eo_list_setof Term.__eo_List_cons x) y) := by
            simpa [unused] using hMemUnused
          have hMemSetof :
              eo_var_list_mem (Term.Var (Term.String s) T)
                (__eo_list_setof Term.__eo_List_cons x) :=
            eo_var_list_mem_of_mem_diff_left
              (eo_var_list_setof hXVarList) hYVarList
              (term_var_string_ne_stuck s T) hMemDiff
          exact eo_smt_var_env_mem_of_var_list_mem hXBinders
            (eo_var_list_mem_of_mem_setof hXVarList
              (term_var_string_ne_stuck s T) hMemSetof)
    have hWfUnusedKeys :
        ∀ key ∈ unusedVars, __smtx_type_wf key.2 = true := by
      intro key hKey
      rcases eo_smt_var_env_var_list_mem_of_mem hUnusedBinders hKey with
        ⟨s, T, hKeyEq, hMemUnused⟩
      subst key
      exact hWfUnused s T hMemUnused
    rcases hQ with hForall | hExists
    · subst Q
      have hTyForallX :
          __smtx_typeof (__eo_to_smt (qforall x F)) =
            SmtType.Bool := by
        simpa [qforall, qterm] using hLeftTy
      have hx : x ≠ Term.__eo_List_nil :=
        qforall_non_nil_of_non_none x F (by rw [hTyForallX]; simp)
      have hXExistsNotTy :
          __smtx_typeof
              (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
            SmtType.Bool := by
        rw [eo_to_smt_forall_eq x F hx] at hTyForallX
        exact smtx_typeof_not_arg_of_bool _ hTyForallX
      have hTyForallY :
          __smtx_typeof (__eo_to_smt (qforall y F)) =
            SmtType.Bool := by
        simpa [qforall, qterm] using hRightTy
      have hYExistsNotTy :
          __smtx_typeof
              (__eo_to_smt_exists y (SmtTerm.not (__eo_to_smt F))) =
            SmtType.Bool := by
        rw [eo_to_smt_forall_eq y F hYNonNil] at hTyForallY
        exact smtx_typeof_not_arg_of_bool _ hTyForallY
      have hNotBodyTy :
          __smtx_typeof (SmtTerm.not (__eo_to_smt F)) = SmtType.Bool :=
        smtx_typeof_not_bool_of_arg_bool (__eo_to_smt F) hBodyTy
      have hWfYKeys :
          ∀ key ∈ yVars, __smtx_type_wf key.2 = true :=
        eo_smt_var_env_vars_wf_of_exists_bool hYBinders hYExistsNotTy
      have hWfConcatKeys :
          ∀ key ∈ yVars ++ unusedVars,
            __smtx_type_wf key.2 = true := by
        intro key hKey
        rcases List.mem_append.1 hKey with hKeyY | hKeyUnused
        · exact hWfYKeys key hKeyY
        · exact hWfUnusedKeys key hKeyUnused
      have hConcatTy :
          __smtx_typeof
              (__eo_to_smt_exists yUnused
                (SmtTerm.not (__eo_to_smt F))) =
            SmtType.Bool :=
        smtx_typeof_eo_to_smt_exists_bool_of_env_vars_wf
          hConcatBinders hNotBodyTy hWfConcatKeys
      have hXToConcat :
          __smtx_model_eval M
              (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
            __smtx_model_eval M
              (__eo_to_smt_exists yUnused
                (SmtTerm.not (__eo_to_smt F))) :=
        smtx_model_eval_eo_to_smt_exists_mem_iff_of_env
          M (SmtTerm.not (__eo_to_smt F)) hXBinders hConcatBinders
          hBinderMemIff
      have hNotConstUnused :
          body_constant_on_eo_binders
            (SmtTerm.not (__eo_to_smt F)) unused :=
        body_constant_on_eo_binders_not
          (__eo_to_smt F) unused hBodyConstUnused
      have hDrop :
          __smtx_model_eval M
              (__eo_to_smt_exists yUnused
                (SmtTerm.not (__eo_to_smt F))) =
            __smtx_model_eval M
              (__eo_to_smt_exists y (SmtTerm.not (__eo_to_smt F))) := by
        dsimp [yUnused]
        exact
          smtx_model_eval_eo_to_smt_exists_concat_rec_eq_of_suffix_const
            M hM y unused (SmtTerm.not (__eo_to_smt F))
            hYBinders hUnusedBinders hNotBodyTy hConcatTy
            hYExistsNotTy hNotConstUnused
      have hInner :
          __smtx_model_eval M
              (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
            __smtx_model_eval M
              (__eo_to_smt_exists y (SmtTerm.not (__eo_to_smt F))) :=
        hXToConcat.trans hDrop
      change
        __smtx_model_eval M (__eo_to_smt (qforall x F)) =
          __smtx_model_eval M (__eo_to_smt (qforall y F))
      rw [eo_to_smt_forall_eq x F hx]
      rw [eo_to_smt_forall_eq y F hYNonNil]
      simp [__smtx_model_eval, hInner]
    · subst Q
      have hTyExistsX :
          __smtx_typeof (__eo_to_smt (qexists x F)) =
            SmtType.Bool := by
        simpa [qexists, qterm] using hLeftTy
      have hx : x ≠ Term.__eo_List_nil :=
        qexists_non_nil_of_non_none x F (by rw [hTyExistsX]; simp)
      have hXExistsTy :
          __smtx_typeof (__eo_to_smt_exists x (__eo_to_smt F)) =
            SmtType.Bool := by
        simpa [eo_to_smt_exists_eq x F hx] using hTyExistsX
      have hTyExistsY :
          __smtx_typeof (__eo_to_smt (qexists y F)) =
            SmtType.Bool := by
        simpa [qexists, qterm] using hRightTy
      have hYExistsTy :
          __smtx_typeof (__eo_to_smt_exists y (__eo_to_smt F)) =
            SmtType.Bool := by
        simpa [eo_to_smt_exists_eq y F hYNonNil] using hTyExistsY
      have hWfYKeys :
          ∀ key ∈ yVars, __smtx_type_wf key.2 = true :=
        eo_smt_var_env_vars_wf_of_exists_bool hYBinders hYExistsTy
      have hWfConcatKeys :
          ∀ key ∈ yVars ++ unusedVars,
            __smtx_type_wf key.2 = true := by
        intro key hKey
        rcases List.mem_append.1 hKey with hKeyY | hKeyUnused
        · exact hWfYKeys key hKeyY
        · exact hWfUnusedKeys key hKeyUnused
      have hConcatTy :
          __smtx_typeof
              (__eo_to_smt_exists yUnused (__eo_to_smt F)) =
            SmtType.Bool :=
        smtx_typeof_eo_to_smt_exists_bool_of_env_vars_wf
          hConcatBinders hBodyTy hWfConcatKeys
      have hXToConcat :
          __smtx_model_eval M (__eo_to_smt_exists x (__eo_to_smt F)) =
            __smtx_model_eval M
              (__eo_to_smt_exists yUnused (__eo_to_smt F)) :=
        smtx_model_eval_eo_to_smt_exists_mem_iff_of_env
          M (__eo_to_smt F) hXBinders hConcatBinders hBinderMemIff
      have hDrop :
          __smtx_model_eval M
              (__eo_to_smt_exists yUnused (__eo_to_smt F)) =
            __smtx_model_eval M
              (__eo_to_smt_exists y (__eo_to_smt F)) := by
        dsimp [yUnused]
        exact
          smtx_model_eval_eo_to_smt_exists_concat_rec_eq_of_suffix_const
            M hM y unused (__eo_to_smt F)
            hYBinders hUnusedBinders hBodyTy hConcatTy
            hYExistsTy hBodyConstUnused
      have hInner :
          __smtx_model_eval M (__eo_to_smt_exists x (__eo_to_smt F)) =
            __smtx_model_eval M
              (__eo_to_smt_exists y (__eo_to_smt F)) :=
        hXToConcat.trans hDrop
      change
        __smtx_model_eval M (__eo_to_smt (qexists x F)) =
          __smtx_model_eval M (__eo_to_smt (qexists y F))
      rw [eo_to_smt_exists_eq x F hx]
      rw [eo_to_smt_exists_eq y F hYNonNil]
      exact hInner

theorem cmd_step_quant_unused_vars_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_unused_vars args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_unused_vars args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_unused_vars args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                  using hCmdTrans
              have hProgTy :
                  __eo_typeof (__eo_prog_quant_unused_vars a1) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) = Term.Bool
                  at hResultTy
                exact hResultTy
              have hProgQuant :
                  __eo_prog_quant_unused_vars a1 ≠ Term.Stuck := by
                exact term_ne_stuck_of_typeof_bool hProgTy
              rcases quant_unused_shape_of_not_stuck a1 hProgQuant with
                ⟨Q, x, F, G, hA1, hQ, hNoFree, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (qeq (qterm Q x F) G) := by
                simpa [hA1] using hTransA1
              have hFormulaType :
                  __eo_typeof (qeq (qterm Q x F) G) = Term.Bool := by
                rw [hProgEq] at hProgTy
                exact hProgTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (qeq (qterm Q x F) G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (qeq (qterm Q x F) G) hTransFormula hFormulaType
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_unused_vars a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M
                  (qterm Q x F) G
                · exact hFormulaBool
                · have hEvalEq :=
                    quant_unused_eval M hM Q x F G hQ hNoFree hFormulaBool
                  rw [hEvalEq]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M (__eo_to_smt G))
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_unused_vars a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
