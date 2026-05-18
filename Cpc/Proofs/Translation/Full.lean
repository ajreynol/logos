import Cpc.Spec
import Cpc.Proofs.Translation.Datatypes
import Cpc.Proofs.Translation.Apply

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-!
Full translation-proof surface corresponding to the lightweight stub in
`Cpc.Proofs.Translation`.
-/

private theorem eo_type_valid_of_valid_rec_top_full
    {T : Term}
    (h : eo_type_valid_rec [] T) :
    eo_type_valid T := by
  cases T <;> try simpa [eo_type_valid] using h
  case UOp op =>
    cases op <;> simp [eo_type_valid, eo_type_valid_rec] at h ⊢

private theorem eo_type_valid_of_guard_wf_non_none_full
    {T U : Term}
    (h :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) (__eo_to_smt_type U) ≠
        SmtType.None) :
    eo_type_valid T := by
  unfold __smtx_typeof_guard_wf at h
  have hWf : __smtx_type_wf (__eo_to_smt_type T) = true := by
    by_cases hWf : __smtx_type_wf (__eo_to_smt_type T) = true
    · exact hWf
    · exfalso
      simp [native_ite, hWf] at h
  exact eo_type_valid_of_smt_wf T hWf

private theorem eo_type_valid_of_smt_type_eq_of_field_wf_full
    {T : Term} {A : SmtType}
    (hEq : __eo_to_smt_type T = A)
    (hA : smtx_type_field_wf_rec A native_reflist_nil) :
    eo_type_valid T := by
  exact eo_type_valid_of_valid_rec_top_full
    (eo_type_valid_of_smt_field_wf_rec native_reflist_nil (by
      simpa [hEq] using hA))

private theorem eo_type_valid_of_requires_eq_dtcapp_full
    {T V U A B : Term}
    (hU : eo_type_valid U)
    (hReq : __eo_requires T V U = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  unfold __eo_requires at hReq
  cases hEq : native_teq T V <;> simp [native_ite, hEq] at hReq
  cases hStuck : native_teq T Term.Stuck <;>
    simp [native_ite, hStuck, native_not] at hReq
  all_goals first
    | rw [← hReq]; exact hU
    | exact hU
    | cases hReq

private theorem eo_type_valid_of_typeof_apply_eq_dtcapp_full
    {F X A B : Term}
    (hF : eo_type_valid F)
    (hTy : __eo_typeof_apply F X = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  have hFun :
      ∀ T U, F = Term.Apply (Term.Apply Term.FunType T) U ->
        eo_type_valid U := by
    intro T U hFU
    subst F
    have hF' := hF
    simp [eo_type_valid, eo_type_valid_rec] at hF'
    exact eo_type_valid_of_valid_rec_top_full hF'.2
  have hDtc :
      ∀ T U, F = Term.DtcAppType T U -> eo_type_valid U := by
    intro T U hFU
    subst F
    have hF' := hF
    simp [eo_type_valid, eo_type_valid_rec] at hF'
    exact eo_type_valid_of_valid_rec_top_full hF'.2
  clear hF
  cases X <;> try cases hTy
  all_goals
    cases F <;> try cases hTy
    case Apply f U =>
      cases f <;> try cases hTy
      case Apply g T =>
        cases g <;> try cases hTy
        case FunType =>
          exact eo_type_valid_of_requires_eq_dtcapp_full
            (hFun T U rfl) hTy
    case DtcAppType T U =>
      exact eo_type_valid_of_requires_eq_dtcapp_full
        (hDtc T U rfl) hTy

private theorem eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
    {F X A B : Term}
    (hFun :
      ∀ T U, F = Term.Apply (Term.Apply Term.FunType T) U ->
        eo_type_valid U)
    (hDtc :
      ∀ T U, F = Term.DtcAppType T U -> eo_type_valid U)
    (hTy : __eo_typeof_apply F X = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  cases X <;> try cases hTy
  all_goals
    cases F <;> try cases hTy
    case Apply f U =>
      cases f <;> try cases hTy
      case Apply g T =>
        cases g <;> try cases hTy
        case FunType =>
          exact eo_type_valid_of_requires_eq_dtcapp_full
            (hFun T U rfl) hTy
    case DtcAppType T U =>
      exact eo_type_valid_of_requires_eq_dtcapp_full
        (hDtc T U rfl) hTy

private theorem smtx_apply_head_non_none_of_non_special_full
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
        SmtType.None := by
    cases f
    case DtSel s d i j =>
      exact False.elim (hSel s d i j rfl)
    case DtTester s d i =>
      exact False.elim (hTester s d i rfl)
    all_goals
      simpa [__smtx_typeof] using hNN
  rcases typeof_apply_non_none_cases hApply with ⟨A, B, hHead, _hArg, _hA, _hB⟩
  rcases hHead with hHead | hHead
  · rw [hHead]
    simp
  · rw [hHead]
    simp

private theorem eo_type_valid_of_generic_apply_eq_dtcapp_full
    {f x A B : Term}
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f) ∧
          eo_type_valid (__eo_typeof f))
    (hSel : ∀ s d i j, __eo_to_smt f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, __eo_to_smt f ≠ SmtTerm.DtTester s d i)
    (hTranslate :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply f x) =
        __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hNN : term_has_non_none_type (__eo_to_smt (Term.Apply f x)))
    (hTy : __eo_typeof (Term.Apply f x) = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  have hApplyNN :
      __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
        SmtType.None := by
    unfold term_has_non_none_type at hNN
    rw [← hTranslate]
    exact hNN
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None :=
    smtx_apply_head_non_none_of_non_special_full
      (__eo_to_smt f) (__eo_to_smt x) hSel hTester hApplyNN
  exact eo_type_valid_of_typeof_apply_eq_dtcapp_full (ihF hFNN).2 (by
    rw [← hEoApply]
    exact hTy)

private theorem smtx_typeof_guard_ne_dtcapp_of_ne
    {T U A B : SmtType}
    (hU : U ≠ SmtType.DtcAppType A B) :
    __smtx_typeof_guard T U ≠ SmtType.DtcAppType A B := by
  unfold __smtx_typeof_guard
  cases native_Teq T SmtType.None <;> simp [native_ite, hU]

private theorem native_ite_none_ne_dtcapp_of_ne
    {c : native_Bool} {U A B : SmtType}
    (hU : U ≠ SmtType.DtcAppType A B) :
    native_ite c U SmtType.None ≠ SmtType.DtcAppType A B := by
  cases c <;> simp [native_ite, hU]

private theorem eo_to_smt_type_apply_ne_dtcapp
    (a b : Term) (A B : SmtType) :
    __eo_to_smt_type (Term.Apply a b) ≠ SmtType.DtcAppType A B := by
  intro h
  cases a
  case UOp op =>
    cases op
    case BitVec =>
      cases b <;> simp [__eo_to_smt_type] at h
      case Numeral n =>
        exact native_ite_none_ne_dtcapp_of_ne (by intro h'; cases h') h
    case Seq =>
      exact smtx_typeof_guard_ne_dtcapp_of_ne (by intro h'; cases h') h
    case Set =>
      exact smtx_typeof_guard_ne_dtcapp_of_ne (by intro h'; cases h') h
    all_goals
      simp [__eo_to_smt_type] at h
  case Apply g y =>
    cases g
    case FunType =>
      exact smtx_typeof_guard_ne_dtcapp_of_ne
        (smtx_typeof_guard_ne_dtcapp_of_ne (by intro h'; cases h')) h
    case UOp op =>
      cases op
      case Array =>
        exact smtx_typeof_guard_ne_dtcapp_of_ne
          (smtx_typeof_guard_ne_dtcapp_of_ne (by intro h'; cases h')) h
      case Tuple =>
        exact native_ite_none_ne_dtcapp_of_ne
          (eo_to_smt_type_tuple_ne_dtc_app (__eo_to_smt_type y) (__eo_to_smt_type b) A B) h
      all_goals
        simp [__eo_to_smt_type] at h
    all_goals
      simp [__eo_to_smt_type] at h
  all_goals
    simp [__eo_to_smt_type] at h

private theorem false_of_eq_eo_dtcapp_type_of_no_smt_dtcapp_full
    {t : SmtTerm} {a b : Term}
    (hEq : __smtx_typeof t = __eo_to_smt_type (Term.DtcAppType a b))
    (hNN : __eo_to_smt_type (Term.DtcAppType a b) ≠ SmtType.None)
    (hNe : ∀ A B, __smtx_typeof t ≠ SmtType.DtcAppType A B) :
    False := by
  change
    __smtx_typeof t =
      __smtx_typeof_guard (__eo_to_smt_type a)
        (__smtx_typeof_guard (__eo_to_smt_type b)
          (SmtType.DtcAppType (__eo_to_smt_type a) (__eo_to_smt_type b))) at hEq
  change
    __smtx_typeof_guard (__eo_to_smt_type a)
        (__smtx_typeof_guard (__eo_to_smt_type b)
          (SmtType.DtcAppType (__eo_to_smt_type a) (__eo_to_smt_type b))) ≠
      SmtType.None at hNN
  cases hA : __eo_to_smt_type a <;> cases hB : __eo_to_smt_type b <;>
    simp [__smtx_typeof_guard, native_ite, native_Teq, hA, hB] at hEq hNN
  all_goals
    exact hNe _ _ hEq

private theorem smtx_typeof_apply_dt_sel_ne_dtcapp_full
    (s : native_String) (d : SmtDatatype) (i j : native_Nat)
    (x : SmtTerm) (A B : SmtType) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) ≠
      SmtType.DtcAppType A B := by
  intro h
  cases hR : __smtx_ret_typeof_sel s d i j <;>
    simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
      __smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard,
      native_and, native_ite, native_Teq, hR] at h
  all_goals
    repeat split at h
    all_goals cases h

private theorem eo_to_smt_apply_dt_sel_ne_dtcapp_full
    (s : native_String) (d : Datatype) (i j : native_Nat) (x : Term)
    (A B : SmtType) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) ≠
      SmtType.DtcAppType A B := by
  intro h
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite (native_reserved_datatype_name s) SmtTerm.None
            (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j))
          (__eo_to_smt x)) =
      SmtType.DtcAppType A B at h
  cases hRes : native_reserved_datatype_name s
  · simp [native_ite, hRes] at h
    exact smtx_typeof_apply_dt_sel_ne_dtcapp_full s (__eo_to_smt_datatype d) i j
      (__eo_to_smt x) A B h
  · simp [native_ite, hRes, __smtx_typeof, __smtx_typeof_apply] at h

/-- Recovers Boolean typing of a zero-index `choice_nth` body from `non_none`. -/
private theorem choice_nth_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body 0)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
        cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [__smtx_typeof_choice_nth, hEqFalse, native_ite]
  simpa [native_Teq] using hEq

/-- Pulls the body Boolean fact back through nested `__eo_to_smt_exists`. -/
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

/-- Typing a successor `choice_nth` is the same as skolemizing the body. -/
private theorem smtx_typeof_choice_nth_succ_eq_skolemize
    (s : native_String) (T : SmtType) (body : SmtTerm) (n : native_Nat) :
    __smtx_typeof (SmtTerm.choice_nth s T body n.succ) =
      __smtx_typeof (__eo_to_smt_quantifiers_skolemize body n) := by
  cases body <;>
    simp [__smtx_typeof, __smtx_typeof_choice_nth, __eo_to_smt_quantifiers_skolemize]

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

/-- A true EO list check implies the underlying nil search is non-stuck. -/
private theorem eo_get_nil_rec_ok_of_is_list_true
    (xs : Term) :
    __eo_is_list Term.__eo_List_cons xs = Term.Boolean true ->
    __eo_is_ok (__eo_get_nil_rec Term.__eo_List_cons xs) = Term.Boolean true := by
  intro h
  cases xs <;>
    simpa [__eo_is_list, __eo_get_nil_rec, __eo_is_ok, __eo_requires,
      __eo_is_list_nil, native_ite, native_teq, native_not] using h

/-- SMT existential translation only typechecks for syntactic EO variable lists. -/
private theorem eo_is_list_of_exists_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __eo_is_list Term.__eo_List_cons xs = Term.Boolean true := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    native_decide
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
            have hTailList := eo_is_list_of_exists_bool a body hSub
            have hTailOk := eo_get_nil_rec_ok_of_is_list_true a hTailList
            change
              __eo_is_list Term.__eo_List_cons
                  (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a) =
                Term.Boolean true
            simpa [__eo_is_list, __eo_get_nil_rec, __eo_requires, native_ite,
              native_teq, native_not] using hTailOk
          all_goals
            subst hname
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
            exact False.elim (smtx_typeof_none_ne_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
          exact False.elim (smtx_typeof_none_ne_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
      exact False.elim (smtx_typeof_none_ne_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
    exact False.elim (smtx_typeof_none_ne_bool hNone)

/-- The head variable is the zeroth element of a translated EO variable list. -/
private theorem get_var_type_list_nth_zero_cons_var_of_exists_bool
    (s : native_String) (T a : Term) (body : SmtTerm)
    (hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool) :
    __get_var_type
        (__eo_list_nth Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
          (Term.Numeral (native_nat_to_int 0))) =
      T := by
  have hTailList := eo_is_list_of_exists_bool a body hTailBool
  have hTailOk := eo_get_nil_rec_ok_of_is_list_true a hTailList
  have hFullList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a) =
        Term.Boolean true := by
    simpa [__eo_is_list, __eo_get_nil_rec, __eo_requires, native_ite,
      native_teq, native_not] using hTailOk
  change
    __get_var_type
        (__eo_requires
          (__eo_is_list Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a))
          (Term.Boolean true)
          (__eo_list_nth_rec
            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
            (Term.Numeral (native_nat_to_int 0)))) =
      T
  rw [hFullList]
  rfl

/-- Successor list indexing through a translated EO variable-list cons. -/
private theorem get_var_type_list_nth_succ_cons_var_of_exists_bool
    (s : native_String) (T a : Term) (body : SmtTerm) (n : native_Nat)
    (hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool) :
    __get_var_type
        (__eo_list_nth Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
          (Term.Numeral (native_nat_to_int n.succ))) =
      __get_var_type
        (__eo_list_nth Term.__eo_List_cons a (Term.Numeral (native_nat_to_int n))) := by
  have hTailList := eo_is_list_of_exists_bool a body hTailBool
  have hTailOk := eo_get_nil_rec_ok_of_is_list_true a hTailList
  have hFullList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a) =
        Term.Boolean true := by
    simpa [__eo_is_list, __eo_get_nil_rec, __eo_requires, native_ite,
      native_teq, native_not] using hTailOk
  change
    __get_var_type
        (__eo_requires
          (__eo_is_list Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a))
          (Term.Boolean true)
          (__eo_list_nth_rec
            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
            (Term.Numeral (native_nat_to_int n.succ)))) =
      __get_var_type
        (__eo_requires (__eo_is_list Term.__eo_List_cons a) (Term.Boolean true)
          (__eo_list_nth_rec a (Term.Numeral (native_nat_to_int n))))
  rw [hFullList, hTailList]
  change
    __get_var_type
        (__eo_list_nth_rec a
          (__eo_add (Term.Numeral (native_nat_to_int n.succ))
            (Term.Numeral (-1 : native_Int)))) =
      __get_var_type (__eo_list_nth_rec a (Term.Numeral (native_nat_to_int n)))
  change
    __get_var_type
        (__eo_list_nth_rec a
          (Term.Numeral (native_zplus (native_nat_to_int n.succ) (-1 : native_Int)))) =
      __get_var_type (__eo_list_nth_rec a (Term.Numeral (native_nat_to_int n)))
  rw [show native_zplus (native_nat_to_int n.succ) (-1 : native_Int) =
      native_nat_to_int n by
    simp [native_zplus, native_nat_to_int]
    calc
      (↑n + 1 + -1 : Int) = ↑n + (1 + -1) := by ac_rfl
      _ = ↑n := by rfl]

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
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
            exact False.elim (smtx_typeof_none_ne_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
          exact False.elim (smtx_typeof_none_ne_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
      exact False.elim (smtx_typeof_none_ne_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
    exact False.elim (smtx_typeof_none_ne_bool hNone)

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
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
            exact False.elim (smtx_typeof_none_ne_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
          exact False.elim (smtx_typeof_none_ne_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
      exact False.elim (smtx_typeof_none_ne_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      simpa [smtx_typeof_none, __eo_to_smt_exists] using hTy
    exact False.elim (smtx_typeof_none_ne_bool hNone)

/-- Any well-typed skolemized choice forces the enclosing existential chain to be Boolean. -/
private theorem eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
    (xs : Term) (body : SmtTerm) (n : native_Nat)
    (hBodyNoExists : ∀ s T F, body ≠ SmtTerm.exists s T F) :
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists xs body) n) ≠ SmtType.None ->
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
                                (SmtTerm.choice_nth s (__eo_to_smt_type T) (__eo_to_smt_exists a body) 0) := by
                            unfold term_has_non_none_type
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                          have hBodyBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                            choice_nth_body_bool_of_non_none hChoiceNN
                          rw [__eo_to_smt_exists, __smtx_typeof.eq_135]
                          simp [hBodyBool, native_ite, native_Teq]
                      | _ =>
                          exfalso
                          have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                          exact hNoneNN smtx_typeof_none
                  | _ =>
                      exfalso
                      have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                        simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                      exact hNoneNN smtx_typeof_none
              | _ =>
                  exfalso
                  have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                    simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                  exact hNoneNN smtx_typeof_none
          | _ =>
              exfalso
              have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
              exact hNoneNN smtx_typeof_none
      | _ =>
          exfalso
          have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
          exact hNoneNN smtx_typeof_none
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
                              __smtx_typeof (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists a body) n) ≠
                                SmtType.None := by
                            have hChoiceSucc :
                                __smtx_typeof
                                    (SmtTerm.choice_nth s (__eo_to_smt_type T)
                                      (__eo_to_smt_exists a body) n.succ) ≠
                                  SmtType.None := by
                              simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                            rw [smtx_typeof_choice_nth_succ_eq_skolemize] at hChoiceSucc
                            exact hChoiceSucc
                          have hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                            ih a body hBodyNoExists hTailNN
                          rw [__eo_to_smt_exists, __smtx_typeof.eq_135]
                          simp [hTailBool, native_ite, native_Teq]
                      | _ =>
                          exfalso
                          have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                              __smtx_typeof_choice_nth] using hNN
                          exact hNoneNN smtx_typeof_none
                  | _ =>
                      exfalso
                      have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                        simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                          __smtx_typeof_choice_nth] using hNN
                      exact hNoneNN smtx_typeof_none
              | _ =>
                  exfalso
                  have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                    simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                      __smtx_typeof_choice_nth] using hNN
                  exact hNoneNN smtx_typeof_none
          | _ =>
              exfalso
              have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                  __smtx_typeof_choice_nth] using hNN
              exact hNoneNN smtx_typeof_none
      | _ =>
          exfalso
          cases body
          case «exists» s T F =>
            exact hBodyNoExists s T F rfl
          all_goals
            have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
              simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                __smtx_typeof_choice_nth] using hNN
            exact hNoneNN smtx_typeof_none

/-- Computes the selected binder type for quantifier skolemization. -/
private theorem eo_to_smt_quantifiers_skolemize_type_of_non_none
    (xs : Term) (body : SmtTerm) (n : native_Nat)
    (hBodyNoExists : ∀ s T F, body ≠ SmtTerm.exists s T F) :
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists xs body) n) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists xs body) n) =
      __eo_to_smt_type
        (__get_var_type (__eo_list_nth Term.__eo_List_cons xs (Term.Numeral (native_nat_to_int n)))) := by
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
                                (SmtTerm.choice_nth s (__eo_to_smt_type T) (__eo_to_smt_exists a body) 0) := by
                            unfold term_has_non_none_type
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                          have hBodyBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                            choice_nth_body_bool_of_non_none hChoiceNN
                          have hTy :
                              __smtx_typeof
                                  (__eo_to_smt_quantifiers_skolemize
                                    (__eo_to_smt_exists
                                      (Term.Apply (Term.Apply Term.__eo_List_cons
                                        (Term.Var (Term.String s) T)) a) body) 0) =
                                __eo_to_smt_type T := by
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using
                              (choice_term_typeof_of_non_none
                                (s := s) (T := __eo_to_smt_type T) (body := __eo_to_smt_exists a body) hChoiceNN)
                          have hNth :
                              __get_var_type
                                  (__eo_list_nth Term.__eo_List_cons
                                    (Term.Apply (Term.Apply Term.__eo_List_cons
                                      (Term.Var (Term.String s) T)) a)
                                    (Term.Numeral (native_nat_to_int 0))) =
                                T :=
                            get_var_type_list_nth_zero_cons_var_of_exists_bool
                              (s := s) (T := T) (a := a) (body := body) hBodyBool
                          exact hTy.trans (by
                            exact congrArg __eo_to_smt_type hNth.symm)
                      | _ =>
                          exfalso
                          have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                          exact hNoneNN smtx_typeof_none
                  | _ =>
                      exfalso
                      have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                        simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                      exact hNoneNN smtx_typeof_none
              | _ =>
                  exfalso
                  have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                    simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                  exact hNoneNN smtx_typeof_none
          | _ =>
              exfalso
              have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
              exact hNoneNN smtx_typeof_none
      | _ =>
          exfalso
          cases body
          case «exists» s T F =>
            exact hBodyNoExists s T F rfl
          all_goals
            have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
              simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
            exact hNoneNN smtx_typeof_none
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
                              __smtx_typeof (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists a body) n) ≠
                                SmtType.None := by
                            have hChoiceSucc :
                                __smtx_typeof
                                    (SmtTerm.choice_nth s (__eo_to_smt_type T)
                                      (__eo_to_smt_exists a body) n.succ) ≠
                                  SmtType.None := by
                              simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                            rw [smtx_typeof_choice_nth_succ_eq_skolemize] at hChoiceSucc
                            exact hChoiceSucc
                          have hTailBool :
                              __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                            eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
                              a body n hBodyNoExists hTailNN
                          have hTailTy :
                              __smtx_typeof (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists a body) n) =
                                __eo_to_smt_type
                                  (__get_var_type
                                    (__eo_list_nth Term.__eo_List_cons a
                                      (Term.Numeral (native_nat_to_int n)))) :=
                            ih a body hBodyNoExists hTailNN
                          have hNth :
                              __get_var_type
                                  (__eo_list_nth Term.__eo_List_cons
                                    (Term.Apply (Term.Apply Term.__eo_List_cons
                                      (Term.Var (Term.String s) T)) a)
                                    (Term.Numeral (native_nat_to_int n.succ))) =
                                __get_var_type
                                  (__eo_list_nth Term.__eo_List_cons a
                                    (Term.Numeral (native_nat_to_int n))) :=
                            get_var_type_list_nth_succ_cons_var_of_exists_bool
                              (s := s) (T := T) (a := a) (body := body) (n := n) hTailBool
                          have hSkolemize :
                              __smtx_typeof
                                  (__eo_to_smt_quantifiers_skolemize
                                    (__eo_to_smt_exists
                                      (Term.Apply (Term.Apply Term.__eo_List_cons
                                        (Term.Var (Term.String s) T)) a) body) n.succ) =
                                __smtx_typeof
                                  (__eo_to_smt_quantifiers_skolemize
                                    (__eo_to_smt_exists a body) n) := by
                            change
                              __smtx_typeof
                                  (SmtTerm.choice_nth s (__eo_to_smt_type T)
                                    (__eo_to_smt_exists a body) n.succ) =
                                __smtx_typeof
                                  (__eo_to_smt_quantifiers_skolemize
                                    (__eo_to_smt_exists a body) n)
                            rw [smtx_typeof_choice_nth_succ_eq_skolemize]
                          exact hSkolemize.trans (hTailTy.trans (by
                            exact congrArg __eo_to_smt_type hNth.symm))
                      | _ =>
                          exfalso
                          have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                              __smtx_typeof_choice_nth] using hNN
                          exact hNoneNN smtx_typeof_none
                  | _ =>
                      exfalso
                      have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                        simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                          __smtx_typeof_choice_nth] using hNN
                      exact hNoneNN smtx_typeof_none
              | _ =>
                  exfalso
                  have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                    simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                      __smtx_typeof_choice_nth] using hNN
                  exact hNoneNN smtx_typeof_none
          | _ =>
              exfalso
              have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                  __smtx_typeof_choice_nth] using hNN
              exact hNoneNN smtx_typeof_none
      | _ =>
          exfalso
          have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
              __smtx_typeof_choice_nth] using hNN
          exact hNoneNN smtx_typeof_none

/-- The selected binder type in a well-typed skolemization is a valid EO type. -/
private theorem eo_to_smt_quantifiers_skolemize_var_type_valid_of_non_none
    (xs : Term) (body : SmtTerm) (n : native_Nat)
    (hBodyNoExists : ∀ s T F, body ≠ SmtTerm.exists s T F) :
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists xs body) n) ≠
      SmtType.None ->
    eo_type_valid
      (__get_var_type
        (__eo_list_nth Term.__eo_List_cons xs (Term.Numeral (native_nat_to_int n)))) := by
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
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]
                              using hNN
                          have hBodyBool :
                              __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                            choice_nth_body_bool_of_non_none hChoiceNN
                          have hGuardTy :
                              __smtx_typeof
                                  (SmtTerm.choice_nth s (__eo_to_smt_type T)
                                    (__eo_to_smt_exists a body) 0) =
                                __smtx_typeof_guard_wf (__eo_to_smt_type T)
                                  (__eo_to_smt_type T) :=
                            choice_term_guard_type_of_non_none hChoiceNN
                          have hGuardNN :
                              __smtx_typeof_guard_wf (__eo_to_smt_type T)
                                  (__eo_to_smt_type T) ≠
                                SmtType.None := by
                            intro hNone
                            unfold term_has_non_none_type at hChoiceNN
                            apply hChoiceNN
                            rw [hGuardTy, hNone]
                          have hNth :
                              __get_var_type
                                  (__eo_list_nth Term.__eo_List_cons
                                    (Term.Apply (Term.Apply Term.__eo_List_cons
                                      (Term.Var (Term.String s) T)) a)
                                    (Term.Numeral (native_nat_to_int 0))) =
                                T :=
                            get_var_type_list_nth_zero_cons_var_of_exists_bool
                              (s := s) (T := T) (a := a) (body := body) hBodyBool
                          simpa [hNth] using
                            (eo_type_valid_of_guard_wf_non_none_full
                              (T := T) (U := T) hGuardNN)
                      | _ =>
                          exfalso
                          have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]
                              using hNN
                          exact hNoneNN smtx_typeof_none
                  | _ =>
                      exfalso
                      have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                        simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                      exact hNoneNN smtx_typeof_none
              | _ =>
                  exfalso
                  have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                    simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
                  exact hNoneNN smtx_typeof_none
          | _ =>
              exfalso
              have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists] using hNN
              exact hNoneNN smtx_typeof_none
      | _ =>
          exfalso
          cases body
          case «exists» s T F =>
            exact hBodyNoExists s T F rfl
          all_goals
            have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
              simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                __smtx_typeof_choice_nth] using hNN
            exact hNoneNN smtx_typeof_none
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
                                  SmtType.None := by
                              simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]
                                using hNN
                            rw [smtx_typeof_choice_nth_succ_eq_skolemize] at hChoiceSucc
                            exact hChoiceSucc
                          have hTailBool :
                              __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                            eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
                              a body n hBodyNoExists hTailNN
                          have hTailValid :=
                            ih a body hBodyNoExists hTailNN
                          have hNth :
                              __get_var_type
                                  (__eo_list_nth Term.__eo_List_cons
                                    (Term.Apply (Term.Apply Term.__eo_List_cons
                                      (Term.Var (Term.String s) T)) a)
                                    (Term.Numeral (native_nat_to_int n.succ))) =
                                __get_var_type
                                  (__eo_list_nth Term.__eo_List_cons a
                                    (Term.Numeral (native_nat_to_int n))) :=
                            get_var_type_list_nth_succ_cons_var_of_exists_bool
                              (s := s) (T := T) (a := a) (body := body) (n := n) hTailBool
                          simpa [hNth] using hTailValid
                      | _ =>
                          exfalso
                          have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                              __smtx_typeof_choice_nth] using hNN
                          exact hNoneNN smtx_typeof_none
                  | _ =>
                      exfalso
                      have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                        simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                          __smtx_typeof_choice_nth] using hNN
                      exact hNoneNN smtx_typeof_none
              | _ =>
                  exfalso
                  have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                    simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                      __smtx_typeof_choice_nth] using hNN
                  exact hNoneNN smtx_typeof_none
          | _ =>
              exfalso
              have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
                  __smtx_typeof_choice_nth] using hNN
              exact hNoneNN smtx_typeof_none
      | _ =>
          exfalso
          have hNoneNN : __smtx_typeof SmtTerm.None ≠ SmtType.None := by
            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists,
              __smtx_typeof_choice_nth] using hNN
          exact hNoneNN smtx_typeof_none

/-- Strong induction form: translation typing plus proof-side validity. -/
private theorem eo_to_smt_typeof_matches_translation_and_valid
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) ∧
      eo_type_valid (__eo_typeof t) := by
  let rec go : (term : Term) ->
      __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
        eo_type_valid (__eo_typeof term)
    | Term.UOp op, hNonNone => by
        cases op
        case re_allchar =>
          refine ⟨?_, ?_⟩
          · rw [eo_to_smt_re_allchar, eo_typeof_re_allchar, eo_to_smt_type_reglan]
            unfold __smtx_typeof
            rfl
          · simp [eo_typeof_re_allchar, eo_type_valid]
        case re_none =>
          refine ⟨?_, ?_⟩
          · rw [eo_to_smt_re_none, eo_typeof_re_none, eo_to_smt_type_reglan]
            unfold __smtx_typeof
            rfl
          · simp [eo_typeof_re_none, eo_type_valid]
        case re_all =>
          refine ⟨?_, ?_⟩
          · rw [eo_to_smt_re_all, eo_typeof_re_all, eo_to_smt_type_reglan]
            unfold __smtx_typeof
            rfl
          · simp [eo_typeof_re_all, eo_type_valid]
        case tuple_unit =>
          refine ⟨?_, ?_⟩
          · rw [eo_to_smt_term_tuple_unit, smtx_typeof_tuple_unit_translation,
              eo_typeof_tuple_unit, eo_to_smt_type_unit_tuple]
          · simp [eo_typeof_tuple_unit, eo_type_valid, eo_type_valid_rec]
        all_goals
          exact False.elim (hNonNone (by
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact smtx_typeof_none))
    | Term.UOp1 UserOp1.repeat x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1.zero_extend x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1.sign_extend x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1.rotate_left x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1.rotate_right x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1._at_bit x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1.re_exp x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1._at_witness_string_length x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1.is x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1.update x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1.tuple_select x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1.tuple_update x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp1 UserOp1.int_to_bv x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp2 UserOp2.extract x y, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.UOp2 UserOp2._at_bv x y, hNonNone => by
        have hTranslate :
            __eo_to_smt (Term.UOp2 UserOp2._at_bv x y) =
              __eo_to_smt__at_bv (__eo_to_smt x) (__eo_to_smt y) := by
          rfl
        have hAtNN :
            __smtx_typeof (__eo_to_smt__at_bv (__eo_to_smt x) (__eo_to_smt y)) ≠
              SmtType.None := by
          rwa [← hTranslate]
        rcases eo_to_smt_at_bv_of_non_none hAtNN with
          ⟨n, w, hx, hy, hw, hSmtAt⟩
        have hXTerm : x = Term.Numeral n :=
          eo_to_smt_eq_numeral x n hx
        have hYTerm : y = Term.Numeral w :=
          eo_to_smt_eq_numeral y w hy
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.UOp2 UserOp2._at_bv x y)) =
              SmtType.BitVec (native_int_to_nat w) := by
          rw [hTranslate]
          exact hSmtAt
        have hEo :
            __eo_to_smt_type (__eo_typeof (Term.UOp2 UserOp2._at_bv x y)) =
              SmtType.BitVec (native_int_to_nat w) := by
          rw [hXTerm, hYTerm]
          change
            __eo_to_smt_type
                (__eo_typeof__at_bv (Term.UOp UserOp.Int) (Term.UOp UserOp.Int)
                  (Term.Numeral w)) =
              SmtType.BitVec (native_int_to_nat w)
          simp [__eo_typeof__at_bv, native_ite, hw]
        refine ⟨hSmt.trans hEo.symm, ?_⟩
        rw [hXTerm, hYTerm]
        change eo_type_valid (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
        simp [eo_type_valid, eo_type_valid_rec, hw]
    | Term.UOp2 UserOp2.re_loop x y, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.Boolean b, hNonNone => by
        refine ⟨?_, ?_⟩
        · rw [eo_to_smt_boolean, eo_typeof_boolean, eo_to_smt_type_bool]
          unfold __smtx_typeof
          rfl
        · simp [eo_typeof_boolean, eo_type_valid, eo_type_valid_rec]
    | Term.Numeral n, hNonNone => by
        have hSmt : __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int := by
          change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Int
          unfold __smtx_typeof
          rfl
        refine ⟨hSmt.trans (eo_to_smt_type_typeof_numeral n).symm, ?_⟩
        change eo_type_valid (Term.UOp UserOp.Int)
        simp [eo_type_valid, eo_type_valid_rec]
    | Term.Rational r, hNonNone => by
        have hSmt : __smtx_typeof (__eo_to_smt (Term.Rational r)) = SmtType.Real := by
          change __smtx_typeof (SmtTerm.Rational r) = SmtType.Real
          unfold __smtx_typeof
          rfl
        refine ⟨hSmt.trans (eo_to_smt_type_typeof_rational r).symm, ?_⟩
        change eo_type_valid (Term.UOp UserOp.Real)
        simp [eo_type_valid, eo_type_valid_rec]
    | Term.String s, hNonNone => by
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.String s)) = SmtType.Seq SmtType.Char := by
          change __smtx_typeof (SmtTerm.String s) = SmtType.Seq SmtType.Char
          unfold __smtx_typeof
          rfl
        refine ⟨hSmt.trans (eo_to_smt_type_typeof_string s).symm, ?_⟩
        change eo_type_valid (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
        simp [eo_type_valid, eo_type_valid_rec]
    | Term.Binary w n, hNonNone => by
        have hWidth : native_zleq 0 w = true := by
          by_cases hw : native_zleq 0 w = true
          · exact hw
          · exfalso
            change __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None at hNonNone
            apply hNonNone
            unfold __smtx_typeof
            simp [native_ite, SmtEval.native_and, hw]
        change __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None at hNonNone
        have hSmt := smtx_typeof_binary_of_non_none w n
          hNonNone
        refine ⟨?_, ?_⟩
        · change __smtx_typeof (SmtTerm.Binary w n) =
            __eo_to_smt_type (__eo_typeof (Term.Binary w n))
          exact hSmt.trans (eo_to_smt_type_typeof_binary w n hWidth).symm
        · change eo_type_valid (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
          simp [eo_type_valid, eo_type_valid_rec, hWidth]
    | Term.Var name T, hNonNone => by
        cases name with
        | String s =>
            change __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) ≠
              SmtType.None at hNonNone
            refine ⟨?_, ?_⟩
            · change __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) =
                __eo_to_smt_type (__eo_typeof (Term.Var (Term.String s) T))
              exact
                (smtx_typeof_var_of_non_none s (__eo_to_smt_type T) hNonNone).trans
                  (eo_to_smt_type_typeof_var s T).symm
            · exact eo_type_valid_of_guard_wf_non_none_full
                (T := T) (U := T) (by
                  simpa [__smtx_typeof] using hNonNone)
        | _ =>
            exact False.elim (hNonNone (by
              change __smtx_typeof SmtTerm.None = SmtType.None
              exact smtx_typeof_none))
    | Term.DtCons s d i, hNonNone => by
        have hReserved : __eo_reserved_datatype_name s = false := by
          cases hRes : __eo_reserved_datatype_name s
          · rfl
          · exfalso
            apply hNonNone
            rw [eo_to_smt_term_dt_cons, hRes]
            simp [native_ite]
        have hDtNN :
            __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) ≠ SmtType.None := by
          change
            __smtx_typeof
                (native_ite (__eo_reserved_datatype_name s) SmtTerm.None
                  (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)) ≠
              SmtType.None at hNonNone
          rw [hReserved] at hNonNone
          exact hNonNone
        let D : SmtType := SmtType.Datatype s (__eo_to_smt_datatype d)
        let raw : SmtType :=
          __smtx_typeof_dt_cons_rec D
            (__smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d)) i
        have hGuardNN : __smtx_typeof_guard_wf D raw ≠ SmtType.None := by
          simpa [D, raw, typeof_dt_cons_eq] using hDtNN
        have hWf : __smtx_type_wf D = true :=
          Smtm.smtx_typeof_guard_wf_wf_of_non_none D raw hGuardNN
        have hTyValid : eo_type_valid (Term.DatatypeType s d) :=
          eo_type_valid_of_smt_wf (Term.DatatypeType s d) (by
            simpa [D, __eo_to_smt_type, hReserved, native_ite] using hWf)
        have hDtValid : eo_datatype_valid_rec [s] d := by
          have hPair :
              __eo_reserved_datatype_name s = false ∧ eo_datatype_valid_rec [s] d := by
            simpa [eo_type_valid, eo_type_valid_rec] using hTyValid
          exact hPair.2
        have hTy := eo_to_smt_type_typeof_dt_cons_of_valid s d i hReserved hDtValid hDtNN
        refine ⟨?_, ?_⟩
        · change
            __smtx_typeof
                (native_ite (__eo_reserved_datatype_name s) SmtTerm.None
                  (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)) =
              __eo_to_smt_type (__eo_typeof (Term.DtCons s d i))
          rw [hReserved]
          exact hTy.1.symm
        · exact eo_type_valid_of_valid_rec_top_full hTy.2
    | Term.UConst i T, hNonNone => by
        change __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) ≠
          SmtType.None at hNonNone
        refine ⟨?_, ?_⟩
        · change __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) =
            __eo_to_smt_type (__eo_typeof (Term.UConst i T))
          exact
            (smtx_typeof_uconst_of_non_none (native_uconst_id i) (__eo_to_smt_type T)
              hNonNone).trans
              (eo_to_smt_type_typeof_uconst i T).symm
        · exact eo_type_valid_of_guard_wf_non_none_full
            (T := T) (U := T) (by
              simpa [__smtx_typeof] using hNonNone)
    | Term.Apply f x, hNonNone => by
        have hEq :=
          eo_to_smt_typeof_matches_translation_apply f x (go f) (go x)
            (fun op y h hNN => by
              subst f
              exact go y hNN)
            (fun g y h hNN => by
              subst f
              exact go y hNN)
            (fun g z y h hNN => by
              subst f
              exact go z hNN)
            hNonNone
        refine ⟨hEq, ?_⟩
        have hTermNN :
            term_has_non_none_type (__eo_to_smt (Term.Apply f x)) := by
          unfold term_has_non_none_type
          exact hNonNone
        have hTypeNN :
            __eo_to_smt_type (__eo_typeof (Term.Apply f x)) ≠ SmtType.None := by
          rw [← hEq]
          exact hNonNone
        cases hTy : __eo_typeof (Term.Apply f x)
        case UOp op =>
          rw [hTy] at hTypeNN
          cases op <;>
            simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type] at hTypeNN ⊢
        case DatatypeType s d =>
          have hReserved : __eo_reserved_datatype_name s = false := by
            have hTypeNN' := hTypeNN
            rw [hTy] at hTypeNN'
            simpa [__eo_to_smt_type, native_ite] using hTypeNN'
          have hSmtTy :
              __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                SmtType.Datatype s (__eo_to_smt_datatype d) := by
            rw [hEq, hTy]
            simp [__eo_to_smt_type, native_ite, hReserved]
          exact eo_type_valid_of_smt_wf (Term.DatatypeType s d)
            (by
              simpa [__eo_to_smt_type, native_ite, hReserved] using
                Smtm.smt_datatype_wf_of_non_none_type
                  (__eo_to_smt (Term.Apply f x)) s (__eo_to_smt_datatype d) hSmtTy)
        case DatatypeTypeRef s =>
          have hReserved : __eo_reserved_datatype_name s = false := by
            have hTypeNN' := hTypeNN
            rw [hTy] at hTypeNN'
            simpa [__eo_to_smt_type, native_ite] using hTypeNN'
          have hSmtTy :
              __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                SmtType.TypeRef s := by
            rw [hEq, hTy]
            simp [__eo_to_smt_type, native_ite, hReserved]
          have hNoNone :=
            Smtm.term_type_has_no_none_components_of_non_none
              (__eo_to_smt (Term.Apply f x)) hTermNN
          rw [hSmtTy] at hNoNone
          exact False.elim (by
            simpa [Smtm.type_has_no_none_components] using hNoNone)
        case Apply a b =>
          have hSmtTy :
              __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                __eo_to_smt_type (Term.Apply a b) := by
            rw [hEq, hTy]
          cases hSmt : __eo_to_smt_type (Term.Apply a b)
          case None =>
            exact False.elim (hTypeNN (by rw [hTy, hSmt]))
          case Bool =>
            exact eo_type_valid_of_smt_wf (Term.Apply a b) (by
              simp [hSmt, __smtx_type_wf, __smtx_type_wf_rec, native_and])
          case Int =>
            exact eo_type_valid_of_smt_wf (Term.Apply a b) (by
              simp [hSmt, __smtx_type_wf, __smtx_type_wf_rec, native_and])
          case Real =>
            exact eo_type_valid_of_smt_wf (Term.Apply a b) (by
              simp [hSmt, __smtx_type_wf, __smtx_type_wf_rec, native_and])
          case RegLan =>
            exact eo_type_valid_of_smt_wf (Term.Apply a b) (by
              simp [hSmt, __smtx_type_wf])
          case BitVec w =>
            exact eo_type_valid_of_smt_wf (Term.Apply a b) (by
              simp [hSmt, __smtx_type_wf, __smtx_type_wf_rec, native_and,
                native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
                __smtx_value_canonical_bool, native_zleq, native_zeq,
                native_mod_total, native_int_pow2, native_zexp_total,
                native_nat_to_int, native_int_to_nat, native_ite])
          case Map A B =>
            have hMapTy :
                __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                  SmtType.Map A B := by
              simpa [hSmt] using hSmtTy
            exact eo_type_valid_of_smt_wf (Term.Apply a b)
              (by
                simpa [hSmt] using
                  Smtm.smt_term_map_type_wf_of_non_none
                    (__eo_to_smt (Term.Apply f x)) hTermNN hMapTy)
          case Set A =>
            have hSetTy :
                __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                  SmtType.Set A := by
              simpa [hSmt] using hSmtTy
            exact eo_type_valid_of_smt_wf (Term.Apply a b)
              (by
                simpa [hSmt] using
                  Smtm.smt_term_set_type_wf_of_non_none
                    (__eo_to_smt (Term.Apply f x)) hTermNN hSetTy)
          case Seq A =>
            have hSeqTy :
                __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                  SmtType.Seq A := by
              simpa [hSmt] using hSmtTy
            exact eo_type_valid_of_smt_wf (Term.Apply a b)
              (by
                simpa [hSmt] using
                  Smtm.smt_term_seq_type_wf_of_non_none
                    (__eo_to_smt (Term.Apply f x)) hTermNN hSeqTy)
          case Char =>
            exact eo_type_valid_of_smt_wf (Term.Apply a b) (by
              simp [hSmt, __smtx_type_wf, __smtx_type_wf_rec, native_and])
          case Datatype s d =>
            have hDatatypeTy :
                __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                  SmtType.Datatype s d := by
              simpa [hSmt] using hSmtTy
            exact eo_type_valid_of_smt_wf (Term.Apply a b)
              (by
                simpa [hSmt] using
                  Smtm.smt_datatype_wf_of_non_none_type
                    (__eo_to_smt (Term.Apply f x)) s d hDatatypeTy)
          case TypeRef s =>
            have hRefTy :
                __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                  SmtType.TypeRef s := by
              simpa [hSmt] using hSmtTy
            have hNoNone :=
              Smtm.term_type_has_no_none_components_of_non_none
                (__eo_to_smt (Term.Apply f x)) hTermNN
            rw [hRefTy] at hNoNone
            exact False.elim (by
              simpa [Smtm.type_has_no_none_components] using hNoNone)
          case USort i =>
            exact eo_type_valid_of_smt_wf (Term.Apply a b) (by
              simp [hSmt, __smtx_type_wf, __smtx_type_wf_rec, native_and])
          case FunType A B =>
            have hFunTy :
                __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                  SmtType.FunType A B := by
              simpa [hSmt] using hSmtTy
            exact eo_type_valid_of_smt_wf (Term.Apply a b)
              (by
                simpa [hSmt] using
                  Smtm.smt_term_fun_type_wf_of_non_none
                    (__eo_to_smt (Term.Apply f x)) hTermNN hFunTy)
          case DtcAppType A B =>
            exact False.elim (eo_to_smt_type_apply_ne_dtcapp a b A B hSmt)
        case DtcAppType a b =>
          cases f <;> try dsimp [__eo_typeof] at hTy <;> try cases hTy
          case UOp op =>
            cases op <;> dsimp [__eo_typeof] at hTy hTypeNN
            all_goals first
              | exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                  (f := Term.UOp op) (x := x) (A := a) (B := b)
                  (go (Term.UOp op))
                  (by
                    intro s d i j h
                    cases op <;> simp [__eo_to_smt] at h)
                  (by
                    intro s d i h
                    cases op <;> simp [__eo_to_smt] at h)
                  rfl rfl hTermNN hTy
              | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                  (by intro T U h; cases h)
                  (by intro T U h; cases h)
                  hTy
              | simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                  __eo_typeof_apply, __eo_requires, __eo_typeof_BitVec,
                  __eo_typeof_Seq, __eo_typeof__at__at_TypedList_nil,
                  __eo_typeof_not, __eo_typeof_distinct, __eo_typeof_to_real,
                  __eo_typeof_to_int, __eo_typeof_is_int, __eo_typeof_abs,
                  __eo_typeof_int_pow2, __eo_typeof_int_ispow2,
                  __eo_typeof__at_bvsize, __eo_typeof_bvnot,
                  __eo_typeof_bvnego, __eo_typeof_bvredand,
                  __eo_typeof_str_len, __eo_typeof_str_rev,
                  __eo_typeof_str_to_lower, __eo_typeof_str_to_code,
                  __eo_typeof_str_from_code, __eo_typeof_str_is_digit,
                  __eo_typeof_str_to_re, __eo_typeof_re_mult,
                  __eo_typeof_seq_unit, __eo_typeof_set_singleton,
                  __eo_typeof_set_choose, __eo_typeof_set_is_empty,
                  __eo_typeof__at_div_by_zero, __is_arith_type, __eo_eq,
                  __eo_and, native_ite, native_teq, native_not] at hTy hTypeNN ⊢
                cases hxTy : __eo_typeof x <;>
                  simp [hxTy, eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                    __eo_typeof_apply, __eo_requires, __eo_typeof_BitVec,
                    __eo_typeof_Seq, __eo_typeof__at__at_TypedList_nil,
                    __eo_typeof_not, __eo_typeof_distinct, __eo_typeof_to_real,
                    __eo_typeof_to_int, __eo_typeof_is_int, __eo_typeof_abs,
                    __eo_typeof_int_pow2, __eo_typeof_int_ispow2,
                    __eo_typeof__at_bvsize, __eo_typeof_bvnot,
                    __eo_typeof_bvnego, __eo_typeof_bvredand,
                    __eo_typeof_str_len, __eo_typeof_str_rev,
                    __eo_typeof_str_to_lower, __eo_typeof_str_to_code,
                    __eo_typeof_str_from_code, __eo_typeof_str_is_digit,
                    __eo_typeof_str_to_re, __eo_typeof_re_mult,
                    __eo_typeof_seq_unit, __eo_typeof_set_singleton,
                    __eo_typeof_set_choose, __eo_typeof_set_is_empty,
                    __eo_typeof__at_div_by_zero, __is_arith_type, __eo_eq,
                    __eo_and, native_ite, native_teq, native_not] at hTy hTypeNN ⊢
          case UOp1 op y =>
            cases op <;> dsimp [__eo_typeof] at hTy hTypeNN
            all_goals first
              | exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                  (f := Term.UOp1 op y) (x := x) (A := a) (B := b)
                  (go (Term.UOp1 op y))
                  (by
                    intro s d i j h
                    cases op <;> simp [__eo_to_smt] at h)
                  (by
                    intro s d i h
                    cases op <;> simp [__eo_to_smt] at h)
                  rfl rfl hTermNN hTy
              | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                  (by intro T U h; cases h)
                  (by intro T U h; cases h)
                  hTy
              | simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                  __eo_typeof_apply, __eo_requires, __eo_typeof__at_purify,
                  __eo_typeof_repeat, __eo_typeof_zero_extend,
                  __eo_typeof_rotate_left, __eo_typeof__at_bit,
                  __eo_typeof_seq_empty, __eo_typeof_re_exp,
                  __eo_typeof__at_strings_stoi_result,
                  __eo_typeof_str_to_code, __eo_typeof_div,
                  __eo_typeof_str_at, __eo_typeof_is,
                  __eo_typeof_tuple_select, __eo_typeof_set_empty,
                  __eo_typeof_int_to_bv, __eo_mk_apply, __eo_requires,
                  __eo_add, __eo_mul, __is_arith_type, __eo_eq, native_ite,
                  native_teq, native_not] at hTy hTypeNN ⊢
          case UOp2 op y z =>
            cases op <;> dsimp [__eo_typeof] at hTy hTypeNN
            all_goals first
              | exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                  (f := Term.UOp2 op y z) (x := x) (A := a) (B := b)
                  (go (Term.UOp2 op y z))
                  (by
                    intro s d i j h
                    cases op <;> simp [__eo_to_smt] at h)
                  (by
                    intro s d i h
                    cases op <;> simp [__eo_to_smt] at h)
                  rfl rfl hTermNN hTy
              | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                  (by intro T U h; cases h)
                  (by intro T U h; cases h)
                  hTy
              | simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                  __eo_typeof_apply, __eo_requires,
                  __eo_typeof__at_array_deq_diff, __eo_typeof_extract,
                  __eo_typeof__at_bv, __eo_typeof_re_loop,
                  __eo_typeof__at_strings_deq_diff,
                  __eo_typeof__at_strings_num_occur_re,
                  __eo_typeof__at_strings_occur_index_re,
                  __eo_typeof__at_sets_deq_diff,
                  __eo_typeof__at_quantifiers_skolemize,
                  __eo_typeof__at_const, __eo_mk_apply, __eo_add, __eo_mul,
                  __is_arith_type, __eo_eq, __eo_and, native_ite, native_teq,
                  native_not] at hTy hTypeNN ⊢
          case UOp3 op y z w =>
            cases op <;> dsimp [__eo_typeof, __eo_typeof__at_re_unfold_pos_component] at hTy hTypeNN
            all_goals first
              | exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                  (f := Term.UOp3 op y z w) (x := x) (A := a) (B := b)
                  (go (Term.UOp3 op y z w))
                  (by
                    intro s d i j h
                    cases op <;> simp [__eo_to_smt] at h)
                  (by
                    intro s d i h
                    cases op <;> simp [__eo_to_smt] at h)
                  rfl rfl hTermNN hTy
              | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                  (by intro T U h; cases h)
                  (by intro T U h; cases h)
                  hTy
              | simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                  __eo_typeof_apply, __eo_requires,
                  __eo_typeof__at_re_unfold_pos_component, native_ite,
                  native_teq, native_not] at hTy hTypeNN ⊢
          case __eo_List =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case __eo_List_nil =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case Bool =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case Boolean =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case Numeral =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case Rational =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case String =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case Binary =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case «Type» =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case Stuck =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case FunType =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case DatatypeType =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case DatatypeTypeRef =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case DtcAppType =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case Var name T =>
            exact eo_type_valid_of_generic_apply_eq_dtcapp_full
              (f := Term.Var name T) (x := x) (A := a) (B := b)
              (go (Term.Var name T))
              (by
                intro s d i j h
                cases name <;>
                  first
                    | change SmtTerm.Var _ _ = SmtTerm.DtSel s d i j at h
                      cases h
                    | change SmtTerm.None = SmtTerm.DtSel s d i j at h
                      cases h)
              (by
                intro s d i h
                cases name <;>
                  first
                    | change SmtTerm.Var _ _ = SmtTerm.DtTester s d i at h
                      cases h
                    | change SmtTerm.None = SmtTerm.DtTester s d i at h
                      cases h)
              rfl rfl hTermNN hTy
          case DtCons s d i =>
            exact eo_type_valid_of_generic_apply_eq_dtcapp_full
              (f := Term.DtCons s d i) (x := x) (A := a) (B := b)
              (go (Term.DtCons s d i))
              (by
                intro s' d' i' j' h
                change
                  native_ite (native_reserved_datatype_name s) SmtTerm.None
                      (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) =
                    SmtTerm.DtSel s' d' i' j' at h
                cases hRes : native_reserved_datatype_name s <;>
                  simp [native_ite, hRes] at h)
              (by
                intro s' d' i' h
                change
                  native_ite (native_reserved_datatype_name s) SmtTerm.None
                      (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) =
                    SmtTerm.DtTester s' d' i' at h
                cases hRes : native_reserved_datatype_name s <;>
                  simp [native_ite, hRes] at h)
              rfl rfl hTermNN hTy
          case DtSel s d i j =>
            exact False.elim (false_of_eq_eo_dtcapp_type_of_no_smt_dtcapp_full
              (t := __eo_to_smt (Term.Apply (Term.DtSel s d i j) x))
              (a := a) (b := b)
              (by rw [hEq, hTy])
              (by rw [← hTy]; exact hTypeNN)
              (eo_to_smt_apply_dt_sel_ne_dtcapp_full s d i j x))
          case USort =>
            exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
              (by intro T U h; cases h)
              (by intro T U h; cases h)
              hTy
          case UConst i T =>
            exact eo_type_valid_of_generic_apply_eq_dtcapp_full
              (f := Term.UConst i T) (x := x) (A := a) (B := b)
              (go (Term.UConst i T))
              (by intro s d i j h; cases h)
              (by intro s d i h; cases h)
              rfl rfl hTermNN hTy
        all_goals
          rw [hTy] at hTypeNN
          simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type, native_ite,
            native_Teq] at hTypeNN ⊢
    | Term._at_purify x, hNonNone => by
        have hx : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          intro hNone
          apply hNonNone
          change __smtx_typeof (SmtTerm._at_purify (__eo_to_smt x)) = SmtType.None
          simpa [__smtx_typeof] using hNone
        have hxAll := go x hx
        refine ⟨eo_to_smt_typeof_matches_translation_purify x hxAll.1, ?_⟩
        have hNotStuck : __eo_typeof x ≠ Term.Stuck :=
          eo_type_valid_not_stuck hxAll.2
        change eo_type_valid (__eo_typeof__at_purify (__eo_typeof x))
        cases hTy : __eo_typeof x <;> simp [__eo_typeof__at_purify] at hNotStuck ⊢
        case Stuck =>
          exact False.elim (hNotStuck hTy)
        all_goals
          simpa [hTy] using hxAll.2
      | Term._at_array_deq_diff x1 x2, hNonNone => by
          have hEq :=
            eo_to_smt_typeof_matches_translation_array_deq_diff x1 x2
              (fun h => (go x1 h).1) (fun h => (go x2 h).1) hNonNone
          refine ⟨hEq, ?_⟩
          change
            __smtx_typeof
                (native_ite
                  (native_Teq
                    (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
                    SmtType.None)
                  SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) ≠
              SmtType.None at hNonNone
          cases hGuard :
              native_Teq
                (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
                SmtType.None
          case true =>
            exfalso
            apply hNonNone
            simp [native_ite, hGuard]
          case false =>
            have hMapNN :
                term_has_non_none_type (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) := by
              unfold term_has_non_none_type
              simpa [native_ite, hGuard] using hNonNone
            rcases map_diff_args_of_non_none hMapNN with
              ⟨A, B, hx1Ty, _hx2Ty, hDiffTy⟩ |
              ⟨A, hx1Ty, _hx2Ty, hDiffTy⟩
            · have hAField :
                  smtx_type_field_wf_rec A native_reflist_nil :=
                smtx_type_field_wf_rec_of_type_wf_rec
                  (smt_map_components_wf_rec_of_non_none_type
                    (__eo_to_smt x1) A B hx1Ty).1
              have hEoA :
                  __eo_to_smt_type
                      (__eo_typeof (Term._at_array_deq_diff x1 x2)) = A := by
                rw [← hEq]
                change
                  __smtx_typeof
                      (native_ite
                        (native_Teq
                          (__eo_to_smt_type
                            (__eo_typeof (Term._at_array_deq_diff x1 x2)))
                          SmtType.None)
                        SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) =
                    A
                simpa [native_ite, hGuard] using hDiffTy
              exact eo_type_valid_of_smt_type_eq_of_field_wf_full hEoA hAField
            · have hAField :
                  smtx_type_field_wf_rec A native_reflist_nil :=
                smtx_type_field_wf_rec_of_type_wf_rec
                  (smt_set_component_wf_rec_of_non_none_type
                    (__eo_to_smt x1) A hx1Ty)
              have hEoA :
                  __eo_to_smt_type
                      (__eo_typeof (Term._at_array_deq_diff x1 x2)) = A := by
                rw [← hEq]
                change
                  __smtx_typeof
                      (native_ite
                        (native_Teq
                          (__eo_to_smt_type
                            (__eo_typeof (Term._at_array_deq_diff x1 x2)))
                          SmtType.None)
                        SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) =
                    A
                simpa [native_ite, hGuard] using hDiffTy
              exact eo_type_valid_of_smt_type_eq_of_field_wf_full hEoA hAField
      | Term.seq_empty T, hNonNone => by
          change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) ≠
            SmtType.None at hNonNone
          refine ⟨?_, ?_⟩
          · change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) =
              __eo_to_smt_type (__eo_typeof (Term.seq_empty T))
            exact eo_to_smt_typeof_matches_translation_seq_empty T hNonNone
          · cases hTy : __eo_to_smt_type T <;> rw [hTy] at hNonNone <;>
              simp [__eo_to_smt_seq_empty] at hNonNone
            case Seq A =>
              have hSmt : __smtx_typeof (SmtTerm.seq_empty A) = SmtType.Seq A :=
                smtx_typeof_seq_empty_of_non_none A hNonNone
              have hSeqWF : __smtx_type_wf (SmtType.Seq A) = true :=
                Smtm.smtx_typeof_guard_wf_wf_of_non_none
                  (SmtType.Seq A) (SmtType.Seq A) (by
                    simpa [__smtx_typeof] using hNonNone)
              have hEq :=
                eo_to_smt_typeof_matches_translation_seq_empty
                  T (by simpa [hTy, __eo_to_smt_seq_empty] using hNonNone)
              have hEoSeq :
                  __eo_to_smt_type (__eo_typeof (Term.seq_empty T)) =
                    SmtType.Seq A := by
                rw [← hEq]
                simpa [hTy, __eo_to_smt_seq_empty] using hSmt
              exact eo_type_valid_of_smt_wf (__eo_typeof (Term.seq_empty T))
                (by simpa [hEoSeq] using hSeqWF)
      | Term.set_empty T, hNonNone => by
          change __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) ≠
            SmtType.None at hNonNone
          refine ⟨?_, ?_⟩
          · change __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) =
              __eo_to_smt_type (__eo_typeof (Term.set_empty T))
            exact eo_to_smt_typeof_matches_translation_set_empty T hNonNone
          · cases hTy : __eo_to_smt_type T <;> rw [hTy] at hNonNone <;>
              simp [__eo_to_smt_set_empty] at hNonNone
            case Set A =>
              have hSmt : __smtx_typeof (SmtTerm.set_empty A) = SmtType.Set A :=
                smtx_typeof_set_empty_of_non_none A hNonNone
              have hSetWF : __smtx_type_wf (SmtType.Set A) = true :=
                Smtm.smtx_typeof_guard_wf_wf_of_non_none
                  (SmtType.Set A) (SmtType.Set A) (by
                    simpa [__smtx_typeof] using hNonNone)
              have hEq :=
                eo_to_smt_typeof_matches_translation_set_empty
                  T (by simpa [hTy, __eo_to_smt_set_empty] using hNonNone)
              have hEoSet :
                  __eo_to_smt_type (__eo_typeof (Term.set_empty T)) =
                    SmtType.Set A := by
                rw [← hEq]
                simpa [hTy, __eo_to_smt_set_empty] using hSmt
              exact eo_type_valid_of_smt_wf (__eo_typeof (Term.set_empty T))
                (by simpa [hEoSet] using hSetWF)
      | Term._at_sets_deq_diff x1 x2, hNonNone => by
          exfalso
          apply hNonNone
          change
            __smtx_typeof
                (native_ite
                  (native_Teq (__eo_to_smt_type (Term._at_sets_deq_diff x1 x2))
                    SmtType.None)
                  SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) =
              SmtType.None
          simp [__eo_to_smt_type, native_ite, native_Teq]
    | Term._at_quantifiers_skolemize q idx, hNonNone => by
        cases q with
        | Apply qf body =>
            cases qf with
            | Apply qff xs =>
                cases qff with
                | UOp op =>
                    cases op
                    case «forall» =>
                      cases hIdxZ : native_teq (__eo_is_z idx) (Term.Boolean true)
                      · exfalso
                        apply hNonNone
                        change __smtx_typeof
                            (native_ite (native_teq (__eo_is_z idx) (Term.Boolean true))
                              (native_ite (native_teq (__eo_is_neg idx) (Term.Boolean false))
                                (__eo_to_smt_quantifiers_skolemize
                                  (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                                  (__eo_to_smt_nat idx))
                                SmtTerm.None)
                              SmtTerm.None) =
                          SmtType.None
                        rw [hIdxZ]
                        simp [native_ite, smtx_typeof_none]
                      · cases hIdxNeg : native_teq (__eo_is_neg idx) (Term.Boolean false)
                        · exfalso
                          apply hNonNone
                          change __smtx_typeof
                              (native_ite (native_teq (__eo_is_z idx) (Term.Boolean true))
                                (native_ite (native_teq (__eo_is_neg idx) (Term.Boolean false))
                                  (__eo_to_smt_quantifiers_skolemize
                                    (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                                    (__eo_to_smt_nat idx))
                                  SmtTerm.None)
                                SmtTerm.None) =
                            SmtType.None
                          rw [hIdxZ, hIdxNeg]
                          simp [native_ite, smtx_typeof_none]
                        · refine ⟨?_, ?_⟩
                          · change
                              __smtx_typeof
                                  (native_ite (native_teq (__eo_is_z idx) (Term.Boolean true))
                                    (native_ite (native_teq (__eo_is_neg idx) (Term.Boolean false))
                                      (__eo_to_smt_quantifiers_skolemize
                                        (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                                        (__eo_to_smt_nat idx))
                                      SmtTerm.None)
                                    SmtTerm.None) =
                                __eo_to_smt_type
                                  (__eo_typeof
                                    (Term._at_quantifiers_skolemize
                                      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) idx))
                            rw [hIdxZ, hIdxNeg]
                            simp [native_ite]
                            have hSkolemNN :
                                __smtx_typeof
                                    (__eo_to_smt_quantifiers_skolemize
                                      (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                                      (__eo_to_smt_nat idx)) ≠
                                  SmtType.None := by
                              change
                                __smtx_typeof
                                    (native_ite (native_teq (__eo_is_z idx) (Term.Boolean true))
                                      (native_ite (native_teq (__eo_is_neg idx) (Term.Boolean false))
                                        (__eo_to_smt_quantifiers_skolemize
                                          (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                                          (__eo_to_smt_nat idx))
                                        SmtTerm.None)
                                      SmtTerm.None) ≠
                                  SmtType.None at hNonNone
                              rw [hIdxZ, hIdxNeg] at hNonNone
                              simpa [native_ite] using hNonNone
                            have hBodyNoExists :
                                ∀ s T F, SmtTerm.not (__eo_to_smt body) ≠ SmtTerm.exists s T F := by
                              intro s T F h
                              cases h
                            have hSkTy :=
                              eo_to_smt_quantifiers_skolemize_type_of_non_none xs
                                (SmtTerm.not (__eo_to_smt body)) (__eo_to_smt_nat idx)
                                hBodyNoExists hSkolemNN
                            cases idx with
                            | Numeral n =>
                                have hExistsBool :=
                                  eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none xs
                                    (SmtTerm.not (__eo_to_smt body)) (native_int_to_nat n)
                                    hBodyNoExists hSkolemNN
                                have hXsList :
                                    __eo_typeof xs = Term.__eo_List :=
                                  eo_typeof_var_list_of_exists_bool xs
                                    (SmtTerm.not (__eo_to_smt body)) hExistsBool
                                have hNotBool :
                                    __smtx_typeof (SmtTerm.not (__eo_to_smt body)) = SmtType.Bool :=
                                  eo_to_smt_exists_body_bool_of_bool xs
                                    (SmtTerm.not (__eo_to_smt body)) hExistsBool
                                have hBodyBool :
                                    __smtx_typeof (__eo_to_smt body) = SmtType.Bool :=
                                  smtx_typeof_not_arg_bool (__eo_to_smt body) hNotBool
                                have hBodyNN :
                                    __smtx_typeof (__eo_to_smt body) ≠ SmtType.None := by
                                  rw [hBodyBool]
                                  simp
                                have hBodyBridge := go body hBodyNN
                                have hBodyEoSmt :
                                    __eo_to_smt_type (__eo_typeof body) = SmtType.Bool := by
                                  rw [← hBodyBridge.1, hBodyBool]
                                have hBodyEo : __eo_typeof body = Term.Bool :=
                                  eo_to_smt_type_eq_bool hBodyEoSmt
                                have hQType :
                                    __eo_typeof
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) =
                                      Term.Bool := by
                                  change __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) =
                                    Term.Bool
                                  rw [hXsList, hBodyEo]
                                  rfl
                                have hNat :
                                    native_nat_to_int (native_int_to_nat n) = n := by
                                  have hNegFalse : native_zlt n 0 = false := by
                                    simpa [__eo_is_neg, native_teq, native_and, native_not]
                                      using hIdxNeg
                                  have hNonneg : 0 ≤ n := by
                                    have hNotLt : ¬ n < 0 := by
                                      apply of_decide_eq_false
                                      simpa [native_zlt, SmtEval.native_zlt] using hNegFalse
                                    exact Int.not_lt.mp hNotLt
                                  simp [native_nat_to_int, native_int_to_nat,
                                    SmtEval.native_nat_to_int, SmtEval.native_int_to_nat]
                                  exact Int.max_eq_left hNonneg
                                have hEoSk :
                                    __eo_to_smt_type
                                        (__eo_typeof
                                          (Term._at_quantifiers_skolemize
                                            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
                                            (Term.Numeral n))) =
                                      __eo_to_smt_type
                                        (__get_var_type
                                          (__eo_list_nth Term.__eo_List_cons xs
                                            (Term.Numeral
                                              (native_nat_to_int (native_int_to_nat n))))) := by
                                  change
                                    __eo_to_smt_type
                                        (__eo_typeof__at_quantifiers_skolemize
                                          (__eo_typeof
                                            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body))
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
                                          (__eo_typeof (Term.Numeral n)) (Term.Numeral n)) =
                                      __eo_to_smt_type
                                        (__get_var_type
                                          (__eo_list_nth Term.__eo_List_cons xs
                                            (Term.Numeral
                                              (native_nat_to_int (native_int_to_nat n)))))
                                  rw [hQType]
                                  change
                                    __eo_to_smt_type
                                        (__get_nth_var_type
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
                                          (Term.Numeral n)) =
                                      __eo_to_smt_type
                                        (__get_var_type
                                          (__eo_list_nth Term.__eo_List_cons xs
                                            (Term.Numeral
                                              (native_nat_to_int (native_int_to_nat n)))))
                                  change
                                    __eo_to_smt_type
                                        (__get_var_type
                                          (__eo_list_nth Term.__eo_List_cons xs (Term.Numeral n))) =
                                      __eo_to_smt_type
                                        (__get_var_type
                                          (__eo_list_nth Term.__eo_List_cons xs
                                            (Term.Numeral
                                              (native_nat_to_int (native_int_to_nat n)))))
                                  rw [hNat]
                                simpa [__eo_to_smt_nat] using hSkTy.trans hEoSk.symm
                            | _ =>
                                exfalso
                                simpa [__eo_is_z, __eo_is_z_internal, native_teq,
                                  native_and, native_not] using hIdxZ
                          · have hSkolemNN :
                                __smtx_typeof
                                    (__eo_to_smt_quantifiers_skolemize
                                      (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                                      (__eo_to_smt_nat idx)) ≠
                                  SmtType.None := by
                              change
                                __smtx_typeof
                                    (native_ite (native_teq (__eo_is_z idx) (Term.Boolean true))
                                      (native_ite (native_teq (__eo_is_neg idx) (Term.Boolean false))
                                        (__eo_to_smt_quantifiers_skolemize
                                          (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                                          (__eo_to_smt_nat idx))
                                        SmtTerm.None)
                                      SmtTerm.None) ≠
                                  SmtType.None at hNonNone
                              rw [hIdxZ, hIdxNeg] at hNonNone
                              simpa [native_ite] using hNonNone
                            have hBodyNoExists :
                                ∀ s T F, SmtTerm.not (__eo_to_smt body) ≠ SmtTerm.exists s T F := by
                              intro s T F h
                              cases h
                            cases idx with
                            | Numeral n =>
                                have hExistsBool :=
                                  eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none xs
                                    (SmtTerm.not (__eo_to_smt body)) (native_int_to_nat n)
                                    hBodyNoExists hSkolemNN
                                have hXsList :
                                    __eo_typeof xs = Term.__eo_List :=
                                  eo_typeof_var_list_of_exists_bool xs
                                    (SmtTerm.not (__eo_to_smt body)) hExistsBool
                                have hNotBool :
                                    __smtx_typeof (SmtTerm.not (__eo_to_smt body)) = SmtType.Bool :=
                                  eo_to_smt_exists_body_bool_of_bool xs
                                    (SmtTerm.not (__eo_to_smt body)) hExistsBool
                                have hBodyBool :
                                    __smtx_typeof (__eo_to_smt body) = SmtType.Bool :=
                                  smtx_typeof_not_arg_bool (__eo_to_smt body) hNotBool
                                have hBodyNN :
                                    __smtx_typeof (__eo_to_smt body) ≠ SmtType.None := by
                                  rw [hBodyBool]
                                  simp
                                have hBodyBridge := go body hBodyNN
                                have hBodyEoSmt :
                                    __eo_to_smt_type (__eo_typeof body) = SmtType.Bool := by
                                  rw [← hBodyBridge.1, hBodyBool]
                                have hBodyEo : __eo_typeof body = Term.Bool :=
                                  eo_to_smt_type_eq_bool hBodyEoSmt
                                have hQType :
                                    __eo_typeof
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) =
                                      Term.Bool := by
                                  change __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) =
                                    Term.Bool
                                  rw [hXsList, hBodyEo]
                                  rfl
                                have hNat :
                                    native_nat_to_int (native_int_to_nat n) = n := by
                                  have hNegFalse : native_zlt n 0 = false := by
                                    simpa [__eo_is_neg, native_teq, native_and, native_not]
                                      using hIdxNeg
                                  have hNonneg : 0 ≤ n := by
                                    have hNotLt : ¬ n < 0 := by
                                      apply of_decide_eq_false
                                      simpa [native_zlt, SmtEval.native_zlt] using hNegFalse
                                    exact Int.not_lt.mp hNotLt
                                  simp [native_nat_to_int, native_int_to_nat,
                                    SmtEval.native_nat_to_int, SmtEval.native_int_to_nat]
                                  exact Int.max_eq_left hNonneg
                                have hSkValid :=
                                  eo_to_smt_quantifiers_skolemize_var_type_valid_of_non_none xs
                                    (SmtTerm.not (__eo_to_smt body)) (native_int_to_nat n)
                                    hBodyNoExists hSkolemNN
                                change
                                  eo_type_valid
                                    (__eo_typeof__at_quantifiers_skolemize
                                      (__eo_typeof
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body))
                                      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
                                      (__eo_typeof (Term.Numeral n)) (Term.Numeral n))
                                rw [hQType]
                                change
                                  eo_type_valid
                                    (__get_var_type
                                      (__eo_list_nth Term.__eo_List_cons xs (Term.Numeral n)))
                                simpa [hNat] using hSkValid
                            | _ =>
                                exfalso
                                simpa [__eo_is_z, __eo_is_z_internal, native_teq,
                                  native_and, native_not] using hIdxZ
                    all_goals
                      exact False.elim (hNonNone (by
                        change __smtx_typeof SmtTerm.None = SmtType.None
                        exact smtx_typeof_none))
                | _ =>
                    exact False.elim (hNonNone (by
                      change __smtx_typeof SmtTerm.None = SmtType.None
                      exact smtx_typeof_none))
            | _ =>
                exact False.elim (hNonNone (by
                  change __smtx_typeof SmtTerm.None = SmtType.None
                  exact smtx_typeof_none))
        | _ =>
            exact False.elim (hNonNone (by
              change __smtx_typeof SmtTerm.None = SmtType.None
              exact smtx_typeof_none))
    | Term.__eo_List, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.__eo_List_nil, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.__eo_List_cons, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.Bool, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.Type, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.Stuck, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.FunType, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.DatatypeType s d, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.DatatypeTypeRef s, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.DtcAppType T U, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term.DtSel s d i j, hNonNone => by
        exfalso
        apply hNonNone
        cases hRes : __eo_reserved_datatype_name s <;>
          rw [eo_to_smt_term_dt_sel, hRes] <;>
          simp [native_ite, smtx_typeof_none, smtx_typeof_dt_sel_head_none]
    | Term.USort i, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
      | Term._at_re_unfold_pos_component x y z, hNonNone => by
          exact
            eo_to_smt_typeof_matches_translation_apply_apply_apply_re_unfold_pos_component
              z y x (fun h => (go x h).1) (fun h => (go y h).1) hNonNone
      | Term._at_strings_deq_diff x y, hNonNone => by
          exact
            eo_to_smt_typeof_matches_translation_apply_at_strings_deq_diff
              y x (fun h => (go x h).1) (fun h => (go y h).1) hNonNone
    | Term._at_strings_stoi_result x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term._at_strings_stoi_non_digit x, hNonNone => by
        let regex :=
          SmtTerm.re_comp (SmtTerm.re_range (SmtTerm.String "0") (SmtTerm.String "9"))
        have hTranslate :
            __eo_to_smt (Term._at_strings_stoi_non_digit x) =
              SmtTerm.str_indexof_re (__eo_to_smt x) regex (SmtTerm.Numeral 0) := by
          rfl
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.str_indexof_re (__eo_to_smt x) regex (SmtTerm.Numeral 0)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        have hArgs := str_indexof_re_args_of_non_none hApplyNN
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term._at_strings_stoi_non_digit x)) =
              SmtType.Int := by
          rw [hTranslate, typeof_str_indexof_re_eq]
          simp [hArgs.1, hArgs.2.1, hArgs.2.2, native_Teq, native_ite]
        have hEo :
            __eo_to_smt_type (__eo_typeof (Term._at_strings_stoi_non_digit x)) =
              SmtType.Int := by
          exact eo_to_smt_type_typeof_apply_at_strings_stoi_non_digit_of_seq_char x
            (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x
              (fun h => (go x h).1) hArgs.1)
        refine ⟨hSmt.trans hEo.symm, ?_⟩
        rw [eo_to_smt_type_eq_int hEo]
        simp [eo_type_valid, eo_type_valid_rec]
    | Term._at_strings_itos_result x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term._at_strings_num_occur_re x y, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term._at_strings_occur_index_re x y, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term._at_strings_replace_all_result x, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    | Term._at_const v T, hNonNone => by
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
    termination_by term _ => sizeOf term
    decreasing_by
      all_goals
        subst_vars
        simp_wf
      all_goals
        omega
  exact go t

/-- Direct form of the translation typing theorem. -/
theorem eo_to_smt_typeof_matches_translation
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) := by
  intro hNonNone
  exact (eo_to_smt_typeof_matches_translation_and_valid t hNonNone).1

/--
Post-induction form of EO type recovery from SMT typing.

This is the proof term we want for the deferred recovery theorem once the
remaining early callers are rewritten to use explicit induction hypotheses
instead of importing the full translation theorem.
-/
theorem eo_to_smt_type_typeof_of_smt_type_from_full
    (t : Term) {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof t) = T := by
  have hNonNone : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [h]
    exact hT
  exact (eo_to_smt_typeof_matches_translation t hNonNone).symm.trans h

/--
Compatibility wrapper matching the more explicit theorem shape we used in the
`CpcMini` development.
-/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T := by
  intro hs hNonNone hTy
  subst s
  simpa [hTy] using eo_to_smt_typeof_matches_translation t hNonNone

/-- Transfers EO Boolean typing to the translated SMT term under a defined translation. -/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = Term.Bool ->
    __smtx_typeof s = SmtType.Bool := by
  intro hs hNonNone hTy
  exact eo_to_smt_well_typed_and_typeof_implies_smt_type
    t Term.Bool s hs hNonNone hTy

end TranslationProofs

namespace RuleProofs

/-- Transfers EO typing information to the translated SMT term when the translation is defined. -/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = T ->
  __smtx_typeof s = __eo_to_smt_type T := by
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    t T s

/-- Shows that `eo_to_smt_non_none_and_typeof_bool` implies `smt_bool`. -/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = Term.Bool ->
  __smtx_typeof s = SmtType.Bool := by
  exact TranslationProofs.eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    t s

end RuleProofs
