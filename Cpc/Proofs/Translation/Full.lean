import Cpc.Spec
import Cpc.Proofs.Translation.Datatypes
import Cpc.Proofs.Translation.Apply

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-!
Full translation-proof surface corresponding to the lightweight stub in
`Cpc.Proofs.Translation`.
-/

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
                          rw [__eo_to_smt_exists, __smtx_typeof.eq_134]
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
                          rw [__eo_to_smt_exists, __smtx_typeof.eq_134]
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

/-- Direct form of the translation typing theorem. -/
theorem eo_to_smt_typeof_matches_translation
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) := by
  sorry

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
