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

/-- Computes the EO type of a variable-headed list cons once the tail is a list. -/
private theorem eo_typeof_list_cons_var
    (s : native_String) (T xs : Term)
    (hTail : __eo_typeof xs = Term.__eo_List) :
    __eo_typeof (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs) =
      Term.__eo_List := by
  have hHead :
      __eo_typeof (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) =
        Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List := rfl
  rw [__eo_typeof.eq_def, hHead, hTail, __eo_typeof_apply, __eo_requires]
  simp [native_ite, native_teq, native_not]

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
    (xs : Term) (body : SmtTerm) (n : native_Nat) :
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
                          simp [__eo_to_smt_exists, __smtx_typeof_exists, hBodyBool, native_ite, native_Teq]
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
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists, __smtx_typeof_choice_nth]
                              using hNN
                          have hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                            ih a body hTailNN
                          simp [__eo_to_smt_exists, __smtx_typeof_exists, hTailBool, native_ite, native_Teq]
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

/-- Computes the selected binder type for quantifier skolemization. -/
private theorem eo_to_smt_quantifiers_skolemize_type_of_non_none
    (xs : Term) (body : SmtTerm) (n : native_Nat) :
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
                          exact hTy.trans (by
                            simp [__get_var_type, __eo_list_nth, __eo_list_nth_rec, __eo_requires,
                              __eo_is_list, __eo_get_nil_rec, __eo_is_ok, __eo_typeof.eq_def,
                              native_ite, native_teq, native_not])
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
                            simpa [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists, __smtx_typeof_choice_nth]
                              using hNN
                          have hTailTy :
                              __smtx_typeof (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists a body) n) =
                                __eo_to_smt_type
                                  (__get_var_type
                                    (__eo_list_nth Term.__eo_List_cons a
                                      (Term.Numeral (native_nat_to_int n)))) :=
                            ih a body hTailNN
                          exact hTailTy.trans (by
                            simp [__get_var_type, __eo_list_nth, __eo_list_nth_rec, __eo_requires,
                              __eo_is_list, __eo_get_nil_rec, __eo_is_ok, __eo_typeof.eq_def,
                              __eo_add, native_ite, native_teq, native_not, native_zplus,
                              native_nat_to_int])
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
  let rec go (t : Term) :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) := by
    letI bridge : TranslationBridge := ⟨go⟩
    cases t <;> intro hNonNone
    case UOp op =>
      cases op
      all_goals
        try simp [__eo_to_smt.eq_def] at hNonNone
      case re_allchar =>
          rw [__eo_to_smt.eq_def, eo_typeof_re_allchar, eo_to_smt_type_reglan]
          unfold __smtx_typeof
          rfl
      case re_none =>
          rw [__eo_to_smt.eq_def, eo_typeof_re_none, eo_to_smt_type_reglan]
          unfold __smtx_typeof
          rfl
      case re_all =>
          rw [__eo_to_smt.eq_def, eo_typeof_re_all, eo_to_smt_type_reglan]
          unfold __smtx_typeof
          rfl
      case tuple_unit =>
          simpa [__eo_to_smt.eq_def] using smtx_typeof_tuple_unit_translation
    case __eo_List =>
      simp [__eo_to_smt.eq_def] at hNonNone
    case __eo_List_nil =>
      simp [__eo_to_smt.eq_def] at hNonNone
    case __eo_List_cons =>
      simp [__eo_to_smt.eq_def] at hNonNone
    case Bool =>
      simp [__eo_to_smt.eq_def] at hNonNone
    case Boolean b =>
      rw [__eo_to_smt.eq_def, eo_typeof_boolean, eo_to_smt_type_bool]
      unfold __smtx_typeof
      rfl
    case «Type» =>
      simp [__eo_to_smt.eq_def] at hNonNone
    case Stuck =>
      simp [__eo_to_smt.eq_def] at hNonNone
    case FunType =>
      simp [__eo_to_smt.eq_def] at hNonNone
    case DatatypeType s d =>
      simp [__eo_to_smt.eq_def] at hNonNone
    case DatatypeTypeRef s =>
      simp [__eo_to_smt.eq_def] at hNonNone
    case USort i =>
      simp [__eo_to_smt.eq_def] at hNonNone
    case Numeral n =>
      rw [show __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int by
        simpa [__eo_to_smt.eq_def] using
          (show __smtx_typeof (SmtTerm.Numeral n) = SmtType.Int by
            unfold __smtx_typeof
            rfl)]
      symm
      exact eo_to_smt_type_typeof_numeral n
    case Rational r =>
      rw [show __smtx_typeof (__eo_to_smt (Term.Rational r)) = SmtType.Real by
        simpa [__eo_to_smt.eq_def] using
          (show __smtx_typeof (SmtTerm.Rational r) = SmtType.Real by
            unfold __smtx_typeof
            rfl)]
      symm
      exact eo_to_smt_type_typeof_rational r
    case String s =>
      rw [show __smtx_typeof (__eo_to_smt (Term.String s)) = SmtType.Seq SmtType.Char by
        simpa [__eo_to_smt.eq_def] using
          (show __smtx_typeof (SmtTerm.String s) = SmtType.Seq SmtType.Char by
            unfold __smtx_typeof
            rfl)]
      symm
      exact eo_to_smt_type_typeof_string s
    case Binary w n =>
      have hTy : __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None := by
        simpa [__eo_to_smt.eq_def] using hNonNone
      have hWidth : native_zleq 0 w = true :=
        (smtx_binary_well_formed_of_non_none w n hTy).1
      rw [show __smtx_typeof (__eo_to_smt (Term.Binary w n)) =
        SmtType.BitVec (native_int_to_nat w) by
        simpa [__eo_to_smt.eq_def] using smtx_typeof_binary_of_non_none w n hTy]
      symm
      simpa using eo_to_smt_type_typeof_binary w n hWidth
    case Var name T =>
      cases name
      case String s =>
          have hTy : __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) ≠ SmtType.None := by
            simpa [__eo_to_smt.eq_def] using hNonNone
          rw [show __smtx_typeof (__eo_to_smt (Term.Var (Term.String s) T)) = __eo_to_smt_type T by
            simpa [__eo_to_smt.eq_def] using
              smtx_typeof_var_of_non_none s (__eo_to_smt_type T) hTy]
          symm
          simpa using eo_to_smt_type_typeof_var s T
      all_goals
        exact False.elim (hNonNone (by simp [__eo_to_smt.eq_def]))
    case DtCons s d i =>
      symm
      simpa [eo_to_smt_term_dt_cons] using
        eo_to_smt_type_typeof_dt_cons s d i (by
          simpa [eo_to_smt_term_dt_cons] using hNonNone)
    case DtSel s d i j =>
      have hNone : __smtx_typeof (__eo_to_smt (Term.DtSel s d i j)) = SmtType.None := by
        simpa [__eo_to_smt.eq_def] using
          smtx_typeof_dt_sel_head_none s (__eo_to_smt_datatype d) i j
      exact (hNonNone hNone).elim
    case UConst i T =>
      have hTy :
          __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) ≠
            SmtType.None := by
        simpa [__eo_to_smt.eq_def] using hNonNone
      rw [show __smtx_typeof (__eo_to_smt (Term.UConst i T)) = __eo_to_smt_type T by
        simpa [__eo_to_smt.eq_def] using
          smtx_typeof_uconst_of_non_none (native_uconst_id i) (__eo_to_smt_type T) hTy]
      symm
      simpa using eo_to_smt_type_typeof_uconst i T
    case Apply f x =>
      simpa using eo_to_smt_typeof_matches_translation_apply f x (go f) (go x) hNonNone
    case _at_purify x =>
      have hTranslatePurify : __eo_to_smt (Term._at_purify x) = __eo_to_smt x := by
        rw [__eo_to_smt.eq_def]
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        intro hNone
        apply hNonNone
        rwa [hTranslatePurify]
      have hX := go x hXNonNone
      rw [hTranslatePurify, hX]
      exact (eo_to_smt_type_typeof_purify x).symm
    case _at_array_deq_diff x1 x2 =>
      simpa using eo_to_smt_typeof_matches_translation_array_deq_diff x1 x2 hNonNone
    case seq_empty x =>
      symm
      simpa [__eo_to_smt.eq_def] using eo_to_smt_type_typeof_seq_empty x
        (by simpa [__eo_to_smt.eq_def] using hNonNone)
    case set_empty x =>
      symm
      simpa [__eo_to_smt.eq_def] using eo_to_smt_type_typeof_set_empty x
        (by simpa [__eo_to_smt.eq_def] using hNonNone)
    case _at_sets_deq_diff x1 x2 =>
      simpa using eo_to_smt_typeof_matches_translation_sets_deq_diff x1 x2 hNonNone
    case _at_quantifiers_skolemize x1 x2 =>
      cases x1 with
      | Apply f body =>
          cases f with
          | Apply g xs =>
              cases g with
              | UOp op =>
                  cases op <;> simp [__eo_to_smt.eq_def] at hNonNone
                  case «forall» =>
                      cases x2 with
                      | Numeral n =>
                          by_cases hnNeg : native_zlt n 0 = true
                          · simp [__eo_to_smt.eq_def, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
                              __eo_to_smt_nat, hnNeg, native_ite] at hNonNone
                          · have hChoiceNN :
                                __smtx_typeof
                                    (__eo_to_smt_quantifiers_skolemize
                                      (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                                      (native_int_to_nat n)) ≠
                                  SmtType.None := by
                              simpa [__eo_to_smt.eq_def, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
                                __eo_to_smt_nat, hnNeg, native_ite] using hNonNone
                            have hExistsBool :
                                __smtx_typeof
                                    (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body))) =
                                  SmtType.Bool :=
                              eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
                                xs (SmtTerm.not (__eo_to_smt body)) (native_int_to_nat n) hChoiceNN
                            have hNotTy :
                                __smtx_typeof (SmtTerm.not (__eo_to_smt body)) = SmtType.Bool :=
                              eo_to_smt_exists_body_bool_of_bool xs (SmtTerm.not (__eo_to_smt body))
                                hExistsBool
                            have hBodySmt : __smtx_typeof (__eo_to_smt body) = SmtType.Bool := by
                              rw [typeof_not_eq] at hNotTy
                              cases hTy : __smtx_typeof (__eo_to_smt body) <;>
                                simp [native_ite, native_Teq, hTy] at hNotTy
                              rfl
                            have hBodyNN : __smtx_typeof (__eo_to_smt body) ≠ SmtType.None := by
                              rw [hBodySmt]
                              simp
                            have hBodyTranslate := go body hBodyNN
                            have hBodyEO : __eo_typeof body = Term.Bool := by
                              apply eo_to_smt_type_eq_bool
                              rw [← hBodyTranslate]
                              exact hBodySmt
                            have hXsEO : __eo_typeof xs = Term.__eo_List :=
                              eo_typeof_var_list_of_exists_bool xs (SmtTerm.not (__eo_to_smt body))
                                hExistsBool
                            have hForallEO :
                                __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) =
                                  Term.Bool := by
                              simpa [__eo_typeof.eq_def, __eo_typeof_forall, hXsEO, hBodyEO]
                            have hNonneg : 0 <= n := by
                              have hNotLt : ¬ n < 0 := by
                                simpa [SmtEval.native_zlt] using hnNeg
                              exact Int.le_of_not_gt hNotLt
                            have hSmt :
                                __smtx_typeof
                                    (__eo_to_smt
                                      (Term._at_quantifiers_skolemize
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
                                        (Term.Numeral n))) =
                                  __eo_to_smt_type
                                    (__get_var_type
                                      (__eo_list_nth Term.__eo_List_cons xs (Term.Numeral n))) := by
                              simpa [__eo_to_smt.eq_def, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
                                __eo_to_smt_nat, hnNeg, native_ite, SmtEval.native_nat_to_int,
                                SmtEval.native_int_to_nat, Int.toNat_of_nonneg hNonneg] using
                                eo_to_smt_quantifiers_skolemize_type_of_non_none
                                  xs (SmtTerm.not (__eo_to_smt body)) (native_int_to_nat n) hChoiceNN
                            have hEo :
                                __eo_to_smt_type
                                    (__eo_typeof
                                      (Term._at_quantifiers_skolemize
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
                                        (Term.Numeral n))) =
                                  __eo_to_smt_type
                                    (__get_var_type
                                      (__eo_list_nth Term.__eo_List_cons xs (Term.Numeral n))) := by
                              have hRound :
                                  native_nat_to_int (native_int_to_nat n) = n := by
                                simp [SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
                                  Int.toNat_of_nonneg hNonneg]
                              simpa [__eo_typeof.eq_def, __eo_typeof__at_quantifiers_skolemize, hForallEO,
                                hRound]
                            exact hSmt.trans hEo.symm
                      | _ =>
                          exfalso
                          simp [__eo_to_smt.eq_def, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
                            __eo_to_smt_nat, native_ite] at hNonNone
              | _ =>
                  exfalso
                  simp [__eo_to_smt.eq_def] at hNonNone
          | _ =>
              exfalso
              simp [__eo_to_smt.eq_def] at hNonNone
      | _ =>
          exfalso
          simp [__eo_to_smt.eq_def] at hNonNone
    all_goals
      first
        | exact False.elim (hNonNone (by simp [__eo_to_smt.eq_def]))
        | native_decide
  exact go t

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
