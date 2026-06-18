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

private def quantUnusedFormula (Q x F G : Term) : Term :=
  qeq (qterm Q x F) G

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

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  cases h : __smtx_typeof t <;>
    simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢

private theorem smtx_typeof_not_bool_of_arg_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

private theorem smtx_typeof_none_ne_bool :
    __smtx_typeof SmtTerm.None ≠ SmtType.Bool := by
  simp [TranslationProofs.smtx_typeof_none]

private theorem smtx_typeof_exists_bool_or_none_local
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.exists s T body) = SmtType.None := by
  rw [smtx_typeof_exists_term_eq]
  cases hBody : __smtx_typeof body <;>
    simp [native_ite, native_Teq]
  cases hWf : __smtx_type_wf T <;>
    simp [__smtx_typeof_guard_wf, native_ite, hWf]

private theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply
            (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
            xs)
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
          (Term.Apply
            (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
            xs)
          body) = SmtType.Bool ->
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro hTy
  have hTail :
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
    smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool ≠
        SmtType.None := by
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

private theorem smtx_typeof_qexists_bool_or_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.None := by
  unfold qexists qterm
  cases x
  case __eo_List_nil =>
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
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
                      (__eo_to_smt_exists tail (__eo_to_smt F))) =
                  SmtType.Bool ∨
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt F))) =
                  SmtType.None
            exact smtx_typeof_exists_bool_or_none_local s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail (__eo_to_smt F))
          all_goals
            right
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact TranslationProofs.smtx_typeof_none
        all_goals
          right
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      all_goals
        right
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    all_goals
      right
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  all_goals
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

private theorem eo_to_smt_exists_bool_env :
    ∀ (xs : Term) (body : SmtTerm),
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
        ∃ vars, EoSmtVarEnv xs vars
  | Term.__eo_List_nil, _body, _hTy =>
      by
        exact ⟨[], EoSmtVarEnv.nil⟩
  | Term.Apply f tail, body, hTy =>
      by
        cases f
        case Apply g head =>
          cases g
          case __eo_List_cons =>
            cases head
            case Var name T =>
              cases name
              case String s =>
                have hExistsTy :
                    __smtx_typeof
                        (SmtTerm.exists s (__eo_to_smt_type T)
                          (__eo_to_smt_exists tail body)) =
                      SmtType.Bool := by
                  simpa [__eo_to_smt_exists] using hTy
                have hNN :
                    term_has_non_none_type
                      (SmtTerm.exists s (__eo_to_smt_type T)
                        (__eo_to_smt_exists tail body)) := by
                  unfold term_has_non_none_type
                  rw [hExistsTy]
                  simp
                have hTailTy :
                    __smtx_typeof (__eo_to_smt_exists tail body) =
                      SmtType.Bool :=
                  exists_body_bool_of_non_none hNN
                rcases eo_to_smt_exists_bool_env tail body hTailTy with
                  ⟨vars, hEnv⟩
                exact ⟨(s, __eo_to_smt_type T) :: vars,
                  EoSmtVarEnv.cons hEnv⟩
              all_goals
                have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
                  simpa [__eo_to_smt_exists] using hTy
                exact False.elim (smtx_typeof_none_ne_bool hNone)
            all_goals
              have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
                simpa [__eo_to_smt_exists] using hTy
              exact False.elim (smtx_typeof_none_ne_bool hNone)
          all_goals
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            exact False.elim (smtx_typeof_none_ne_bool hNone)
        all_goals
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simpa [__eo_to_smt_exists] using hTy
          exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.UOp _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.UOp1 _ _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.UOp2 _ _ _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.UOp3 _ _ _ _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.__eo_List, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.__eo_List_cons, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.Bool, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.Boolean _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.Numeral _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.Rational _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.String _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.Binary _ _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.Type, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.Stuck, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.FunType, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.Var _ _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.DatatypeType _ _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.DatatypeTypeRef _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.DtcAppType _ _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.DtCons _ _ _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.DtSel _ _ _ _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.USort _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
  | Term.UConst _ _, _body, hTy =>
      by
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)

private theorem eo_to_smt_exists_top_bool_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool := by
  rcases smtx_typeof_qexists_bool_or_none x F with hBool | hNone
  · exact hBool
  · exact False.elim (hNN hNone)

private theorem qexists_non_nil_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None) :
    x ≠ Term.__eo_List_nil := by
  intro hx
  subst x
  apply hNN
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_non_nil_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None) :
    x ≠ Term.__eo_List_nil := by
  intro hx
  subst x
  apply hNN
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_inner_exists_bool_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
      SmtType.Bool := by
  have hx : x ≠ Term.__eo_List_nil := qforall_non_nil_of_non_none x F hNN
  have hNN' := hNN
  rw [eo_to_smt_forall_eq x F hx] at hNN'
  exact smtx_typeof_not_arg_of_non_none
    (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) hNN'

private theorem qforall_top_bool_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
  have hx : x ≠ Term.__eo_List_nil := qforall_non_nil_of_non_none x F hNN
  rw [eo_to_smt_forall_eq x F hx]
  exact smtx_typeof_not_bool_of_arg_bool _
    (qforall_inner_exists_bool_of_non_none x F hNN)

private theorem qterm_top_bool_of_non_none
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNN : __smtx_typeof (__eo_to_smt (qterm Q x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool := by
  rcases hQ with hQ | hQ
  · subst Q
    exact qforall_top_bool_of_non_none x F hNN
  · subst Q
    exact eo_to_smt_exists_top_bool_of_non_none x F hNN

private theorem qterm_binder_env_of_bool
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool) :
    ∃ vars, EoSmtVarEnv x vars := by
  rcases hQ with hQ | hQ
  · subst Q
    have hTyForall :
        __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
      simpa [qforall] using hTy
    have hNN :
        __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None := by
      rw [hTyForall]
      simp
    have hExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool :=
      qforall_inner_exists_bool_of_non_none x F hNN
    exact eo_to_smt_exists_bool_env x (SmtTerm.not (__eo_to_smt F)) hExistsTy
  · subst Q
    have hTyExists :
        __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool := by
      simpa [qexists] using hTy
    have hNN :
        __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None := by
      rw [hTyExists]
      simp
    have hx : x ≠ Term.__eo_List_nil :=
      qexists_non_nil_of_non_none x F hNN
    rw [eo_to_smt_exists_eq x F hx] at hTyExists
    exact eo_to_smt_exists_bool_env x (__eo_to_smt F) hTyExists

private theorem get_unused_vars_not_stuck_of_no_free
    (Q x F G : Term)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false) :
    __get_unused_vars (qterm Q x F) G ≠ Term.Stuck := by
  intro h
  rw [h] at hNoFree
  cases G <;> simp [__contains_atomic_term_list_free_rec] at hNoFree

private theorem smtx_eval_exists_unused_of_body_invariant
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hInv : ∀ v,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.exists s T body) =
      __smtx_model_eval M body := by
  classical
  rcases Smtm.canonical_type_inhabited_of_type_wf T hWF with
    ⟨w, hwTy, hwCan⟩
  have hwCanBool : __smtx_value_canonical_bool w = true := by
    simpa [value_canonical_bool_eq_true] using hwCan
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with ⟨b, hb⟩
  let P : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true
  cases b
  · have hNotP : ¬ P := by
      intro hP
      rcases hP with ⟨v, hvTy, hvCan, hvEval⟩
      have hEval := hInv v hvTy hvCan
      rw [hb] at hEval
      rw [hEval] at hvEval
      cases hvEval
    simp [__smtx_model_eval, P, hNotP, hb]
  · have hP : P := by
      refine ⟨w, hwTy, hwCanBool, ?_⟩
      rw [hInv w hwTy hwCanBool]
      exact hb
    simp [__smtx_model_eval, P, hP, hb]

private theorem smtx_eval_not_not_of_bool
    (M : SmtModel) (hM : model_total_typed M)
    (body : SmtTerm)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
    __smtx_model_eval M (SmtTerm.not (SmtTerm.not body)) =
      __smtx_model_eval M body := by
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with ⟨b, hb⟩
  cases b <;>
    simp [__smtx_model_eval, hb, __smtx_model_eval_not, SmtEval.native_not]

private theorem smtx_eval_forall_unused_of_body_invariant
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hInv : ∀ v,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M
        (SmtTerm.not (SmtTerm.exists s T (SmtTerm.not body))) =
      __smtx_model_eval M body := by
  have hNotTy : __smtx_typeof (SmtTerm.not body) = SmtType.Bool := by
    rw [typeof_not_eq]
    simp [hBodyTy, native_ite, native_Teq]
  have hExists :
      __smtx_model_eval M (SmtTerm.exists s T (SmtTerm.not body)) =
        __smtx_model_eval M (SmtTerm.not body) := by
    apply smtx_eval_exists_unused_of_body_invariant M hM s T
      (SmtTerm.not body) hWF hNotTy
    intro v hvTy hvCan
    simp [__smtx_model_eval, hInv v hvTy hvCan]
  rw [__smtx_model_eval.eq_6, hExists]
  simpa [__smtx_model_eval] using
    smtx_eval_not_not_of_bool M hM body hBodyTy

private theorem model_agrees_on_env_push_of_not_mem
    (vars : List SmtVarKey) (M : SmtModel)
    (s : native_String) (T : SmtType) (v : SmtValue)
    (hNotMem : (s, T) ∉ vars) :
    model_agrees_on_env vars M (native_model_push M s T v) := by
  refine ⟨model_agrees_on_globals_push M s T v, ?_⟩
  intro s' T' hMem
  by_cases hKey :
      ({ isVar := true, name := s', ty := T' } : SmtModelKey) =
        { isVar := true, name := s, ty := T }
  · cases hKey
    exact False.elim (hNotMem hMem)
  · simp [native_model_var_lookup, native_model_push, hKey]

private theorem smt_model_eval_push_eq_of_closedIn_not_mem
    (t : SmtTerm) (vars : List SmtVarKey) (M : SmtModel)
    (s : native_String) (T : SmtType) (v : SmtValue)
    (hClosed : SmtTermClosedIn vars t)
    (hNotMem : (s, T) ∉ vars) :
    __smtx_model_eval (native_model_push M s T v) t =
      __smtx_model_eval M t := by
  exact (smt_model_eval_eq_of_closedIn t vars M
    (native_model_push M s T v) hClosed
    (model_agrees_on_env_push_of_not_mem vars M s T v hNotMem)).symm

private theorem smtx_eval_exists_unused_of_closedIn_not_mem
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (vars : List SmtVarKey)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hClosed : SmtTermClosedIn vars body)
    (hNotMem : (s, T) ∉ vars) :
    __smtx_model_eval M (SmtTerm.exists s T body) =
      __smtx_model_eval M body := by
  apply smtx_eval_exists_unused_of_body_invariant M hM s T body hWF hBodyTy
  intro v _hvTy _hvCan
  exact smt_model_eval_push_eq_of_closedIn_not_mem
    body vars M s T v hClosed hNotMem

private theorem smtx_eval_forall_unused_of_closedIn_not_mem
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (vars : List SmtVarKey)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hClosed : SmtTermClosedIn vars body)
    (hNotMem : (s, T) ∉ vars) :
    __smtx_model_eval M
        (SmtTerm.not (SmtTerm.exists s T (SmtTerm.not body))) =
      __smtx_model_eval M body := by
  apply smtx_eval_forall_unused_of_body_invariant M hM s T body hWF hBodyTy
  intro v _hvTy _hvCan
  exact smt_model_eval_push_eq_of_closedIn_not_mem
    body vars M s T v hClosed hNotMem

private theorem smtx_eval_qexists_single_unused_of_closedIn_not_mem
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T F : Term) (vars : List SmtVarKey)
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (hClosed : SmtTermClosedIn vars (__eo_to_smt F))
    (hNotMem : (s, __eo_to_smt_type T) ∉ vars) :
    __smtx_model_eval M
        (__eo_to_smt
          (qexists
            (Term.Apply
              (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
              Term.__eo_List_nil) F)) =
      __smtx_model_eval M (__eo_to_smt F) := by
  change
    __smtx_model_eval M
        (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt F)) =
      __smtx_model_eval M (__eo_to_smt F)
  exact smtx_eval_exists_unused_of_closedIn_not_mem M hM s
    (__eo_to_smt_type T) (__eo_to_smt F) vars hWF hBodyTy hClosed hNotMem

private theorem smtx_eval_qforall_single_unused_of_closedIn_not_mem
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T F : Term) (vars : List SmtVarKey)
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (hClosed : SmtTermClosedIn vars (__eo_to_smt F))
    (hNotMem : (s, __eo_to_smt_type T) ∉ vars) :
    __smtx_model_eval M
        (__eo_to_smt
          (qforall
            (Term.Apply
              (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
              Term.__eo_List_nil) F)) =
      __smtx_model_eval M (__eo_to_smt F) := by
  change
    __smtx_model_eval M
        (SmtTerm.not
          (SmtTerm.exists s (__eo_to_smt_type T)
            (SmtTerm.not (__eo_to_smt F)))) =
      __smtx_model_eval M (__eo_to_smt F)
  exact smtx_eval_forall_unused_of_closedIn_not_mem M hM s
    (__eo_to_smt_type T) (__eo_to_smt F) vars hWF hBodyTy hClosed hNotMem

private theorem smtTermClosedIn_eo_to_smt_exists_of_body_closed
    (xs : Term) (body : SmtTerm) (vars : List SmtVarKey)
    (hClosed : SmtTermClosedIn vars body) :
    SmtTermClosedIn vars (__eo_to_smt_exists xs body) := by
  exact smtTermClosedIn_eo_to_smt_exists_of_env_or_none
    (vs := xs) (vars := vars) (F := body)
    (by
      intro binderVars _hEnv
      exact SmtTermClosedIn.mono
        (t := body) (vars := vars) (vars' := binderVars.reverse ++ vars)
        (by
          intro s T hMem
          exact List.mem_append.2 (Or.inr hMem))
        hClosed)

private theorem smtx_eval_eo_to_smt_exists_unused_of_closedIn_not_mem :
    ∀ (xs : Term) (M : SmtModel),
      model_total_typed M ->
      ∀ (body : SmtTerm) (vars : List SmtVarKey),
        __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
        SmtTermClosedIn vars body ->
        (∀ s T,
          EoSmtVarEnvTermMem (Term.Var (Term.String s) T) xs ->
            (s, __eo_to_smt_type T) ∉ vars) ->
        __smtx_model_eval M (__eo_to_smt_exists xs body) =
          __smtx_model_eval M body
  | Term.__eo_List_nil, M, _hM, body, _vars, _hTy, _hClosed, _hNotMem =>
      by
        rfl
  | Term.Apply f tail, M, hM, body, vars, hTy, hClosed, hNotMem =>
      by
        cases f
        case Apply g head =>
          cases g
          case __eo_List_cons =>
            cases head
            case Var name T =>
              cases name
              case String s =>
                have hTailTy :
                    __smtx_typeof (__eo_to_smt_exists tail body) =
                      SmtType.Bool :=
                  smtx_typeof_exists_tail_bool_of_cons_bool s T tail body hTy
                have hWF :
                    __smtx_type_wf (__eo_to_smt_type T) = true :=
                  smtx_type_wf_of_exists_cons_bool s T tail body hTy
                have hClosedTail :
                    SmtTermClosedIn vars
                      (__eo_to_smt_exists tail body) :=
                  smtTermClosedIn_eo_to_smt_exists_of_body_closed
                    tail body vars hClosed
                have hHeadNotMem :
                    (s, __eo_to_smt_type T) ∉ vars :=
                  hNotMem s T (Or.inl rfl)
                have hHeadEval :
                    __smtx_model_eval M
                        (__eo_to_smt_exists
                          (Term.Apply
                            (Term.Apply Term.__eo_List_cons
                              (Term.Var (Term.String s) T))
                            tail)
                          body) =
                      __smtx_model_eval M
                        (__eo_to_smt_exists tail body) := by
                  change
                    __smtx_model_eval M
                        (SmtTerm.exists s (__eo_to_smt_type T)
                          (__eo_to_smt_exists tail body)) =
                      __smtx_model_eval M
                        (__eo_to_smt_exists tail body)
                  exact smtx_eval_exists_unused_of_closedIn_not_mem M hM s
                    (__eo_to_smt_type T) (__eo_to_smt_exists tail body)
                    vars hWF hTailTy hClosedTail hHeadNotMem
                rw [hHeadEval]
                exact
                  smtx_eval_eo_to_smt_exists_unused_of_closedIn_not_mem
                    tail M hM body vars hTailTy hClosed
                    (by
                      intro s' T' hTailMem
                      exact hNotMem s' T' (Or.inr hTailMem))
              all_goals
                change __smtx_model_eval M SmtTerm.None =
                  __smtx_model_eval M body
                simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
                  using hTy
            all_goals
              change __smtx_model_eval M SmtTerm.None =
                __smtx_model_eval M body
              simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
                using hTy
          all_goals
            change __smtx_model_eval M SmtTerm.None =
              __smtx_model_eval M body
            simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
              using hTy
        all_goals
          change __smtx_model_eval M SmtTerm.None =
            __smtx_model_eval M body
          simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
            using hTy
  | Term.UOp _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.UOp1 _ _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.UOp2 _ _ _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.UOp3 _ _ _ _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.__eo_List, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.__eo_List_cons, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.Bool, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.Boolean _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.Numeral _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.Rational _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.String _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.Binary _ _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.Type, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.Stuck, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.FunType, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.Var _ _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.DatatypeType _ _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.DatatypeTypeRef _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.DtcAppType _ _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.DtCons _ _ _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.DtSel _ _ _ _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.USort _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy
  | Term.UConst _ _, M, _hM, body, _vars, hTy, _hClosed, _hNotMem =>
      by
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval M body
        simpa [__eo_to_smt_exists, TranslationProofs.smtx_typeof_none]
          using hTy

private theorem smtx_eval_eo_to_smt_forall_unused_of_closedIn_not_mem
    (xs : Term) (M : SmtModel) (hM : model_total_typed M)
    (body : SmtTerm) (vars : List SmtVarKey)
    (hExistsTy :
      __smtx_typeof (__eo_to_smt_exists xs (SmtTerm.not body)) =
        SmtType.Bool)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hClosed : SmtTermClosedIn vars body)
    (hNotMem :
      ∀ s T,
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) xs ->
          (s, __eo_to_smt_type T) ∉ vars) :
    __smtx_model_eval M
        (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
      __smtx_model_eval M body := by
  have hExistsEval :
      __smtx_model_eval M
          (__eo_to_smt_exists xs (SmtTerm.not body)) =
        __smtx_model_eval M (SmtTerm.not body) :=
    smtx_eval_eo_to_smt_exists_unused_of_closedIn_not_mem
      xs M hM (SmtTerm.not body) vars hExistsTy hClosed hNotMem
  rw [smtx_eval_not_term_eq, hExistsEval]
  simpa [smtx_eval_not_term_eq] using
    smtx_eval_not_not_of_bool M hM body hBodyTy

private theorem smtx_eval_qexists_unused_of_closedIn_not_mem
    (M : SmtModel) (hM : model_total_typed M)
    (x F : Term) (vars : List SmtVarKey)
    (hTy : __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool)
    (hClosed : SmtTermClosedIn vars (__eo_to_smt F))
    (hNotMem :
      ∀ s T,
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) x ->
          (s, __eo_to_smt_type T) ∉ vars) :
    __smtx_model_eval M (__eo_to_smt (qexists x F)) =
      __smtx_model_eval M (__eo_to_smt F) := by
  have hNN : __smtx_typeof (__eo_to_smt (qexists x F)) ≠
      SmtType.None := by
    rw [hTy]
    simp
  have hx : x ≠ Term.__eo_List_nil :=
    qexists_non_nil_of_non_none x F hNN
  rw [eo_to_smt_exists_eq x F hx] at hTy ⊢
  exact smtx_eval_eo_to_smt_exists_unused_of_closedIn_not_mem
    x M hM (__eo_to_smt F) vars hTy hClosed hNotMem

private theorem smtx_eval_qforall_unused_of_closedIn_not_mem
    (M : SmtModel) (hM : model_total_typed M)
    (x F : Term) (vars : List SmtVarKey)
    (hTy : __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool)
    (hBodyTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (hClosed : SmtTermClosedIn vars (__eo_to_smt F))
    (hNotMem :
      ∀ s T,
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) x ->
          (s, __eo_to_smt_type T) ∉ vars) :
    __smtx_model_eval M (__eo_to_smt (qforall x F)) =
      __smtx_model_eval M (__eo_to_smt F) := by
  have hNN : __smtx_typeof (__eo_to_smt (qforall x F)) ≠
      SmtType.None := by
    rw [hTy]
    simp
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F hNN
  have hExistsTy :
      __smtx_typeof (__eo_to_smt_exists x
          (SmtTerm.not (__eo_to_smt F))) = SmtType.Bool :=
    qforall_inner_exists_bool_of_non_none x F hNN
  rw [eo_to_smt_forall_eq x F hx]
  exact smtx_eval_eo_to_smt_forall_unused_of_closedIn_not_mem
    x M hM (__eo_to_smt F) vars hExistsTy hBodyTy hClosed hNotMem

private theorem smtx_model_eval_eo_to_smt_exists_eq_of_rel
    (R : SmtModel -> SmtModel -> Prop)
    (body : SmtTerm)
    (hPush :
      ∀ M N s T v,
        R M N ->
          R (native_model_push M s T v) (native_model_push N s T v))
    (hBody :
      ∀ M N, R M N ->
        __smtx_model_eval M body = __smtx_model_eval N body) :
    ∀ xs M N,
      R M N ->
        __smtx_model_eval M (__eo_to_smt_exists xs body) =
          __smtx_model_eval N (__eo_to_smt_exists xs body)
  | Term.__eo_List_nil, M, N, hRel => by
      simpa [__eo_to_smt_exists] using hBody M N hRel
  | Term.Apply f tail, M, N, hRel => by
      cases f
      case Apply g head =>
        cases g
        case __eo_List_cons =>
          cases head
          case Var name T =>
            cases name
            case String s =>
              change
                __smtx_model_eval M
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail body)) =
                  __smtx_model_eval N
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail body))
              exact smtx_model_eval_exists_eq_of_body_eval_eq
                (fun v =>
                  smtx_model_eval_eo_to_smt_exists_eq_of_rel
                    R body hPush hBody tail
                    (native_model_push M s (__eo_to_smt_type T) v)
                    (native_model_push N s (__eo_to_smt_type T) v)
                    (hPush M N s (__eo_to_smt_type T) v hRel))
            all_goals
              simp [__eo_to_smt_exists, __smtx_model_eval]
          all_goals
            simp [__eo_to_smt_exists, __smtx_model_eval]
        all_goals
          simp [__eo_to_smt_exists, __smtx_model_eval]
      all_goals
        simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.UOp _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.UOp1 _ _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.UOp2 _ _ _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.UOp3 _ _ _ _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.__eo_List, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.__eo_List_cons, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Bool, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Boolean _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Numeral _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Rational _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.String _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Binary _ _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Type, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Stuck, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.FunType, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Var _ _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.DatatypeType _ _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.DatatypeTypeRef _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.DtcAppType _ _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.DtCons _ _ _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.DtSel _ _ _ _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.USort _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.UConst _ _, M, N, _hRel => by
      simp [__eo_to_smt_exists, __smtx_model_eval]

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

private theorem eo_ite_false_cases (c e : Term) :
    __eo_ite c (Term.Boolean false) e = Term.Boolean false ->
    c = Term.Boolean true ∨ e = Term.Boolean false := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h
  case Boolean b =>
    cases b
    · exact Or.inr (by simpa using h rfl)
    · exact Or.inl rfl

private theorem eo_ite_true_eq_false (c e : Term) :
    __eo_ite c (Term.Boolean true) e = Term.Boolean false ->
    c = Term.Boolean false ∧ e = Term.Boolean false := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h
  case Boolean b =>
    cases b <;> simp at h
    exact ⟨rfl, h⟩

private theorem eo_requires_false_eq_false_guard_true (x : Term) :
    __eo_requires x (Term.Boolean true) (Term.Boolean false) =
      Term.Boolean false ->
    x = Term.Boolean true := by
  intro h
  cases x <;> simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at h
  case Boolean b =>
    cases b <;> simp at h ⊢

private theorem contains_atomic_var_false_cases
    (name T xs bvs : Term)
    (h :
      __contains_atomic_term_list_free_rec (Term.Var name T) xs bvs =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons xs (Term.Var name T)) =
      Term.Boolean true ∨
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons bvs (Term.Var name T)) =
      Term.Boolean false := by
  cases xs <;> cases bvs <;>
    simp [__contains_atomic_term_list_free_rec] at h ⊢
  all_goals exact eo_ite_false_cases _ _ h

private theorem contains_atomic_binder_body_false
    (q x ys a xs bvs : Term)
    (h :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
            a)
          xs bvs = Term.Boolean false) :
      __contains_atomic_term_list_free_rec a xs
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons x) ys) bvs) =
      Term.Boolean false := by
  cases xs <;> cases bvs <;>
    simpa [__contains_atomic_term_list_free_rec] using h

private theorem contains_atomic_atom_false_is_closed_rec
    (t xs bvs : Term)
    (hNotApply : ∀ f a, t ≠ Term.Apply f a)
    (hNotVar : ∀ name T, t ≠ Term.Var name T)
    (h :
      __contains_atomic_term_list_free_rec t xs bvs =
        Term.Boolean false) :
    __is_closed_rec t Term.__eo_List_nil = Term.Boolean true := by
  cases t
  case Stuck =>
    cases xs <;> simp [__contains_atomic_term_list_free_rec] at h
  case Apply f a =>
    exact False.elim (hNotApply f a rfl)
  case Var name T =>
    exact False.elim (hNotVar name T rfl)
  all_goals
    apply eo_requires_false_eq_false_guard_true
    cases xs <;> cases bvs <;>
      simpa [__contains_atomic_term_list_free_rec] using h

private def model_agrees_for_free_check
    (xs bvs : Term) (M N : SmtModel) : Prop :=
  model_agrees_on_globals M N ∧
    ∀ s T,
      (__eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T)) =
        Term.Boolean true ∨
        __eo_is_neg
          (__eo_list_find Term.__eo_List_cons bvs
            (Term.Var (Term.String s) T)) =
        Term.Boolean false) ->
      native_model_var_lookup M s (__eo_to_smt_type T) =
        native_model_var_lookup N s (__eo_to_smt_type T)

private theorem model_agrees_on_globals_symm
    {M N : SmtModel} :
    model_agrees_on_globals M N ->
      model_agrees_on_globals N M := by
  intro hAgree
  exact ⟨by intro s T; exact (hAgree.1 s T).symm,
    by intro fid T U; exact (hAgree.2 fid T U).symm⟩

private theorem model_agrees_for_free_check_refl
    (xs bvs : Term) (M : SmtModel) :
    model_agrees_for_free_check xs bvs M M := by
  exact ⟨model_agrees_on_globals_refl M, by intro s T _h; rfl⟩

private theorem model_agrees_for_free_check_symm
    (xs bvs : Term) (M N : SmtModel)
    (hAgree : model_agrees_for_free_check xs bvs M N) :
    model_agrees_for_free_check xs bvs N M := by
  refine ⟨model_agrees_on_globals_symm hAgree.1, ?_⟩
  intro s T hFree
  exact (hAgree.2 s T hFree).symm

private theorem model_agrees_for_free_check_trans
    (xs bvs : Term) (M N K : SmtModel)
    (hMN : model_agrees_for_free_check xs bvs M N)
    (hNK : model_agrees_for_free_check xs bvs N K) :
    model_agrees_for_free_check xs bvs M K := by
  refine ⟨model_agrees_on_globals_trans hMN.1 hNK.1, ?_⟩
  intro s T hFree
  exact (hMN.2 s T hFree).trans (hNK.2 s T hFree)

private theorem model_agrees_for_free_check_push_same
    (xs bvs : Term) (M N : SmtModel)
    (s : native_String) (T : SmtType) (v : SmtValue)
    (hAgree : model_agrees_for_free_check xs bvs M N) :
    model_agrees_for_free_check xs bvs
      (native_model_push M s T v) (native_model_push N s T v) := by
  refine ⟨model_agrees_on_globals_push₂ hAgree.1, ?_⟩
  intro s' T' hFree
  by_cases hKey :
      ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
        SmtModelKey) =
        { isVar := true, name := s, ty := T }
  · cases hKey
    simp [native_model_var_lookup, native_model_push]
  · simpa [native_model_var_lookup, native_model_push, hKey]
      using hAgree.2 s' T' hFree

private theorem smt_model_eval_var_string_eq_of_free_check
    (s : native_String) (T xs bvs : Term) (M N : SmtModel)
    (hAgree : model_agrees_for_free_check xs bvs M N)
    (hCheck :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) xs bvs =
        Term.Boolean false) :
    __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
      __smtx_model_eval N (__eo_to_smt (Term.Var (Term.String s) T)) := by
  rw [TranslationProofs.eo_to_smt_var,
    smtx_eval_var_term_eq, smtx_eval_var_term_eq]
  exact hAgree.2 s T
    (contains_atomic_var_false_cases (Term.String s) T xs bvs hCheck)

private theorem get_unused_vars_quant_match
    (Q x F y : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hF : F ≠ Term.Stuck)
    (h :
      __get_unused_vars (qterm Q x F) (qterm Q y F) ≠ Term.Stuck) :
    __eo_list_minclude Term.__eo_List_cons
        (__eo_list_setof Term.__eo_List_cons x) y =
      Term.Boolean true ∧
    __get_unused_vars (qterm Q x F) (qterm Q y F) =
      __eo_list_diff Term.__eo_List_cons
        (__eo_list_setof Term.__eo_List_cons x) y := by
  rcases hQ with hQ | hQ <;> subst Q
  · let set := __eo_list_setof Term.__eo_List_cons x
    let diff := __eo_list_diff Term.__eo_List_cons set y
    have hReq :
        __eo_requires (__eo_list_minclude Term.__eo_List_cons set y)
            (Term.Boolean true) diff ≠ Term.Stuck := by
      simpa [qterm, __get_unused_vars, set, diff, __eo_and, __eo_eq,
        __eo_ite, native_ite, native_teq] using h
    have hIncl :
        __eo_list_minclude Term.__eo_List_cons set y = Term.Boolean true :=
      eq_of_requires_ne_stuck hReq
    have hGuard :
        __eo_and
            (__eo_eq (Term.UOp UserOp.forall) (Term.UOp UserOp.forall))
            (__eo_eq F F) =
          Term.Boolean true := by
      simp [__eo_and, __eo_eq, native_teq, native_and]
    constructor
    · simpa [set] using hIncl
    · simpa [qterm, __get_unused_vars, set, diff, hIncl, hGuard,
        __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not]
  · let set := __eo_list_setof Term.__eo_List_cons x
    let diff := __eo_list_diff Term.__eo_List_cons set y
    have hReq :
        __eo_requires (__eo_list_minclude Term.__eo_List_cons set y)
            (Term.Boolean true) diff ≠ Term.Stuck := by
      simpa [qterm, __get_unused_vars, set, diff, __eo_and, __eo_eq,
        __eo_ite, native_ite, native_teq] using h
    have hIncl :
        __eo_list_minclude Term.__eo_List_cons set y = Term.Boolean true :=
      eq_of_requires_ne_stuck hReq
    have hGuard :
        __eo_and
            (__eo_eq (Term.UOp UserOp.exists) (Term.UOp UserOp.exists))
            (__eo_eq F F) =
          Term.Boolean true := by
      simp [__eo_and, __eo_eq, native_teq, native_and]
    constructor
    · simpa [set] using hIncl
    · simpa [qterm, __get_unused_vars, set, diff, hIncl, hGuard,
        __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not]

private theorem get_unused_vars_fallback_eq_of_not_stuck
    (Q x F G : Term)
    (h :
      __eo_l_1___get_unused_vars (qterm Q x F) G ≠ Term.Stuck) :
    G = F ∧
    __eo_l_1___get_unused_vars (qterm Q x F) G =
      __eo_list_setof Term.__eo_List_cons x := by
  by_cases hG : G = Term.Stuck
  · subst G
    simp [__eo_l_1___get_unused_vars] at h
  have hReq :
      __eo_requires (__eo_eq F G) (Term.Boolean true)
          (__eo_list_setof Term.__eo_List_cons x) ≠ Term.Stuck := by
    cases G <;> simp [qterm, __eo_l_1___get_unused_vars] at hG h ⊢
    all_goals exact h
  have hEq : __eo_eq F G = Term.Boolean true :=
    eq_of_requires_ne_stuck hReq
  have hGF : G = F :=
    RuleProofs.eq_of_eo_eq_true F G hEq
  constructor
  · exact hGF
  · subst G
    simpa [qterm, __eo_l_1___get_unused_vars, __eo_eq,
      __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] using h

private theorem no_self_apply_apply (Q y F : Term) :
    F ≠ Term.Apply (Term.Apply Q y) F := by
  intro h
  have hs := congrArg sizeOf h
  simp at hs

private theorem eo_eq_bool_of_ne_stuck {x y : Term}
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    ∃ b, __eo_eq x y = Term.Boolean b := by
  cases x <;> cases y <;>
    simp [__eo_eq] at hx hy ⊢

private theorem get_unused_vars_quant_body
    (Q x F : Term)
    (hF : F ≠ Term.Stuck)
    (h :
      __get_unused_vars (qterm Q x F) F ≠ Term.Stuck) :
    __get_unused_vars (qterm Q x F) F =
      __eo_list_setof Term.__eo_List_cons x := by
  cases F
  case Stuck =>
      exact False.elim (hF rfl)
  case Apply f a =>
      cases f
      case Apply Q' y =>
          have hSelf : Term.Apply (Term.Apply Q' y) a ≠ a := by
            intro hEq
            exact no_self_apply_apply Q' y a hEq.symm
          by_cases ha : a = Term.Stuck
          · subst a
            simpa [qterm, __get_unused_vars, __eo_l_1___get_unused_vars,
              __eo_and, __eo_eq, __eo_ite, native_ite, native_teq]
              using h
          · have hEqFalse :
                __eo_eq (Term.Apply (Term.Apply Q' y) a) a =
                  Term.Boolean false := by
              exact eoEq_false_of_ne_nonstuck hSelf
                (by intro hBad; cases hBad) ha
            have hQNe : Q ≠ Term.Stuck := by
              intro hQ
              subst Q
              simp [qterm, __get_unused_vars, __eo_and, __eo_eq, __eo_ite,
                native_ite, native_teq] at h
            have hQ'Ne : Q' ≠ Term.Stuck := by
              intro hQ'
              subst Q'
              cases Q <;> simp [qterm, __get_unused_vars,
                __eo_and, __eo_eq, __eo_ite, native_ite, native_teq]
                at hQNe h
            have hGuardFalse :
                __eo_and (__eo_eq Q Q')
                    (__eo_eq (Term.Apply (Term.Apply Q' y) a) a) =
                  Term.Boolean false := by
              rcases eo_eq_bool_of_ne_stuck hQNe hQ'Ne with ⟨b, hQQ⟩
              rw [hQQ, hEqFalse]
              cases b <;> simp [__eo_and, native_and]
            have hGet :
                __get_unused_vars
                    (qterm Q x (Term.Apply (Term.Apply Q' y) a))
                    (Term.Apply (Term.Apply Q' y) a) =
                  __eo_requires
                    (__eo_eq (Term.Apply (Term.Apply Q' y) a)
                      (Term.Apply (Term.Apply Q' y) a))
                    (Term.Boolean true)
                    (__eo_list_setof Term.__eo_List_cons x) := by
              simp [qterm, __get_unused_vars, __eo_l_1___get_unused_vars,
                hGuardFalse, __eo_ite, native_ite, native_teq]
            rw [hGet] at h ⊢
            simpa [__eo_eq, __eo_requires, native_ite, native_teq,
              native_not, SmtEval.native_not] using h
      all_goals
        simpa [qterm, __get_unused_vars, __eo_l_1___get_unused_vars,
          __eo_eq, __eo_requires, native_ite, native_teq, native_not,
          SmtEval.native_not] using h
  all_goals
      simpa [qterm, __get_unused_vars, __eo_l_1___get_unused_vars,
        __eo_eq, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] using h

private theorem get_unused_vars_fallback_shape_of_get_eq
    (Q x F G : Term)
    (hGet :
      __get_unused_vars (qterm Q x F) G =
        __eo_l_1___get_unused_vars (qterm Q x F) G)
    (h : __get_unused_vars (qterm Q x F) G ≠ Term.Stuck) :
    G = F ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x := by
  have hFallbackNe :
      __eo_l_1___get_unused_vars (qterm Q x F) G ≠ Term.Stuck := by
    simpa [hGet] using h
  have hFallback :=
    get_unused_vars_fallback_eq_of_not_stuck Q x F G hFallbackNe
  exact ⟨hFallback.1, by rw [hGet]; exact hFallback.2⟩

private theorem get_unused_vars_shape_of_not_stuck
    (Q x F G : Term)
    (h :
      __get_unused_vars (qterm Q x F) G ≠ Term.Stuck) :
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
  let set := __eo_list_setof Term.__eo_List_cons x
  cases G with
  | Apply lhs F₂ =>
      cases lhs with
      | Apply Q₂ y =>
          let guard := __eo_and (__eo_eq Q Q₂) (__eo_eq F F₂)
          let diff := __eo_list_diff Term.__eo_List_cons set y
          let branch :=
            __eo_requires
              (__eo_list_minclude Term.__eo_List_cons set y)
              (Term.Boolean true) diff
          let fallback :=
            __eo_l_1___get_unused_vars (qterm Q x F)
              (Term.Apply (Term.Apply Q₂ y) F₂)
          cases hGuard : guard with
          | Boolean b =>
              cases b
              · have hFallbackNe : fallback ≠ Term.Stuck := by
                  simpa [qterm, __get_unused_vars, guard, fallback, hGuard,
                    __eo_ite, native_ite, native_teq] using h
                have hFallback :=
                  get_unused_vars_fallback_eq_of_not_stuck Q x F
                    (Term.Apply (Term.Apply Q₂ y) F₂) hFallbackNe
                left
                constructor
                · exact hFallback.1
                · have hGet :
                      __get_unused_vars (qterm Q x F)
                          (Term.Apply (Term.Apply Q₂ y) F₂) =
                        fallback := by
                    simp [qterm, __get_unused_vars, guard, fallback, hGuard,
                      __eo_ite, native_ite, native_teq]
                  rw [hGet]
                  exact hFallback.2
              · have hAnd :
                    __eo_and (__eo_eq Q Q₂) (__eo_eq F F₂) =
                      Term.Boolean true := by
                  simpa [guard] using hGuard
                rcases eo_and_eq_true_cases hAnd with ⟨hQEq, hFEq⟩
                have hQ₂ : Q₂ = Q :=
                  RuleProofs.eq_of_eo_eq_true Q Q₂ hQEq
                have hF₂ : F₂ = F :=
                  RuleProofs.eq_of_eo_eq_true F F₂ hFEq
                subst Q₂
                subst F₂
                have hReqNe :
                    __eo_requires
                        (__eo_list_minclude Term.__eo_List_cons set y)
                        (Term.Boolean true) diff ≠ Term.Stuck := by
                  simpa [qterm, __get_unused_vars, set, guard, diff, branch,
                    fallback, hGuard, __eo_ite, native_ite, native_teq] using h
                have hIncl :
                    __eo_list_minclude Term.__eo_List_cons set y =
                      Term.Boolean true :=
                  eq_of_requires_ne_stuck hReqNe
                right
                refine ⟨y, rfl, hIncl, ?_⟩
                simpa [qterm, __get_unused_vars, set, guard, diff, branch,
                  fallback, hGuard, hIncl, __eo_requires, __eo_ite,
                  native_ite, native_teq, native_not, SmtEval.native_not]
          | _ =>
              have hStuck :
                  __get_unused_vars (qterm Q x F)
                      (Term.Apply (Term.Apply Q₂ y) F₂) =
                    Term.Stuck := by
                simp [qterm, __get_unused_vars, guard, hGuard, __eo_ite,
                  native_ite, native_teq]
              exact False.elim (h hStuck)
      | _ =>
          left
          apply get_unused_vars_fallback_shape_of_get_eq Q x F
          · simp [qterm, __get_unused_vars]
          · exact h
  | Stuck =>
      exact False.elim (h (by simp [qterm, __get_unused_vars]))
  | _ =>
      left
      apply get_unused_vars_fallback_shape_of_get_eq Q x F
      · simp [qterm, __get_unused_vars]
      · exact h

private theorem smtx_typeof_qexists_body_bool_of_top_bool
    (x F : Term)
    (hTy : __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
  have hNN :
      __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None := by
    rw [hTy]
    simp
  have hx : x ≠ Term.__eo_List_nil :=
    qexists_non_nil_of_non_none x F hNN
  rw [eo_to_smt_exists_eq x F hx] at hTy
  exact TranslationProofs.eo_to_smt_exists_body_bool_of_bool
    x (__eo_to_smt F) hTy

private theorem smtx_typeof_qforall_body_bool_of_top_bool
    (x F : Term)
    (hTy : __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
  have hNN :
      __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None := by
    rw [hTy]
    simp
  have hExistsTy :
      __smtx_typeof (__eo_to_smt_exists x
          (SmtTerm.not (__eo_to_smt F))) = SmtType.Bool :=
    qforall_inner_exists_bool_of_non_none x F hNN
  have hNotTy :
      __smtx_typeof (SmtTerm.not (__eo_to_smt F)) = SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool
      x (SmtTerm.not (__eo_to_smt F)) hExistsTy
  exact smtx_typeof_not_arg_of_non_none (__eo_to_smt F) (by
    rw [hNotTy]
    simp)

private theorem smtx_typeof_qterm_body_bool_of_top_bool
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
  rcases hQ with hQ | hQ
  · subst Q
    exact smtx_typeof_qforall_body_bool_of_top_bool x F hTy
  · subst Q
    exact smtx_typeof_qexists_body_bool_of_top_bool x F hTy

private theorem quantUnusedFormula_lhs_rhs_same_type
    (Q x F G : Term)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    __smtx_typeof (__eo_to_smt (qterm Q x F)) =
        __smtx_typeof (__eo_to_smt G) ∧
      __smtx_typeof (__eo_to_smt (qterm Q x F)) ≠ SmtType.None := by
  simpa [quantUnusedFormula, qeq] using
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (qterm Q x F) G hBool

private theorem quantUnusedFormula_lhs_bool_of_quant
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool := by
  exact qterm_top_bool_of_non_none Q x F hQ
    (quantUnusedFormula_lhs_rhs_same_type Q x F G hBool).2

private theorem quantUnusedFormula_rhs_bool_of_quant
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    __smtx_typeof (__eo_to_smt G) = SmtType.Bool := by
  have hTypes := quantUnusedFormula_lhs_rhs_same_type Q x F G hBool
  rw [← hTypes.1]
  exact quantUnusedFormula_lhs_bool_of_quant Q x F G hQ hBool

private theorem quantUnusedFormula_body_bool_of_quant
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
  smtx_typeof_qterm_body_bool_of_top_bool Q x F hQ
    (quantUnusedFormula_lhs_bool_of_quant Q x F G hQ hBool)

private theorem quantUnusedFormula_lhs_binder_env_of_quant
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    ∃ vars, EoSmtVarEnv x vars :=
  qterm_binder_env_of_bool Q x F hQ
    (quantUnusedFormula_lhs_bool_of_quant Q x F G hQ hBool)

private theorem quantUnusedFormula_rhs_binder_env_of_quant_shape
    (Q x y F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hBool :
      RuleProofs.eo_has_bool_type
        (quantUnusedFormula Q x F (qterm Q y F))) :
    ∃ vars, EoSmtVarEnv y vars :=
  qterm_binder_env_of_bool Q y F hQ
    (quantUnusedFormula_rhs_bool_of_quant Q x F (qterm Q y F) hQ hBool)

private theorem contains_atomic_qterm_cons_body_false
    (Q head ys F xs bvs : Term)
    (h :
      __contains_atomic_term_list_free_rec
          (qterm Q
            (Term.Apply (Term.Apply Term.__eo_List_cons head) ys) F)
          xs bvs =
        Term.Boolean false) :
    __contains_atomic_term_list_free_rec F xs
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons head) ys) bvs) =
      Term.Boolean false := by
  simpa [qterm] using
    contains_atomic_binder_body_false Q head ys F xs bvs h

private theorem contains_atomic_qterm_body_false_of_binder_env_nil
    (Q y F xs : Term) {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv y vars)
    (h :
      __contains_atomic_term_list_free_rec (qterm Q y F) xs
          Term.__eo_List_nil =
        Term.Boolean false) :
    __contains_atomic_term_list_free_rec F xs
        (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil) =
      Term.Boolean false := by
  cases hEnv with
  | nil =>
      have hBody :
          __contains_atomic_term_list_free_rec F xs Term.__eo_List_nil =
            Term.Boolean false := by
        cases xs <;>
          simp [qterm, __contains_atomic_term_list_free_rec] at h ⊢
        all_goals exact (eo_ite_true_eq_false _ _ h).2
      simpa [__eo_list_concat, __eo_is_list, __eo_get_nil_rec,
        __eo_requires, __eo_is_list_nil, __eo_list_concat_rec, native_ite,
        native_teq, native_not, SmtEval.native_not] using hBody
  | cons hTail =>
      rename_i s T tail varsTail
      simpa using
        contains_atomic_qterm_cons_body_false Q
          (Term.Var (Term.String s) T) tail F xs Term.__eo_List_nil h

private theorem quant_unused_free_shape_of_no_free
    (Q x F G : Term)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false) :
    (G = F ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x ∧
      __contains_atomic_term_list_free_rec F
          (__eo_list_setof Term.__eo_List_cons x) Term.__eo_List_nil =
        Term.Boolean false) ∨
    ∃ y,
      G = qterm Q y F ∧
      __eo_list_minclude Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y =
        Term.Boolean true ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_diff Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y ∧
      __contains_atomic_term_list_free_rec (qterm Q y F)
          (__eo_list_diff Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y)
          Term.__eo_List_nil =
        Term.Boolean false := by
  have hGetNe :
      __get_unused_vars (qterm Q x F) G ≠ Term.Stuck :=
    get_unused_vars_not_stuck_of_no_free Q x F G hNoFree
  rcases get_unused_vars_shape_of_not_stuck Q x F G hGetNe with
    hFallback | hQuant
  · rcases hFallback with ⟨hG, hGet⟩
    subst G
    left
    refine ⟨rfl, hGet, ?_⟩
    simpa [hGet] using hNoFree
  · rcases hQuant with ⟨y, hG, hIncl, hGet⟩
    subst G
    right
    refine ⟨y, rfl, hIncl, hGet, ?_⟩
    simpa [hGet] using hNoFree

private theorem quant_unused_free_body_shape_of_no_free
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    (G = F ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x ∧
      __contains_atomic_term_list_free_rec F
          (__eo_list_setof Term.__eo_List_cons x) Term.__eo_List_nil =
        Term.Boolean false) ∨
    ∃ y vars,
      G = qterm Q y F ∧
      EoSmtVarEnv y vars ∧
      __eo_list_minclude Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y =
        Term.Boolean true ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_diff Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y ∧
      __contains_atomic_term_list_free_rec F
          (__eo_list_diff Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y)
          (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil) =
        Term.Boolean false := by
  rcases quant_unused_free_shape_of_no_free Q x F G hNoFree with
    hFallback | hQuant
  · exact Or.inl hFallback
  · rcases hQuant with ⟨y, hG, hIncl, hGet, hNoFreeQ⟩
    subst G
    rcases quantUnusedFormula_rhs_binder_env_of_quant_shape
        Q x y F hQ hBool with ⟨vars, hEnv⟩
    have hBody :
        __contains_atomic_term_list_free_rec F
            (__eo_list_diff Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y)
            (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil) =
          Term.Boolean false :=
      contains_atomic_qterm_body_false_of_binder_env_nil Q y F
        (__eo_list_diff Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y)
        hEnv hNoFreeQ
    exact Or.inr ⟨y, vars, rfl, hEnv, hIncl, hGet, hBody⟩

private axiom smtx_model_eval_quant_unused_formula
    (M : SmtModel) (hM : model_total_typed M)
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M (__eo_to_smt G)

private theorem quant_unused_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = quantUnusedFormula Q x F G ∧
      (Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists) ∧
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false ∧
      __eo_prog_quant_unused_vars x1 = quantUnusedFormula Q x F G := by
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
                          let unused := __get_unused_vars v0 G
                          let inner :=
                            __eo_requires
                              (__contains_atomic_term_list_free_rec G unused
                                Term.__eo_List_nil)
                              (Term.Boolean false) (qeq v0 G)
                          have hReq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner ≠ Term.Stuck := by
                            simpa [quantUnusedFormula, qeq, qterm, v0, unused,
                              inner, __eo_prog_quant_unused_vars] using hProg
                          have hGuard :
                              __eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                  (__eo_eq Q (Term.UOp UserOp.exists)) =
                                Term.Boolean true :=
                            eq_of_requires_ne_stuck hReq
                          have hInnerNe : inner ≠ Term.Stuck :=
                            body_ne_stuck_of_requires_ne_stuck hReq
                          have hNoFree :
                              __contains_atomic_term_list_free_rec G unused
                                  Term.__eo_List_nil =
                                Term.Boolean false :=
                            eq_of_requires_ne_stuck hInnerNe
                          rcases eo_or_eq_true_cases_local
                              (__eo_eq Q (Term.UOp UserOp.forall))
                              (__eo_eq Q (Term.UOp UserOp.exists)) hGuard with
                            hForall | hExists
                          · have hQ : Q = Term.UOp UserOp.forall :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.forall) hForall).symm
                            subst Q
                            have hNoFree' :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (qterm (Term.UOp UserOp.forall) x F) G)
                                    Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [v0, unused, qterm] using hNoFree
                            have hNoFreeRaw :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (((Term.UOp UserOp.forall).Apply x).Apply F)
                                      G) Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [qterm] using hNoFree'
                            refine ⟨Term.UOp UserOp.forall, x, F, G, rfl,
                              Or.inl rfl, ?_, ?_⟩
                            · exact hNoFree'
                            · change __eo_prog_quant_unused_vars
                                (quantUnusedFormula (Term.UOp UserOp.forall)
                                  x F G) =
                                quantUnusedFormula (Term.UOp UserOp.forall)
                                  x F G
                              simp [quantUnusedFormula, qeq, qterm,
                                __eo_prog_quant_unused_vars, hGuard,
                                hNoFreeRaw,
                                __eo_requires, native_ite, native_teq,
                                native_not, SmtEval.native_not]
                          · have hQ : Q = Term.UOp UserOp.exists :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.exists) hExists).symm
                            subst Q
                            have hNoFree' :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (qterm (Term.UOp UserOp.exists) x F) G)
                                    Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [v0, unused, qterm] using hNoFree
                            have hNoFreeRaw :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (((Term.UOp UserOp.exists).Apply x).Apply F)
                                      G) Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [qterm] using hNoFree'
                            refine ⟨Term.UOp UserOp.exists, x, F, G, rfl,
                              Or.inr rfl, ?_, ?_⟩
                            · exact hNoFree'
                            · change __eo_prog_quant_unused_vars
                                (quantUnusedFormula (Term.UOp UserOp.exists)
                                  x F G) =
                                quantUnusedFormula (Term.UOp UserOp.exists)
                                  x F G
                              simp [quantUnusedFormula, qeq, qterm,
                                __eo_prog_quant_unused_vars, hGuard,
                                hNoFreeRaw,
                                __eo_requires, native_ite, native_teq,
                                native_not, SmtEval.native_not]
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
  have hProg : __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_unused_vars a1 ≠ Term.Stuck := by
                change __eo_prog_quant_unused_vars a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_unused_shape_of_not_stuck a1 hProgQuant with
                ⟨Q, x, F, G, ha1, hQ, hNoFree, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (quantUnusedFormula Q x F G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (quantUnusedFormula Q x F G) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (quantUnusedFormula Q x F G) hTransFormula hFormulaType
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_quant_unused_vars a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M (qterm Q x F) G
                · exact hFormulaBool
                · have hEvalEq :=
                    smtx_model_eval_quant_unused_formula M hM Q x F G hQ
                      hNoFree hFormulaBool
                  rw [hEvalEq]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M (__eo_to_smt G))
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_unused_vars a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
