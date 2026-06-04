import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- The zeroth choice term selects a satisfying witness for a true existential. -/
private theorem choice_zero_witness_of_exists_true
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (hExists :
      __smtx_model_eval M (SmtTerm.exists s T body) =
        SmtValue.Boolean true) :
    __smtx_model_eval
        (native_model_push M s T
          (__smtx_model_eval M (SmtTerm.choice_nth s T body 0))) body =
      SmtValue.Boolean true := by
  classical
  rw [__smtx_model_eval.eq_135] at hExists
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical_bool v = true ∧
          __smtx_model_eval (native_model_push M s T v) body =
            SmtValue.Boolean true
  · have hChoiceEval :
        __smtx_model_eval M (SmtTerm.choice_nth s T body 0) =
          Classical.choose hSat := by
      rw [smtx_model_eval_choice_nth_eq_aux]
      simp [nativeEvalTChoiceNthAux, hSat]
    rw [hChoiceEval]
    exact (Classical.choose_spec hSat).2.2
  · simp [hSat] at hExists

private def eoListOfTerms : List Term -> Term
  | [] => Term.__eo_List_nil
  | x :: xs => Term.Apply (Term.Apply Term.__eo_List_cons x) (eoListOfTerms xs)

private def IsQuantVarTerm : Term -> Prop
  | Term.Var (Term.String _) _ => True
  | _ => False

/-- Pushes the canonical zero-index choice witness for each EO binder. -/
private noncomputable def pushChoiceWitnesses : SmtModel -> Term -> SmtTerm -> SmtModel
  | M, Term.__eo_List_nil, _ => M
  | M, Term.Apply (Term.Apply Term.__eo_List_cons
      (Term.Var (Term.String s) T)) xs, body =>
      pushChoiceWitnesses
        (native_model_push M s (__eo_to_smt_type T)
          (__smtx_model_eval M
            (SmtTerm.choice_nth s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs body) 0)))
        xs body
  | M, _, _ => M

/--
If an EO binder-list existential is true, recursively pushing the generated
choice witnesses makes the innermost body true.
-/
private theorem pushChoiceWitnesses_eval_true
    (M : SmtModel) (xs : List Term) (body : SmtTerm)
    (hxs : ∀ t ∈ xs, IsQuantVarTerm t)
    (hExists :
      __smtx_model_eval M (__eo_to_smt_exists (eoListOfTerms xs) body) =
        SmtValue.Boolean true) :
    __smtx_model_eval
        (pushChoiceWitnesses M (eoListOfTerms xs) body) body =
      SmtValue.Boolean true := by
  induction xs generalizing M body with
  | nil =>
      simpa [eoListOfTerms, pushChoiceWitnesses] using hExists
  | cons x xs ih =>
      have hx : IsQuantVarTerm x := hxs x (by simp)
      have htail : ∀ t ∈ xs, IsQuantVarTerm t := by
        intro t ht
        exact hxs t (by simp [ht])
      cases x <;> simp [IsQuantVarTerm] at hx
      case Var name T =>
        cases name <;> simp at hx
        case String s =>
          let tailBody := __eo_to_smt_exists (eoListOfTerms xs) body
          let v :=
            __smtx_model_eval M
              (SmtTerm.choice_nth s (__eo_to_smt_type T) tailBody 0)
          have hTailExists :
              __smtx_model_eval
                  (native_model_push M s (__eo_to_smt_type T) v)
                  tailBody =
                SmtValue.Boolean true := by
            exact choice_zero_witness_of_exists_true
              M s (__eo_to_smt_type T) tailBody (by
                simpa [eoListOfTerms, tailBody] using hExists)
          simpa [eoListOfTerms, pushChoiceWitnesses, tailBody, v] using
            ih (M := native_model_push M s (__eo_to_smt_type T) v)
              (body := body) htail hTailExists

private theorem smtx_typeof_none_ne_bool :
    __smtx_typeof SmtTerm.None ≠ SmtType.Bool := by
  simp [TranslationProofs.smtx_typeof_none]

/-- Boolean typing of an EO existential chain recovers a real variable list. -/
private theorem eo_to_smt_exists_bool_as_eoList
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    ∃ ts, xs = eoListOfTerms ts ∧ ∀ t ∈ ts, IsQuantVarTerm t := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    exact ⟨[], rfl, by simp⟩
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
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub :
                __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            rcases eo_to_smt_exists_bool_as_eoList a body hSub with
              ⟨ts, hTail, hAllTail⟩
            refine ⟨Term.Var (Term.String s) T :: ts, ?_, ?_⟩
            · simp [eoListOfTerms, hTail]
            · intro t ht
              simp at ht
              rcases ht with ht | ht
              · subst t
                simp [IsQuantVarTerm]
              · exact hAllTail t ht
          all_goals
            subst hname
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              change __smtx_typeof SmtTerm.None = SmtType.Bool at hTy
              exact hTy
            exact False.elim (smtx_typeof_none_ne_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            change __smtx_typeof SmtTerm.None = SmtType.Bool at hTy
            exact hTy
          exact False.elim (smtx_typeof_none_ne_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          change __smtx_typeof SmtTerm.None = SmtType.Bool at hTy
          exact hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        change __smtx_typeof SmtTerm.None = SmtType.Bool at hTy
        exact hTy
      exact False.elim (smtx_typeof_none_ne_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      change __smtx_typeof SmtTerm.None = SmtType.Bool at hTy
      exact hTy
    exact False.elim (smtx_typeof_none_ne_bool hNone)

/--
Typed, true EO existential chains provide a concrete witness-pushed model in
which the body is true.
-/
private theorem pushChoiceWitnesses_eval_true_of_bool_exists
    (M : SmtModel) (xs : Term) (body : SmtTerm)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool)
    (hExists :
      __smtx_model_eval M (__eo_to_smt_exists xs body) =
        SmtValue.Boolean true) :
    ∃ ts,
      xs = eoListOfTerms ts ∧
        (∀ t ∈ ts, IsQuantVarTerm t) ∧
        __smtx_model_eval
            (pushChoiceWitnesses M xs body) body =
          SmtValue.Boolean true := by
  rcases eo_to_smt_exists_bool_as_eoList xs body hTy with
    ⟨ts, hxs, hAll⟩
  subst xs
  refine ⟨ts, rfl, hAll, ?_⟩
  exact pushChoiceWitnesses_eval_true M ts body hAll hExists

/-- A non-stuck skolemize step can only come from `not (forall xs G)`. -/
private theorem skolemize_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_skolemize (Proof.pf x1) ≠ Term.Stuck ->
    ∃ xs G,
      x1 =
        Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) G) ∧
      __eo_prog_skolemize (Proof.pf x1) =
        __substitute_simul (Term.Apply (Term.UOp UserOp.not) G) xs
          (__mk_skolems xs
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) G)
            (Term.Numeral 0)) := by
  intro hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases a with
              | Apply q G =>
                  cases q with
                  | Apply qHead xs =>
                      cases qHead with
                      | UOp qop =>
                          cases qop with
                          | «forall» =>
                              exact ⟨xs, G, rfl, rfl⟩
                          | _ =>
                              simp [__eo_prog_skolemize] at hProg
                      | _ =>
                          simp [__eo_prog_skolemize] at hProg
                  | _ =>
                      simp [__eo_prog_skolemize] at hProg
              | _ =>
                  simp [__eo_prog_skolemize] at hProg
          | _ =>
              simp [__eo_prog_skolemize] at hProg
      | _ =>
          simp [__eo_prog_skolemize] at hProg
  | _ =>
      simp [__eo_prog_skolemize] at hProg

/-- Simplifies the translation of `not (forall xs G)` when `xs` is nonempty. -/
private theorem eo_to_smt_not_forall_eq
    (xs G : Term) (hxs : xs ≠ Term.__eo_List_nil) :
    __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) G)) =
      SmtTerm.not
        (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt G)))) := by
  cases xs <;> first | rfl | exact False.elim (hxs rfl)

/-- Double negation can evaluate to true only when the inner value is true. -/
private theorem smtx_model_eval_not_not_true
    (v : SmtValue) :
    __smtx_model_eval_not (__smtx_model_eval_not v) =
        SmtValue.Boolean true ->
      v = SmtValue.Boolean true := by
  cases v <;> simp [__smtx_model_eval_not, SmtEval.native_not]

/-- Truth of `not (forall xs G)` is truth of the SMT existential chain for `not G`. -/
private theorem not_forall_true_implies_exists_not_true
    (M : SmtModel) (xs G : Term)
    (hxs : xs ≠ Term.__eo_List_nil) :
    eo_interprets M
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) G)) true ->
      __smtx_model_eval M
          (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt G))) =
        SmtValue.Boolean true := by
  intro hTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    eo_to_smt_not_forall_eq xs G hxs] at hTrue
  cases hTrue with
  | intro_true _hTy hEval =>
      rw [__smtx_model_eval.eq_6, __smtx_model_eval.eq_6] at hEval
      exact smtx_model_eval_not_not_true
        (__smtx_model_eval M
          (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt G)))) hEval

/-- A translated Boolean `not (forall xs G)` cannot use the nil binder-list case. -/
private theorem not_forall_vars_non_nil_of_has_bool_type
    (xs G : Term) :
    RuleProofs.eo_has_bool_type
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) G)) ->
      xs ≠ Term.__eo_List_nil := by
  intro hBool hNil
  subst xs
  unfold RuleProofs.eo_has_bool_type at hBool
  change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.Bool at hBool
  rw [typeof_not_eq, TranslationProofs.smtx_typeof_none] at hBool
  simp [native_ite, native_Teq] at hBool

/-- Translating a generated skolem atom peels to SMT `quantifiers_skolemize`. -/
private theorem eo_to_smt_skolem_term_eq
    (xs G i : Term)
    (hValid : __eo_to_smt_nat_is_valid i = true) :
    __eo_to_smt
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) G) i) =
      __eo_to_smt_quantifiers_skolemize
        (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt G)))
        (__eo_to_smt_nat i) := by
  change
    native_ite (__eo_to_smt_nat_is_valid i)
      (__eo_to_smt_quantifiers_skolemize
        (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt G)))
        (__eo_to_smt_nat i))
      SmtTerm.None =
    __eo_to_smt_quantifiers_skolemize
      (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt G)))
      (__eo_to_smt_nat i)
  rw [hValid]
  rfl

/-- A generated skolem for a variable-list cons translates to indexed `choice_nth`. -/
private theorem eo_to_smt_skolem_term_nat_cons
    (s : native_String) (T tail G : Term) (n : native_Nat) :
    __eo_to_smt
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall)
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) tail)) G)
          (Term.Numeral (native_nat_to_int n))) =
      SmtTerm.choice_nth s (__eo_to_smt_type T)
        (__eo_to_smt_exists tail (SmtTerm.not (__eo_to_smt G))) n := by
  have hValid :
      __eo_to_smt_nat_is_valid (Term.Numeral (native_nat_to_int n)) = true := by
    simp [__eo_to_smt_nat_is_valid, native_zleq, SmtEval.native_zleq,
      native_nat_to_int, SmtEval.native_nat_to_int]
  rw [eo_to_smt_skolem_term_eq _ _ _ hValid]
  change
    __eo_to_smt_quantifiers_skolemize
      (SmtTerm.exists s (__eo_to_smt_type T)
        (__eo_to_smt_exists tail (SmtTerm.not (__eo_to_smt G))))
      (__eo_to_smt_nat (Term.Numeral (native_nat_to_int n))) =
      SmtTerm.choice_nth s (__eo_to_smt_type T)
        (__eo_to_smt_exists tail (SmtTerm.not (__eo_to_smt G))) n
  simp [__eo_to_smt_nat, __eo_to_smt_quantifiers_skolemize,
    native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
    SmtEval.native_int_to_nat]

/-- The first generated skolem for a variable-list cons translates to `choice_nth ... 0`. -/
private theorem eo_to_smt_skolem_term_zero_cons
    (s : native_String) (T tail G : Term) :
    __eo_to_smt
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall)
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) tail)) G)
          (Term.Numeral 0)) =
      SmtTerm.choice_nth s (__eo_to_smt_type T)
        (__eo_to_smt_exists tail (SmtTerm.not (__eo_to_smt G))) 0 := by
  have hValid :
      __eo_to_smt_nat_is_valid (Term.Numeral 0) = true := by
    rfl
  rw [eo_to_smt_skolem_term_eq _ _ _ hValid]
  change
    __eo_to_smt_quantifiers_skolemize
      (SmtTerm.exists s (__eo_to_smt_type T)
        (__eo_to_smt_exists tail (SmtTerm.not (__eo_to_smt G)))) 0 =
      SmtTerm.choice_nth s (__eo_to_smt_type T)
        (__eo_to_smt_exists tail (SmtTerm.not (__eo_to_smt G))) 0
  rfl

theorem cmd_step_skolemize_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.skolemize args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.skolemize args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.skolemize args premises) :=
by
  sorry
