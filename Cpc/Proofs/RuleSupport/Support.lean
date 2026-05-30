import Cpc.Proofs.Common
import Cpc.Proofs.Assumptions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Builds the right-associated conjunction of a list of premise terms, using `true` as the empty case. -/
def premiseAndFormulaList : List Term -> Term
  | [] => Term.Boolean true
  | p :: ps => Term.Apply (Term.Apply (Term.UOp UserOp.and) p) (premiseAndFormulaList ps)

/-- Collects the proven terms referenced by a premise index list in a checker state. -/
def premiseTermList (s : CState) : CIndexList -> List Term
  | CIndexList.nil => []
  | CIndexList.cons n premises =>
      __eo_state_proven_nth s n :: premiseTermList s premises

/-- Predicate asserting that every term in a list is interpreted as `true` by a model. -/
def AllInterpretedTrue (M : SmtModel) (ts : List Term) : Prop :=
  ∀ t ∈ ts, eo_interprets M t true

/--
Two models agree on the global part of the interpretation.

Variables may vary, but user constants and native function interpretations are
kept fixed. This is the model relation used when a binder pushes fresh variable
assignments.
-/
def model_agrees_on_globals (M N : SmtModel) : Prop :=
  (∀ s T, native_model_lookup M s T = native_model_lookup N s T) ∧
  (∀ fid T U, native_model_fun_lookup M fid T U =
    native_model_fun_lookup N fid T U)

theorem model_agrees_on_globals_refl (M : SmtModel) :
  model_agrees_on_globals M M :=
by
  exact ⟨by intro s T; rfl, by intro fid T U; rfl⟩

theorem model_agrees_on_globals_trans {M N K : SmtModel} :
  model_agrees_on_globals M N ->
  model_agrees_on_globals N K ->
  model_agrees_on_globals M K :=
by
  intro hMN hNK
  exact
    ⟨by
      intro s T
      exact (hMN.1 s T).trans (hNK.1 s T),
    by
      intro fid T U
      exact (hMN.2 fid T U).trans (hNK.2 fid T U)⟩

theorem model_agrees_on_globals_push
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) :
  model_agrees_on_globals M (native_model_push M s T v) :=
by
  exact
    ⟨by
      intro s' T'
      simp [native_model_lookup, native_model_key, native_model_push],
    by
      intro fid A B
      simp [native_model_fun_lookup, native_model_key, native_model_push]⟩

/--
Contextual truth for a derived formula.

The first field is the ordinary checker fact in the current model. The second
field is the freshness/parametricity fact needed by binder-sensitive rules:
the derived formula remains true in any model that only changes variables,
provided the same assumptions and local pushes hold there.
-/
structure ContextualTruth
    (M : SmtModel) (assumes pushes P : Term) : Prop where
  true_here :
    eo_interprets M assumes true ->
    eo_interprets M pushes true ->
    eo_interprets M P true
  true_in_var_model :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      eo_interprets N assumes true ->
      eo_interprets N pushes true ->
      eo_interprets N P true

/--
The premise evidence supplied to a rule.

Most rules only use `true_here`. Binder-sensitive congruence needs the
unconditional `true_in_any_var_model` field: once a premise is available, it
must remain true in any model that only changes variable assignments.
-/
structure RulePremiseEvidence
    (M : SmtModel) (assumes pushes : Term) (premises : List Term) : Prop where
  true_here :
    AllInterpretedTrue M premises
  true_in_var_model :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      eo_interprets N assumes true ->
      eo_interprets N pushes true ->
      AllInterpretedTrue N premises
  true_in_any_var_model :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      AllInterpretedTrue N premises

/-- Predicate asserting that every term in a list has an SMT translation. -/
def AllHaveSmtTranslation (ts : List Term) : Prop :=
  ∀ t ∈ ts, RuleProofs.eo_has_smt_translation t

/-- Predicate asserting that every term in a list has translated SMT Boolean type. -/
def AllHaveBoolType (ts : List Term) : Prop :=
  ∀ t ∈ ts, RuleProofs.eo_has_bool_type t

/-- Predicate asserting that every term in a list has EO type `Bool`. -/
def AllTypeofBool (ts : List Term) : Prop :=
  ∀ t ∈ ts, __eo_typeof t = Term.Bool

/-- A term with EO type `Bool` cannot be `Stuck`. -/
theorem term_ne_stuck_of_typeof_bool
    {t : Term}
    (hTy : __eo_typeof t = Term.Bool) :
    t ≠ Term.Stuck := by
  intro hStuck
  rw [hStuck] at hTy
  have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
    native_decide
  exact hStuckTy hTy

/-- Derives `premiseAndFormulaList_true` from `all_true`. -/
theorem premiseAndFormulaList_true_of_all_true
    (M : SmtModel) :
  ∀ premises : List Term,
    AllInterpretedTrue M premises ->
    eo_interprets M (premiseAndFormulaList premises) true :=
by
  intro premises hPremises
  induction premises with
  | nil =>
      simpa [premiseAndFormulaList] using RuleProofs.eo_interprets_true M
  | cons p premises ih =>
      apply RuleProofs.eo_interprets_and_intro
      · exact hPremises p (by simp)
      · apply ih
        intro t ht
        exact hPremises t (by simp [ht])

/-- Shows that a conjunction built from Boolean premises still has Boolean type. -/
theorem premiseAndFormulaList_has_bool_type :
  ∀ premises : List Term,
    AllHaveBoolType premises ->
    RuleProofs.eo_has_bool_type (premiseAndFormulaList premises) :=
by
  intro premises hPremises
  induction premises with
  | nil =>
      simpa [premiseAndFormulaList] using RuleProofs.eo_has_bool_type_true
  | cons p premises ih =>
      apply RuleProofs.eo_has_bool_type_and_of_bool_args
      · exact hPremises p (by simp)
      · apply ih
        intro t ht
        exact hPremises t (by simp [ht])

/-- Shows that `premiseAndFormulaList` is recognized as an `and`-list by `__eo_is_list`. -/
theorem premiseAndFormulaList_is_and_list :
  ∀ premises : List Term,
    __eo_is_list (Term.UOp UserOp.and) (premiseAndFormulaList premises) = Term.Boolean true
:=
by
  have hGetNil :
      ∀ premises : List Term,
        __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList premises) ≠ Term.Stuck
  :=
  by
    intro premises
    induction premises with
    | nil =>
        unfold premiseAndFormulaList
        unfold __eo_get_nil_rec
        unfold __eo_requires
        unfold __eo_is_list_nil
        simp [native_ite, native_teq, native_not, SmtEval.native_not]
    | cons p premises ih =>
        unfold premiseAndFormulaList
        unfold __eo_get_nil_rec
        unfold __eo_requires
        simpa [native_ite, native_teq, native_not, SmtEval.native_not] using ih
  intro premises
  have hNotStuck :
      __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList premises) ≠ Term.Stuck :=
    hGetNil premises
  have hPremNotStuck : premiseAndFormulaList premises ≠ Term.Stuck :=
    by
      induction premises with
      | nil =>
          simp [premiseAndFormulaList]
      | cons p premises ih =>
          simp [premiseAndFormulaList]
  unfold __eo_is_list
  unfold __eo_is_ok
  simpa [native_teq, native_not, SmtEval.native_not] using hNotStuck

/-- Establishes an equality relating `mk_premise_list_and` and `premiseAndFormulaList`. -/
theorem mk_premise_list_and_eq_premiseAndFormulaList :
  ∀ (s : CState) (premises : CIndexList),
    __eo_mk_premise_list (Term.UOp UserOp.and) premises s =
      premiseAndFormulaList (premiseTermList s premises)
:=
by
  intro s premises
  induction premises with
  | nil =>
      simp [__eo_mk_premise_list, premiseAndFormulaList, premiseTermList, __eo_nil]
  | cons n premises ih =>
      simp [__eo_mk_premise_list, premiseAndFormulaList, premiseTermList, __eo_cons,
        __eo_requires, native_ite, native_teq, native_not, ih,
        premiseAndFormulaList_is_and_list, SmtEval.native_not]

/-- Structure bundling the correctness and translation obligations for rules that only add a proven fact. -/
structure StepRuleProperties
    (M : SmtModel) (premises : List Term) (P : Term) : Prop where
  facts_of_true :
    AllInterpretedTrue M premises ->
    eo_interprets M P true
  has_smt_translation :
    RuleProofs.eo_has_smt_translation P

/--
Richer rule-correctness template for rules whose soundness depends on more
than premise truth in the current model.

The old `StepRuleProperties` remains as a compatibility template for ordinary
rules. The checker bridge can lift ordinary rules into this shape by
re-instantiating their old proof at each variable-variant model.
-/
structure EvidenceStepRuleProperties
    (M : SmtModel) (assumes pushes : Term) (premises : List Term)
    (P : Term) : Prop where
  facts_of_evidence :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      RulePremiseEvidence N assumes pushes premises ->
      eo_interprets N P true
  has_smt_translation :
    RuleProofs.eo_has_smt_translation P

/-- Predicate packaging the correctness and translation obligations for rules that also pop assumptions. -/
def StepPopRuleProperties
    (x1 : Term) (premises : List Term) (P : Term) : Prop :=
  ∃ x2,
    x2 ∈ premises ∧
    (forall (M : SmtModel), model_total_typed M ->
      ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
      eo_interprets M P true) ∧
    RuleProofs.eo_has_smt_translation P
