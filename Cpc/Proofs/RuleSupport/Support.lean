import Cpc.Proofs.Common
import Cpc.Proofs.Assumptions
import Cpc.Proofs.Closed.Support

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

Most rules only use `true_here`. Binder-sensitive congruence uses
`true_in_var_model`: the checker constructs that field only when the ambient
assumptions and pushes are known to remain true across variable-model changes.
-/
structure RulePremiseEvidence
    (M : SmtModel) (premises : List Term) : Prop where
  true_here :
    AllInterpretedTrue M premises
  true_in_var_model :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      AllInterpretedTrue N premises

instance RulePremiseEvidence.instCoeFun
    {M : SmtModel} {premises : List Term} :
    CoeFun (RulePremiseEvidence M premises)
      (fun _ => ∀ t, t ∈ premises -> eo_interprets M t true) where
  coe h := h.true_here

/-- Predicate asserting that every term in a list has an SMT translation. -/
def AllHaveSmtTranslation (ts : List Term) : Prop :=
  ∀ t ∈ ts, eoHasSmtTranslation t

/-- Projects the strengthened SMT-translation predicate to the legacy one-factor predicate. -/
theorem eoHasSmtTranslation.to_ruleProofs {t : Term}
    (h : eoHasSmtTranslation t) :
    RuleProofs.eo_has_smt_translation t := by
  simpa [RuleProofs.eo_has_smt_translation] using h.typeof_ne_none

/-- Builds the strengthened SMT-translation predicate from the legacy translation fact. -/
theorem eoHasSmtTranslation.of_ruleProofs {t : Term}
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hIndicesClosed : eoUOpIndicesClosed t) :
    eoHasSmtTranslation t := by
  exact ⟨by simpa [RuleProofs.eo_has_smt_translation] using hTrans, hIndicesClosed⟩

/-- Builds the strengthened SMT-translation predicate from Boolean SMT type. -/
theorem eoHasSmtTranslation.of_has_bool_type {t : Term}
    (hBool : RuleProofs.eo_has_bool_type t)
    (hIndicesClosed : eoUOpIndicesClosed t) :
    eoHasSmtTranslation t := by
  exact eoHasSmtTranslation.of_ruleProofs
    (RuleProofs.eo_has_smt_translation_of_has_bool_type t hBool)
    hIndicesClosed

/-- Closure of indexed-operator payloads is preserved by application. -/
theorem eoUOpIndicesClosed.apply {f x : Term}
    (hf : eoUOpIndicesClosed f) (hx : eoUOpIndicesClosed x) :
    eoUOpIndicesClosed (Term.Apply f x) := by
  exact ⟨hf, hx⟩

/-- Builds the indexed-operator closure fact for unary indexed operators. -/
theorem eoUOpIndicesClosed.uop1 {op : UserOp1} {x : Term}
    (hClosed : __eo_is_closed x = Term.Boolean true)
    (hx : eoUOpIndicesClosed x) :
    eoUOpIndicesClosed (Term.UOp1 op x) := by
  exact ⟨hClosed, hx⟩

/-- Builds the indexed-operator closure fact for binary indexed operators. -/
theorem eoUOpIndicesClosed.uop2 {op : UserOp2} {x y : Term}
    (hxClosed : __eo_is_closed x = Term.Boolean true)
    (hyClosed : __eo_is_closed y = Term.Boolean true)
    (hx : eoUOpIndicesClosed x) (hy : eoUOpIndicesClosed y) :
    eoUOpIndicesClosed (Term.UOp2 op x y) := by
  exact ⟨hxClosed, hyClosed, hx, hy⟩

/-- Builds the indexed-operator closure fact for ternary indexed operators. -/
theorem eoUOpIndicesClosed.uop3 {op : UserOp3} {x y z : Term}
    (hxClosed : __eo_is_closed x = Term.Boolean true)
    (hyClosed : __eo_is_closed y = Term.Boolean true)
    (hzClosed : __eo_is_closed z = Term.Boolean true)
    (hx : eoUOpIndicesClosed x) (hy : eoUOpIndicesClosed y)
    (hz : eoUOpIndicesClosed z) :
    eoUOpIndicesClosed (Term.UOp3 op x y z) := by
  exact ⟨hxClosed, hyClosed, hzClosed, hx, hy, hz⟩

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

/-- Shows that conjunctions built from translatable premises have closed indexed-operator payloads. -/
theorem premiseAndFormulaList_indices_closed :
  ∀ premises : List Term,
    AllHaveSmtTranslation premises ->
    eoUOpIndicesClosed (premiseAndFormulaList premises) :=
by
  intro premises hPremises
  induction premises with
  | nil =>
      simp [premiseAndFormulaList, eoUOpIndicesClosed]
  | cons p premises ih =>
      exact
        eoUOpIndicesClosed.apply
          (eoUOpIndicesClosed.apply (by simp [eoUOpIndicesClosed])
            ((hPremises p (by simp)).indices_closed))
          (ih (by
            intro t ht
            exact hPremises t (by simp [ht])))

/-- Shows that conjunctions built from Boolean, translatable premises are translatable. -/
theorem premiseAndFormulaList_has_smt_translation :
  ∀ premises : List Term,
    AllHaveBoolType premises ->
    AllHaveSmtTranslation premises ->
    eoHasSmtTranslation (premiseAndFormulaList premises) :=
by
  intro premises hPremisesBool hPremisesTrans
  exact eoHasSmtTranslation.of_has_bool_type
    (premiseAndFormulaList_has_bool_type premises hPremisesBool)
    (premiseAndFormulaList_indices_closed premises hPremisesTrans)

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

/--
Standard correctness and translation template for rules that add a proven fact.

Most rules only use `RulePremiseEvidence.true_here`. Binder-sensitive rules use
`RulePremiseEvidence.true_in_var_model` to reason under the fresh variable
models introduced by quantified binders.
-/
structure StepRuleProperties
    (M : SmtModel) (premises : List Term) (P : Term) : Prop where
  facts_of_true :
    RulePremiseEvidence M premises ->
    eo_interprets M P true
  has_smt_translation :
    eoHasSmtTranslation P

/-- Predicate packaging the correctness and translation obligations for rules that also pop assumptions. -/
def StepPopRuleProperties
    (x1 : Term) (premises : List Term) (P : Term) : Prop :=
  ∃ x2,
    x2 ∈ premises ∧
    (forall (M : SmtModel), model_total_typed M ->
      ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
      eo_interprets M P true) ∧
    eoHasSmtTranslation P
