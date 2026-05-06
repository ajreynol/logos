import Cpc.Proofs.TermCompat
import Cpc.Proofs.Translation
import Cpc.Proofs.TypePreservation

open Eo
open SmtEval
open Smtm

namespace RuleProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Simplifies EO-to-SMT translation for `true`. -/
private theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rfl

/-- Simplifies EO-to-SMT translation for `false`. -/
private theorem eo_to_smt_false_eq :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := by
  rfl

/-- Simplifies EO-to-SMT translation for `stuck`. -/
private theorem eo_to_smt_stuck_eq :
    __eo_to_smt Term.Stuck = SmtTerm.None := by
  rfl

/-- Simplifies EO-to-SMT translation for `and`. -/
private theorem eo_to_smt_and_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

/-- Simplifies EO-to-SMT translation for `not`. -/
private theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.not) t) =
      SmtTerm.not (__eo_to_smt t) := by
  rfl

/-- Simplifies EO-to-SMT translation for `imp`. -/
private theorem eo_to_smt_imp_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) =
      SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

/-- Simplifies EO-to-SMT translation for `eq`. -/
private theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

/-- Characterizes EO interpretation in terms of the translated SMT interpretation. -/
theorem eo_interprets_iff_smt_interprets (M : SmtModel) (t : Term) (b : Bool) :
  eo_interprets M t b ↔ smt_interprets M (__eo_to_smt t) b := by
  constructor
  · intro h
    rcases h with ⟨s, hs, hInterp⟩
    cases hs
    simpa using hInterp
  · intro h
    exact ⟨__eo_to_smt t, eo_is_obj.intro t, h⟩

/-- Shows that the EO term `true` is interpreted as `true` in every model. -/
theorem eo_interprets_true (M : SmtModel) :
  eo_interprets M (Term.Boolean true) true := by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_true_eq]
  have hTy : __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool := by
    rw [__smtx_typeof.eq_1]
  have hEval : __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true := by
    rw [__smtx_model_eval.eq_1]
  exact smt_interprets.intro_true M (SmtTerm.Boolean true) hTy hEval

/-- Predicate asserting that translating an EO term yields a non-`None` SMT term. -/
def eo_has_smt_translation (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

/-- Predicate asserting that an EO term translates to SMT Boolean type. -/
def eo_has_bool_type (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Bool

/-- Shows that `Term.Boolean true` has an SMT translation. -/
theorem eo_has_smt_translation_true :
  eo_has_smt_translation (Term.Boolean true) := by
  rw [eo_has_smt_translation, eo_to_smt_true_eq, __smtx_typeof.eq_1]
  decide

/-- Shows that `Term.Boolean true` has translated SMT Boolean type. -/
theorem eo_has_bool_type_true :
  eo_has_bool_type (Term.Boolean true) := by
  rw [eo_has_bool_type, eo_to_smt_true_eq, __smtx_typeof.eq_1]

/-- Derives `eo_has_bool_type` from `interprets_true`. -/
theorem eo_has_bool_type_of_interprets_true (M : SmtModel) (t : Term) :
  eo_interprets M t true ->
  eo_has_bool_type t := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy _ =>
      simpa [eo_has_bool_type] using hTy

/-- Derives `eo_has_bool_type` from `interprets_false`. -/
theorem eo_has_bool_type_of_interprets_false (M : SmtModel) (t : Term) :
  eo_interprets M t false ->
  eo_has_bool_type t := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_false hTy _ =>
      simpa [eo_has_bool_type] using hTy

/-- Shows that `eo_typeof_bool` implies `has_bool_type`. -/
theorem eo_typeof_bool_implies_has_bool_type
    (t : Term) :
  eo_has_smt_translation t ->
  __eo_typeof t = Term.Bool ->
  eo_has_bool_type t := by
  intro hTrans hTy
  exact eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    t (__eo_to_smt t) rfl hTrans hTy

/-- Derives `eo_has_smt_translation` from `has_bool_type`. -/
theorem eo_has_smt_translation_of_has_bool_type (t : Term) :
  eo_has_bool_type t ->
  eo_has_smt_translation t := by
  intro hTy
  intro hNone
  rw [eo_has_bool_type] at hTy
  rw [hNone] at hTy
  cases hTy

/-- Derives `term_ne_stuck` from `has_smt_translation`. -/
theorem term_ne_stuck_of_has_smt_translation (t : Term) :
  eo_has_smt_translation t -> t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  rw [eo_has_smt_translation, eo_to_smt_stuck_eq] at hTy
  exact hTy TranslationProofs.smtx_typeof_none

/-- Derives `eo_has_bool_type_and` from `bool_args`. -/
theorem eo_has_bool_type_and_of_bool_args (A B : Term) :
  eo_has_bool_type A ->
  eo_has_bool_type B ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) := by
  intro hA hB
  unfold eo_has_bool_type at hA hB ⊢
  rw [eo_to_smt_and_eq A B, typeof_and_eq]
  simp [hA, hB, native_ite, native_Teq]

/-- Left-projection lemma for `eo_has_bool_type_and`. -/
theorem eo_has_bool_type_and_left (A B : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) ->
  eo_has_bool_type A := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_and_eq A B] at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
    (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1

/-- Right-projection lemma for `eo_has_bool_type_and`. -/
theorem eo_has_bool_type_and_right (A B : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) ->
  eo_has_bool_type B := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_and_eq A B] at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
    (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2

/-- Derives `eo_has_bool_type_not` from `bool_arg`. -/
theorem eo_has_bool_type_not_of_bool_arg (t : Term) :
  eo_has_bool_type t ->
  eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) t) := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_not_eq t, typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

/-- Shows that a translated `not` term can only be Boolean when its argument is Boolean. -/
theorem eo_has_bool_type_not_arg (t : Term) :
  eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) t) ->
  eo_has_bool_type t := by
  intro hTy
  by_cases hT : __smtx_typeof (__eo_to_smt t) = SmtType.Bool
  · simpa [eo_has_bool_type] using hT
  · have : False := by
      unfold eo_has_bool_type at hTy
      rw [eo_to_smt_not_eq t, typeof_not_eq] at hTy
      simp [hT, native_ite, native_Teq] at hTy
    exact False.elim this

/-- Derives `eo_interprets` from `bool_eval`. -/
theorem eo_interprets_of_bool_eval
    (M : SmtModel) (t : Term) (b : Bool) :
  eo_has_bool_type t ->
  __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b ->
  eo_interprets M t b := by
  intro hTy hEval
  rw [eo_interprets_iff_smt_interprets]
  cases b with
  | false =>
      exact smt_interprets.intro_false M (__eo_to_smt t) hTy hEval
  | true =>
      exact smt_interprets.intro_true M (__eo_to_smt t) hTy hEval

/-- Derives `eo_eval_is_boolean` from `has_bool_type`. -/
theorem eo_eval_is_boolean_of_has_bool_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  eo_has_bool_type t ->
  ∃ b : Bool, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b := by
  intro hTy
  exact smt_model_eval_bool_is_boolean M hM (__eo_to_smt t) hTy

/-- Shows that an EO term cannot be interpreted as both `true` and `false`. -/
theorem eo_interprets_true_not_false (M : SmtModel) (t : Term) :
  eo_interprets M t true -> ¬ eo_interprets M t false := by
  intro hTrue hFalse
  rw [eo_interprets_iff_smt_interprets] at hTrue hFalse
  cases hTrue with
  | intro_true hTyTrue hEvalTrue =>
      cases hFalse with
      | intro_false hTyFalse hEvalFalse =>
          rw [hEvalTrue] at hEvalFalse
          cases hEvalFalse

/-- Left-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true ->
  eo_interprets M A true := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_and_eq A B] at h
  cases h with
  | intro_true hty hEval =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean true := by
        rw [__smtx_model_eval.eq_8] at hEval
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.native_and] at hEval
          simp
      exact smt_interprets.intro_true M (__eo_to_smt A) htyA hEvalA

/-- Right-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true ->
  eo_interprets M B true := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_and_eq A B] at h
  cases h with
  | intro_true hty hEval =>
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2
      have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
        rw [__smtx_model_eval.eq_8] at hEval
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.native_and] at hEval
          simp
      exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

/-- Introduction lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true := by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  rw [eo_to_smt_and_eq A B]
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_true htyB hEvalB =>
          apply smt_interprets.intro_true
          · rw [typeof_and_eq]
            simp [htyA, htyB, native_Teq, native_ite]
          · rw [__smtx_model_eval.eq_8]
            rw [hEvalA, hEvalB]
            simp [__smtx_model_eval_and, SmtEval.native_and]

/-- Elimination lemma for `eo_interprets_imp`. -/
theorem eo_interprets_imp_elim (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) true ->
  eo_interprets M A true ->
  eo_interprets M B true := by
  intro hImp hA
  rw [eo_interprets_iff_smt_interprets] at hImp hA ⊢
  rw [eo_to_smt_imp_eq A B] at hImp
  cases hImp with
  | intro_true htyImp hEvalImp =>
      cases hA with
      | intro_true htyA hEvalA =>
          have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
            have hNN : term_has_non_none_type
                (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
              unfold term_has_non_none_type
              rw [htyImp]
              simp
            exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
              (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2
          have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
            rw [__smtx_model_eval.eq_9] at hEvalImp
            cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
              simp [hEvalA, hBeval, __smtx_model_eval_imp, __smtx_model_eval_or,
                __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not] at hEvalImp
            case Boolean a =>
              cases a <;> simp at hEvalImp
              simp
          exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

/-- Introduction lemma for `eo_interprets_imp`. -/
theorem eo_interprets_imp_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) true := by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  rw [eo_to_smt_imp_eq A B]
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_true htyB hEvalB =>
          apply smt_interprets.intro_true
          · rw [typeof_imp_eq]
            simp [htyA, htyB, native_Teq, native_ite]
          · rw [__smtx_model_eval.eq_9]
            rw [hEvalA, hEvalB]
            simp [__smtx_model_eval_imp, __smtx_model_eval_or,
              __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not]

/-- Left-projection lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) false ->
  eo_interprets M A true := by
  intro hImp
  rw [eo_interprets_iff_smt_interprets] at hImp ⊢
  rw [eo_to_smt_imp_eq A B] at hImp
  cases hImp with
  | intro_false htyImp hEvalImp =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [htyImp]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
          (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean true := by
        rw [__smtx_model_eval.eq_9] at hEvalImp
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_imp, __smtx_model_eval_or,
            __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not] at hEvalImp
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp at hEvalImp
          simp
      exact smt_interprets.intro_true M (__eo_to_smt A) htyA hEvalA

/-- Right-projection lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) false ->
  eo_interprets M B false := by
  intro hImp
  rw [eo_interprets_iff_smt_interprets] at hImp ⊢
  rw [eo_to_smt_imp_eq A B] at hImp
  cases hImp with
  | intro_false htyImp hEvalImp =>
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [htyImp]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
          (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2
      have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean false := by
        rw [__smtx_model_eval.eq_9] at hEvalImp
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_imp, __smtx_model_eval_or,
            __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not] at hEvalImp
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp at hEvalImp
          simp
      exact smt_interprets.intro_false M (__eo_to_smt B) htyB hEvalB

/-- Introduction lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B false ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) false := by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  rw [eo_to_smt_imp_eq A B]
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_false htyB hEvalB =>
          apply smt_interprets.intro_false
          · rw [typeof_imp_eq]
            simp [htyA, htyB, native_Teq, native_ite]
          · rw [__smtx_model_eval.eq_9]
            rw [hEvalA, hEvalB]
            simp [__smtx_model_eval_imp, __smtx_model_eval_or,
              __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not]

/-- Semantic equality relation on SMT values, defined by evaluation of SMT equality. -/
def smt_value_rel (v1 v2 : SmtValue) : Prop :=
  __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true

/-- Semantic equality relation on SMT sequences, lifted through `SmtValue.Seq`. -/
def smt_seq_rel (s1 s2 : SmtSeq) : Prop :=
  __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true

mutual

/-- Establishes an equality relating `smtx_model_eval` and `refl_aux`. -/
private theorem smtx_model_eval_eq_refl_aux :
    (v : SmtValue) -> __smtx_model_eval_eq v v = SmtValue.Boolean true
  | SmtValue.Map _ => by
      simp [__smtx_model_eval_eq]
  | SmtValue.Fun _ => by
      simp [__smtx_model_eval_eq]
  | SmtValue.Set _ => by
      simp [__smtx_model_eval_eq]
  | SmtValue.Seq s => by
      simpa using smtx_model_eval_seq_eq_refl_aux s
  | SmtValue.Apply f x => by
      simp [__smtx_model_eval_eq, native_veq, SmtEval.native_and,
        smtx_model_eval_eq_refl_aux f, smtx_model_eval_eq_refl_aux x]
  | SmtValue.NotValue => by
      simp [__smtx_model_eval_eq, native_veq]
  | SmtValue.Boolean _ => by
      simp [__smtx_model_eval_eq, native_veq]
  | SmtValue.Numeral _ => by
      simp [__smtx_model_eval_eq, native_veq]
  | SmtValue.Rational _ => by
      simp [__smtx_model_eval_eq, native_veq]
  | SmtValue.Binary _ _ => by
      simp [__smtx_model_eval_eq, native_veq]
  | SmtValue.Char _ => by
      simp [__smtx_model_eval_eq, native_veq]
  | SmtValue.UValue _ _ => by
      simp [__smtx_model_eval_eq, native_veq]
  | SmtValue.DtCons _ _ _ => by
      simp [__smtx_model_eval_eq, native_veq]
  | SmtValue.RegLan _ => by
      simp [__smtx_model_eval_eq]

/-- Establishes an equality relating `smtx_model_eval_seq` and `refl_aux`. -/
private theorem smtx_model_eval_seq_eq_refl_aux :
    (s : SmtSeq) -> __smtx_model_eval_eq (SmtValue.Seq s) (SmtValue.Seq s) = SmtValue.Boolean true
  | SmtSeq.empty _ => by
      simp [__smtx_model_eval_eq]
  | SmtSeq.cons v s => by
      simp [__smtx_model_eval_eq, native_veq, SmtEval.native_and,
        smtx_model_eval_eq_refl_aux v, smtx_model_eval_seq_eq_refl_aux s]
end

mutual

/-- Establishes an equality relating `smtx_model_eval` and `true_symm`. -/
private theorem smtx_model_eval_eq_true_symm
    {v1 v2 : SmtValue}
    (h : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true) :
    __smtx_model_eval_eq v2 v1 = SmtValue.Boolean true := by
  cases v1 <;> cases v2
  case Map.Map m1 m2 =>
    classical
    simp [__smtx_model_eval_eq] at h ⊢
    intro v
    symm
    exact h v
  case Fun.Fun m1 m2 =>
    classical
    simp [__smtx_model_eval_eq] at h ⊢
    intro v
    symm
    exact h v
  case Set.Set m1 m2 =>
    classical
    simp [__smtx_model_eval_eq] at h ⊢
    intro v
    symm
    exact h v
  case RegLan.RegLan r1 r2 =>
    classical
    simp [__smtx_model_eval_eq] at h ⊢
    intro s
    symm
    exact h s
  case Seq.Seq s1 s2 =>
    simpa using smtx_model_eval_seq_eq_true_symm h
  case Apply.Apply f1 a1 f2 a2 =>
    simp [__smtx_model_eval_eq, native_veq, SmtEval.native_and] at h ⊢
    exact ⟨smtx_model_eval_eq_true_symm h.1, smtx_model_eval_eq_true_symm h.2⟩
  case DtCons.DtCons s1 d1 i1 s2 d2 i2 =>
    simp [__smtx_model_eval_eq, native_veq] at h ⊢
    exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  all_goals
    simp [__smtx_model_eval_eq, native_veq] at h ⊢
    try exact h
    try exact h.symm
    try exact ⟨h.1.symm, h.2.symm⟩
    try exact False.elim h

/-- Establishes an equality relating `smtx_model_eval_seq` and `true_symm`. -/
private theorem smtx_model_eval_seq_eq_true_symm
    {s1 s2 : SmtSeq}
    (h : __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true) :
    __smtx_model_eval_eq (SmtValue.Seq s2) (SmtValue.Seq s1) = SmtValue.Boolean true := by
  cases s1 <;> cases s2
  case cons.cons v1 s1 v2 s2 =>
    simp [__smtx_model_eval_eq, native_veq, SmtEval.native_and] at h ⊢
    exact ⟨smtx_model_eval_eq_true_symm h.1, smtx_model_eval_seq_eq_true_symm h.2⟩
  case empty.empty T1 T2 =>
    simp [__smtx_model_eval_eq]
  all_goals
    simp [__smtx_model_eval_eq, native_veq] at h

end

mutual

/-- Establishes an equality relating `smtx_model_eval` and `true_trans`. -/
private theorem smtx_model_eval_eq_true_trans
    {v1 v2 v3 : SmtValue}
    (h12 : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true)
    (h23 : __smtx_model_eval_eq v2 v3 = SmtValue.Boolean true) :
    __smtx_model_eval_eq v1 v3 = SmtValue.Boolean true := by
  cases v1 <;> cases v2 <;> cases v3
  case Map.Map.Map m1 m2 m3 =>
    classical
    simp [__smtx_model_eval_eq] at h12 h23 ⊢
    intro v
    calc
      __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v := h12 v
      _ = __smtx_msm_lookup m3 v := h23 v
  case Fun.Fun.Fun m1 m2 m3 =>
    classical
    simp [__smtx_model_eval_eq] at h12 h23 ⊢
    intro v
    calc
      __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v := h12 v
      _ = __smtx_msm_lookup m3 v := h23 v
  case Set.Set.Set m1 m2 m3 =>
    classical
    simp [__smtx_model_eval_eq] at h12 h23 ⊢
    intro v
    calc
      __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v := h12 v
      _ = __smtx_msm_lookup m3 v := h23 v
  case RegLan.RegLan.RegLan r1 r2 r3 =>
    classical
    simp [__smtx_model_eval_eq] at h12 h23 ⊢
    intro s
    exact (h12 s).trans (h23 s)
  case Seq.Seq.Seq s1 s2 s3 =>
    simpa using smtx_model_eval_seq_eq_true_trans h12 h23
  case Apply.Apply.Apply f1 a1 f2 a2 f3 a3 =>
    simp [__smtx_model_eval_eq, native_veq, SmtEval.native_and] at h12 h23 ⊢
    exact ⟨smtx_model_eval_eq_true_trans h12.1 h23.1,
      smtx_model_eval_eq_true_trans h12.2 h23.2⟩
  case DtCons.DtCons.DtCons s1 d1 i1 s2 d2 i2 s3 d3 i3 =>
    simp [__smtx_model_eval_eq, native_veq] at h12 h23 ⊢
    exact ⟨h12.1.trans h23.1, h12.2.1.trans h23.2.1, h12.2.2.trans h23.2.2⟩
  all_goals
    simp [__smtx_model_eval_eq, native_veq] at h12 h23 ⊢
    try exact h12.trans h23
    try exact ⟨h12.1.trans h23.1, h12.2.trans h23.2⟩
    try exact False.elim h12
    try exact False.elim h23
    try trivial

/-- Establishes an equality relating `smtx_model_eval_seq` and `true_trans`. -/
private theorem smtx_model_eval_seq_eq_true_trans
    {s1 s2 s3 : SmtSeq}
    (h12 : __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true)
    (h23 : __smtx_model_eval_eq (SmtValue.Seq s2) (SmtValue.Seq s3) = SmtValue.Boolean true) :
    __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s3) = SmtValue.Boolean true := by
  cases s1 <;> cases s2 <;> cases s3
  case cons.cons.cons v1 s1 v2 s2 v3 s3 =>
    simp [__smtx_model_eval_eq, native_veq, SmtEval.native_and] at h12 h23 ⊢
    exact ⟨smtx_model_eval_eq_true_trans h12.1 h23.1,
      smtx_model_eval_seq_eq_true_trans h12.2 h23.2⟩
  case empty.empty.empty T1 T2 T3 =>
    simp [__smtx_model_eval_eq]
  all_goals
    simp [__smtx_model_eval_eq, native_veq] at h12 h23
    try exact False.elim h12
    try exact False.elim h23

end

/-- Reflexivity lemma for `smt_value_rel`. -/
theorem smt_value_rel_refl (v : SmtValue) : smt_value_rel v v :=
  smtx_model_eval_eq_refl_aux v

/-- Reflexivity lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_refl (s : SmtSeq) : smt_seq_rel s s :=
  smtx_model_eval_seq_eq_refl_aux s

/-- Symmetry lemma for `smt_value_rel`. -/
theorem smt_value_rel_symm (v1 v2 : SmtValue) :
    smt_value_rel v1 v2 ->
    smt_value_rel v2 v1 :=
  smtx_model_eval_eq_true_symm

/-- Symmetry lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_symm (s1 s2 : SmtSeq) :
    smt_seq_rel s1 s2 ->
    smt_seq_rel s2 s1 :=
  smtx_model_eval_seq_eq_true_symm

/-- Transitivity lemma for `smt_value_rel`. -/
theorem smt_value_rel_trans (v1 v2 v3 : SmtValue) :
    smt_value_rel v1 v2 ->
    smt_value_rel v2 v3 ->
    smt_value_rel v1 v3 :=
  smtx_model_eval_eq_true_trans

/-- Transitivity lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_trans (s1 s2 s3 : SmtSeq) :
    smt_seq_rel s1 s2 ->
    smt_seq_rel s2 s3 ->
    smt_seq_rel s1 s3 :=
  smtx_model_eval_seq_eq_true_trans

/-- Characterizes `smt_value_rel` in terms of `model_eval_eq_true`. -/
theorem smt_value_rel_iff_model_eval_eq_true
    (v1 : SmtValue) (v2 : SmtValue) :
    smt_value_rel v1 v2 ↔ __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true :=
  Iff.rfl

/-- Characterizes `smt_seq_rel` in terms of `model_eval_eq_true`. -/
theorem smt_seq_rel_iff_model_eval_eq_true
    (s1 : SmtSeq) (s2 : SmtSeq) :
    smt_seq_rel s1 s2 ↔
      __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true :=
  Iff.rfl

/-- Establishes an equality relating `smtx_typeof` and `bool_iff`. -/
theorem smtx_typeof_eq_bool_iff (T U : SmtType) :
  __smtx_typeof_eq T U = SmtType.Bool ↔ T = U ∧ T ≠ SmtType.None := by
  unfold __smtx_typeof_eq __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · subst hT
    simp [native_ite, native_Teq]
  · by_cases hEq : T = U
    · subst hEq
      simp [native_ite, native_Teq, hT]
    · simp [native_ite, native_Teq, hEq, hT]

/-- Derives `eo_eq_operands_same_smt_type` from `has_bool_type`. -/
theorem eo_eq_operands_same_smt_type_of_has_bool_type (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTy
  unfold eo_has_bool_type at hTy
  rw [eo_to_smt_eq_eq x y] at hTy
  rw [typeof_eq_eq] at hTy
  exact (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y))).mp hTy

/-- Derives `eo_has_bool_type_eq` from `same_smt_type`. -/
theorem eo_has_bool_type_eq_of_same_smt_type (x y : Term) :
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ->
  __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) := by
  intro hTy hNonNone
  unfold eo_has_bool_type
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x))
      (__smtx_typeof (__eo_to_smt y))).mpr ⟨hTy, hNonNone⟩
  rw [eo_to_smt_eq_eq x y, typeof_eq_eq]
  exact hEqTy

/-- Establishes an equality relating `eo_has_bool_type` and `symm`. -/
theorem eo_has_bool_type_eq_symm (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) := by
  intro hTy
  rcases eo_eq_operands_same_smt_type_of_has_bool_type x y hTy with ⟨hEq, hNonNone⟩
  have hNonNone' : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    simpa [hEq] using hNonNone
  exact eo_has_bool_type_eq_of_same_smt_type y x hEq.symm hNonNone'

/-- Derives `eo_has_bool_type_eq` from `bool_chain`. -/
theorem eo_has_bool_type_eq_of_bool_chain (x y z : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) z) ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) z) := by
  intro hXY hYZ
  rcases eo_eq_operands_same_smt_type_of_has_bool_type x y hXY with ⟨hTyXY, hNonNone⟩
  rcases eo_eq_operands_same_smt_type_of_has_bool_type y z hYZ with ⟨hTyYZ, _⟩
  have hTyXZ : __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt z) := by
    rw [hTyXY, hTyYZ]
  exact eo_has_bool_type_eq_of_same_smt_type x z hTyXZ hNonNone

/-- Establishes an equality relating `eo` and `operands_same_smt_type`. -/
theorem eo_eq_operands_same_smt_type (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hEq
  rw [eo_interprets_iff_smt_interprets] at hEq
  rw [eo_to_smt_eq_eq x y] at hEq
  cases hEq with
  | intro_true hTy _ =>
      rw [typeof_eq_eq] at hTy
      exact (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y))).mp hTy

/-- Derives `eo_eq_operands_same_smt_type` from `false`. -/
theorem eo_eq_operands_same_smt_type_of_false (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) false ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hEq
  rw [eo_interprets_iff_smt_interprets] at hEq
  rw [eo_to_smt_eq_eq x y] at hEq
  cases hEq with
  | intro_false hTy _ =>
      rw [typeof_eq_eq] at hTy
      exact (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y))).mp hTy

/-- Derives `eo_has_bool_type_eq` from `true_chain`. -/
theorem eo_has_bool_type_eq_of_true_chain (M : SmtModel) (x y z : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) z) true ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) z) := by
  intro hXY hYZ
  rcases eo_eq_operands_same_smt_type M x y hXY with ⟨hTyXY, hNonNone⟩
  rcases eo_eq_operands_same_smt_type M y z hYZ with ⟨hTyYZ, _⟩
  have hTyXZ : __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt z) := by
    rw [hTyXY, hTyYZ]
  unfold eo_has_bool_type
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt z)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt z))).mpr ⟨hTyXZ, hNonNone⟩
  rw [eo_to_smt_eq_eq x z, typeof_eq_eq]
  exact hEqTy

/-- Derives `eo_has_bool_type_eq` from `true`. -/
theorem eo_has_bool_type_eq_of_true (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) := by
  intro hXY
  rcases eo_eq_operands_same_smt_type M x y hXY with ⟨hTyXY, hNonNone⟩
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y))).mpr ⟨hTyXY, hNonNone⟩
  unfold eo_has_bool_type
  rw [eo_to_smt_eq_eq x y, typeof_eq_eq]
  exact hEqTy

/-- Establishes an equality relating `eo_interprets` and `rel`. -/
theorem eo_interprets_eq_rel (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  smt_value_rel (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hEq
  rw [smt_value_rel_iff_model_eval_eq_true]
  rw [eo_interprets_iff_smt_interprets] at hEq
  rw [eo_to_smt_eq_eq x y] at hEq
  cases hEq with
  | intro_true _ hEval =>
      rw [__smtx_model_eval.eq_133] at hEval
      exact hEval

/-- Derives `eo_interprets_eq` from `rel`. -/
theorem eo_interprets_eq_of_rel (M : SmtModel) (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  smt_value_rel (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y)) ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true := by
  intro hTy hRel
  rw [eo_interprets_iff_smt_interprets]
  rw [eo_to_smt_eq_eq x y]
  have hTyEq :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y)) = SmtType.Bool := by
    rw [eo_has_bool_type, eo_to_smt_eq_eq x y, typeof_eq_eq] at hTy
    exact hTy
  have hTy' :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.Bool := by
    rw [typeof_eq_eq]
    exact hTyEq
  refine smt_interprets.intro_true M
      (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) ?_ ?_
  · exact hTy'
  · have hEvalEq :
        __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean true :=
      (smt_value_rel_iff_model_eval_eq_true
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))).mp hRel
    rw [__smtx_model_eval.eq_133]
    exact hEvalEq

/-- Establishes an equality relating `eo_interprets` and `trans`. -/
theorem eo_interprets_eq_trans (M : SmtModel) (x y z : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) z) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) z) true := by
  intro hXY hYZ
  apply eo_interprets_eq_of_rel M x z
  · exact eo_has_bool_type_eq_of_true_chain M x y z hXY hYZ
  · exact smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z))
      (eo_interprets_eq_rel M x y hXY)
      (eo_interprets_eq_rel M y z hYZ)

/-- Derives `eo_interprets_not` from `false`. -/
theorem eo_interprets_not_of_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> eo_interprets M (Term.Apply (Term.UOp UserOp.not) t) true := by
  intro hFalse
  rw [eo_interprets_iff_smt_interprets] at hFalse ⊢
  rw [eo_to_smt_not_eq t]
  cases hFalse with
  | intro_false hTy hEval =>
      refine smt_interprets.intro_true M
          (SmtTerm.not (__eo_to_smt t)) ?_ ?_
      · rw [typeof_not_eq]
        simp [hTy, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_6]
        rw [hEval]
        simp [__smtx_model_eval_not, SmtEval.native_not]

/-- Derives `term_ne_stuck` from `interprets_true`. -/
theorem term_ne_stuck_of_interprets_true (M : SmtModel) (t : Term) :
  eo_interprets M t true -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq] at h
  cases h with
  | intro_true hTy _ =>
      simp [TranslationProofs.smtx_typeof_none] at hTy

/-- Derives `term_ne_stuck` from `interprets_false`. -/
theorem term_ne_stuck_of_interprets_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq] at h
  cases h with
  | intro_false hTy _ =>
      simp [TranslationProofs.smtx_typeof_none] at hTy

/-- Derives `term_ne_stuck` from `has_bool_type`. -/
theorem term_ne_stuck_of_has_bool_type (t : Term) :
  eo_has_bool_type t -> t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  rw [eo_has_bool_type, eo_to_smt_stuck_eq] at hTy
  simp [TranslationProofs.smtx_typeof_none] at hTy

set_option linter.unusedSimpArgs false in
/-- Shows that `eo_interprets_not_true` implies `false`. -/
theorem eo_interprets_not_true_implies_false (M : SmtModel) (t : Term) :
  eo_interprets M (Term.Apply (Term.UOp UserOp.not) t) true -> eo_interprets M t false := by
  intro h
  have htyt : __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
    exact eo_has_bool_type_not_arg t
      (eo_has_bool_type_of_interprets_true M (Term.Apply (Term.UOp UserOp.not) t) h)
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_not_eq t] at h
  cases h with
  | intro_true hty hEval =>
      rw [__smtx_model_eval.eq_6] at hEval
      cases ht : __smtx_model_eval M (__eo_to_smt t) with
      | NotValue =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Boolean b =>
          cases b with
          | false =>
              exact smt_interprets.intro_false M (__eo_to_smt t) htyt ht
          | true =>
              exfalso
              simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Numeral n =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Rational q =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Binary w n =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Map m =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Fun m =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Set m =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Seq s =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Char c =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | UValue s i =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | RegLan r =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | DtCons s d i =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Apply f x =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval

/-- Establishes an equality relating `smtx_typeof` and `refl`. -/
theorem smtx_typeof_eq_refl (T : SmtType) :
  T ≠ SmtType.None -> __smtx_typeof_eq T T = SmtType.Bool := by
  intro hT
  unfold __smtx_typeof_eq __smtx_typeof_guard
  simp [native_ite, native_Teq, hT]

/-- Establishes an equality relating `smtx_model_eval` and `refl`. -/
theorem smtx_model_eval_eq_refl (v : SmtValue) :
  __smtx_model_eval_eq v v = SmtValue.Boolean true := by
  exact (smt_value_rel_iff_model_eval_eq_true v v).mp (smt_value_rel_refl v)

end RuleProofs
