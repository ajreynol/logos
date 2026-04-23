import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CnfSupport
import Cpc.Proofs.RuleSupport.StringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private inductive OrClause : Term -> Prop where
  | false : OrClause (Term.Boolean false)
  | cons (x xs : Term) : OrClause xs ->
      OrClause (Term.Apply (Term.Apply Term.or x) xs)

private theorem is_ok_true_of_ne_stuck {x : Term} :
    x ≠ Term.Stuck ->
    __eo_is_ok x = Term.Boolean true := by
  intro hNe
  cases x <;> simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at hNe ⊢

private theorem is_list_true_of_get_nil_rec_ne_stuck {f x : Term} :
    __eo_get_nil_rec f x ≠ Term.Stuck ->
    __eo_is_list f x = Term.Boolean true := by
  intro hRec
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst hF
    simpa [__eo_get_nil_rec] using hRec
  have hX : x ≠ Term.Stuck := by
    intro hX
    subst hX
    simpa [__eo_get_nil_rec] using hRec
  simp [__eo_is_list, hF, hX, is_ok_true_of_ne_stuck hRec]

private theorem orClause_of_is_list_true {c : Term} :
    __eo_is_list Term.or c = Term.Boolean true -> OrClause c := by
  intro hList
  cases c with
  | Stuck =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, native_teq, native_not,
        SmtEval.native_not] at hList
  | Boolean b =>
      cases b with
      | false =>
          exact OrClause.false
      | true =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | or =>
                  unfold __eo_is_list at hList
                  unfold __eo_is_ok at hList
                  unfold __eo_get_nil_rec at hList
                  unfold __eo_requires at hList
                  simp [native_ite, native_teq, native_not, SmtEval.native_not] at hList
                  exact OrClause.cons x a
                    (orClause_of_is_list_true (is_list_true_of_get_nil_rec_ne_stuck hList))
              | _ =>
                  simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                    __eo_is_list_nil, native_ite, native_teq, native_not,
                    SmtEval.native_not] at hList
          | _ =>
              simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                __eo_is_list_nil, native_ite, native_teq, native_not,
                SmtEval.native_not] at hList
      | _ =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | _ =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList

private theorem orClause_get_nil_rec_ne_stuck {c : Term} :
    OrClause c -> __eo_get_nil_rec Term.or c ≠ Term.Stuck := by
  intro hClause
  induction hClause with
  | false =>
      simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil, native_ite,
        native_teq, native_not, SmtEval.native_not]
  | cons x xs hXs ih =>
      simpa [__eo_get_nil_rec, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] using ih

private theorem orClause_is_list_true {c : Term} :
    OrClause c -> __eo_is_list Term.or c = Term.Boolean true := by
  intro hClause
  exact is_list_true_of_get_nil_rec_ne_stuck (orClause_get_nil_rec_ne_stuck hClause)

private theorem orClause_ne_stuck {c : Term} :
    OrClause c -> c ≠ Term.Stuck := by
  intro hClause
  cases hClause <;> simp

private theorem eo_eq_eq_true_of_eq {x y : Term} :
    x = y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean true := by
  intro hEq hX hY
  subst y
  cases x <;> simp [__eo_eq, native_teq] at hX ⊢

private theorem eo_eq_eq_false_of_ne {x y : Term} :
    x ≠ y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean false := by
  intro hNe hX hY
  by_cases hEq : x = y
  · exact False.elim (hNe hEq)
  · cases x <;> cases y <;>
      simp [__eo_eq, native_teq, eq_comm, hEq] at hNe hX hY ⊢ <;> contradiction

private theorem list_erase_rec_cons_eq
    (x xs e : Term) :
    x = e ->
    x ≠ Term.Stuck ->
    e ≠ Term.Stuck ->
    __eo_list_erase_rec (Term.Apply (Term.Apply Term.or x) xs) e = xs := by
  intro hEq hX hE
  have hEqTerm : __eo_eq x e = Term.Boolean true :=
    eo_eq_eq_true_of_eq hEq hX hE
  simp [__eo_list_erase_rec, hEqTerm, __eo_ite, native_ite, native_teq]

private theorem list_erase_rec_cons_ne
    (x xs e : Term) :
    x ≠ e ->
    x ≠ Term.Stuck ->
    e ≠ Term.Stuck ->
    __eo_list_erase_rec xs e ≠ Term.Stuck ->
    __eo_list_erase_rec (Term.Apply (Term.Apply Term.or x) xs) e =
      Term.Apply (Term.Apply Term.or x) (__eo_list_erase_rec xs e) := by
  intro hNe hX hE hTail
  have hEqTerm : __eo_eq x e = Term.Boolean false :=
    eo_eq_eq_false_of_ne hNe hX hE
  cases hRec : __eo_list_erase_rec xs e <;>
    simp [__eo_list_erase_rec, hEqTerm, __eo_ite, __eo_mk_apply, native_ite, native_teq,
      hRec] at hTail ⊢

private theorem erase_rec_preserves_orClause {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    OrClause (__eo_list_erase_rec c e) := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_rec] using OrClause.false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTail : OrClause (__eo_list_erase_rec xs e) := ih hXsBool hE
      have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
        orClause_ne_stuck hTail
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        exact hXs
      · rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
        exact OrClause.cons x (__eo_list_erase_rec xs e) hTail

private theorem erase_preserves_orClause {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    OrClause (__eo_list_erase Term.or c e) := by
  intro hClause hCBool hE
  change OrClause
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true)
      (__eo_list_erase_rec c e))
  rw [orClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact erase_rec_preserves_orClause hClause hCBool hE

private theorem eo_interprets_false (M : SmtModel) :
    eo_interprets M (Term.Boolean false) false := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by
    rw [__eo_to_smt.eq_def]]
  refine smt_interprets.intro_false M (SmtTerm.Boolean false) ?_ ?_
  · rw [__smtx_typeof.eq_1]
  · rw [__smtx_model_eval.eq_1]

private theorem eo_interprets_or_right_of_left_false
    (M : SmtModel) (hM : model_total_typed M) (A B : Term) :
    eo_interprets M A false ->
    eo_interprets M (Term.Apply (Term.Apply Term.or A) B) true ->
    eo_interprets M B true := by
  intro hAFalse hOrTrue
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_of_interprets_false M A hAFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse hOrTrue ⊢
  rw [RuleProofs.eo_to_smt_or_eq A B] at hOrTrue
  cases hAFalse with
  | intro_false _ hEvalA =>
      cases hOrTrue with
      | intro_true hTyOr hEvalOr =>
          have hBBool : RuleProofs.eo_has_bool_type B :=
            RuleProofs.eo_has_bool_type_or_right A B
              (by simpa [RuleProofs.eo_has_bool_type, RuleProofs.eo_to_smt_or_eq] using hTyOr)
          refine smt_interprets.intro_true M (__eo_to_smt B) hBBool ?_
          rw [__smtx_model_eval.eq_7] at hEvalOr
          rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM B hBBool with ⟨b, hEvalB⟩
          rw [hEvalA, hEvalB, __smtx_model_eval_or, SmtEval.native_or] at hEvalOr
          cases b <;> simp at hEvalOr
          exact hEvalB

private theorem eo_interprets_or_left_of_right_false
    (M : SmtModel) (hM : model_total_typed M) (A B : Term) :
    eo_interprets M B false ->
    eo_interprets M (Term.Apply (Term.Apply Term.or A) B) true ->
    eo_interprets M A true := by
  intro hBFalse hOrTrue
  have hBBool : RuleProofs.eo_has_bool_type B :=
    RuleProofs.eo_has_bool_type_of_interprets_false M B hBFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hBFalse hOrTrue ⊢
  rw [RuleProofs.eo_to_smt_or_eq A B] at hOrTrue
  cases hBFalse with
  | intro_false _ hEvalB =>
      cases hOrTrue with
      | intro_true hTyOr hEvalOr =>
          have hABool : RuleProofs.eo_has_bool_type A :=
            RuleProofs.eo_has_bool_type_or_left A B
              (by simpa [RuleProofs.eo_has_bool_type, RuleProofs.eo_to_smt_or_eq] using hTyOr)
          refine smt_interprets.intro_true M (__eo_to_smt A) hABool ?_
          rw [__smtx_model_eval.eq_7] at hEvalOr
          rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with ⟨a, hEvalA⟩
          rw [hEvalA, hEvalB, __smtx_model_eval_or, SmtEval.native_or] at hEvalOr
          cases a <;> simp at hEvalOr
          exact hEvalA

private theorem eo_interprets_or_false_intro
    (M : SmtModel) (hM : model_total_typed M) (A B : Term) :
    eo_interprets M A false ->
    eo_interprets M B false ->
    eo_interprets M (Term.Apply (Term.Apply Term.or A) B) false := by
  intro hAFalse hBFalse
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_of_interprets_false M A hAFalse
  have hBBool : RuleProofs.eo_has_bool_type B :=
    RuleProofs.eo_has_bool_type_of_interprets_false M B hBFalse
  have hOrBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.or A) B) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args A B hABool hBBool
  rcases CnfSupport.eo_interprets_bool_cases M hM (Term.Apply (Term.Apply Term.or A) B) hOrBool with
    hOrTrue | hOrFalse
  · have hATrue : eo_interprets M A true :=
      eo_interprets_or_left_of_right_false M hM A B hBFalse hOrTrue
    exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hATrue) hAFalse)
  · exact hOrFalse

private theorem eo_interprets_not_false_of_true (M : SmtModel) (t : Term) :
    eo_interprets M t true ->
    eo_interprets M (Term.Apply Term.not t) false := by
  intro hTrue
  have hTy : RuleProofs.eo_has_bool_type t :=
    RuleProofs.eo_has_bool_type_of_interprets_true M t hTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hTrue ⊢
  rw [show __eo_to_smt (Term.Apply Term.not t) = SmtTerm.not (__eo_to_smt t) by
    rw [__eo_to_smt.eq_def]]
  cases hTrue with
  | intro_true _ hEval =>
      refine smt_interprets.intro_false M (SmtTerm.not (__eo_to_smt t)) ?_ ?_
      · simpa [RuleProofs.eo_has_bool_type, show __eo_to_smt (Term.Apply Term.not t) =
            SmtTerm.not (__eo_to_smt t) by rw [__eo_to_smt.eq_def]]
          using RuleProofs.eo_has_bool_type_not_of_bool_arg t hTy
      · rw [__smtx_model_eval.eq_6]
        rw [hEval]
        simp [__smtx_model_eval_not, SmtEval.native_not]

private theorem to_clause_has_bool_type {c : Term} :
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type (__to_clause c) := by
  intro hCBool
  cases c with
  | Stuck =>
      exact False.elim ((RuleProofs.term_ne_stuck_of_has_bool_type _ hCBool) rfl)
  | Apply f a =>
      cases hf : f with
      | Apply g x =>
          rw [hf] at hCBool
          cases hg : g with
          | UOp op =>
              cases op with
              | or =>
                  simpa [__to_clause, hf, hg] using hCBool
              | _ =>
                  simpa [__to_clause, hf, hg] using
                    RuleProofs.eo_has_bool_type_or_of_bool_args
                      (Term.Apply (Term.Apply g x) a) (Term.Boolean false)
                      hCBool RuleProofs.eo_has_bool_type_false
          | _ =>
              simpa [__to_clause, hf, hg] using
                RuleProofs.eo_has_bool_type_or_of_bool_args
                  (Term.Apply (Term.Apply g x) a) (Term.Boolean false)
                  hCBool RuleProofs.eo_has_bool_type_false
      | _ =>
          simpa [__to_clause, hf] using
            RuleProofs.eo_has_bool_type_or_of_bool_args
              (Term.Apply f a) (Term.Boolean false) hCBool RuleProofs.eo_has_bool_type_false
  | Boolean b =>
      cases b with
      | false =>
          simpa [__to_clause] using RuleProofs.eo_has_bool_type_false
      | true =>
          simpa [__to_clause] using
            RuleProofs.eo_has_bool_type_or_of_bool_args
              (Term.Boolean true) (Term.Boolean false)
              hCBool RuleProofs.eo_has_bool_type_false
  | _ =>
      simpa [__to_clause] using
        RuleProofs.eo_has_bool_type_or_of_bool_args
          _ (Term.Boolean false) hCBool RuleProofs.eo_has_bool_type_false

private theorem to_clause_interprets_true
    (M : SmtModel) (hM : model_total_typed M) {c : Term} :
    eo_interprets M c true ->
    eo_interprets M (__to_clause c) true := by
  intro hCTrue
  have hCBool : RuleProofs.eo_has_bool_type c :=
    RuleProofs.eo_has_bool_type_of_interprets_true M c hCTrue
  cases c with
  | Stuck =>
      exact False.elim ((RuleProofs.term_ne_stuck_of_interprets_true M _ hCTrue) rfl)
  | Apply f a =>
      cases hf : f with
      | Apply g x =>
          rw [hf] at hCTrue
          cases hg : g with
          | UOp op =>
              cases op with
              | or =>
                  simpa [__to_clause, hf, hg] using hCTrue
              | _ =>
                  simpa [__to_clause, hf, hg] using
                    RuleProofs.eo_interprets_or_left_intro M hM
                      (Term.Apply (Term.Apply g x) a) (Term.Boolean false) hCTrue
                      RuleProofs.eo_has_bool_type_false
          | _ =>
              simpa [__to_clause, hf, hg] using
                RuleProofs.eo_interprets_or_left_intro M hM
                  (Term.Apply (Term.Apply g x) a) (Term.Boolean false) hCTrue
                  RuleProofs.eo_has_bool_type_false
      | _ =>
          simpa [__to_clause, hf] using
            RuleProofs.eo_interprets_or_left_intro M hM
              (Term.Apply f a) (Term.Boolean false) hCTrue
              RuleProofs.eo_has_bool_type_false
  | Boolean b =>
      cases b with
      | false =>
          exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hCTrue)
            (eo_interprets_false M))
      | true =>
          simpa [__to_clause] using
            RuleProofs.eo_interprets_or_left_intro M hM
              (Term.Boolean true) (Term.Boolean false) hCTrue
              RuleProofs.eo_has_bool_type_false
  | _ =>
      simpa [__to_clause] using
        RuleProofs.eo_interprets_or_left_intro M hM
          _ (Term.Boolean false) hCTrue RuleProofs.eo_has_bool_type_false

private theorem list_erase_nonstuck_input_orClause {c e : Term} :
    __eo_list_erase Term.or c e ≠ Term.Stuck ->
    OrClause c := by
  intro hErase
  have hList : __eo_is_list Term.or c = Term.Boolean true := by
    cases hIs : __eo_is_list Term.or c with
    | Boolean b =>
        simp [__eo_list_erase, __eo_requires, hIs, native_ite, native_teq, native_not,
          SmtEval.native_not] at hErase ⊢
        exact hErase.1
    | _ =>
        simp [__eo_list_erase, __eo_requires, hIs, native_ite, native_teq, native_not,
          SmtEval.native_not] at hErase
  exact orClause_of_is_list_true hList

private theorem list_erase_nonstuck_lit_ne_stuck {c e : Term} :
    __eo_list_erase Term.or c e ≠ Term.Stuck ->
    e ≠ Term.Stuck := by
  intro hErase hE
  subst hE
  simp [__eo_list_erase, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hErase
  have hRecStuck : __eo_list_erase_rec c Term.Stuck = Term.Stuck := by
    cases c <;> simp [__eo_list_erase_rec]
  exact hErase.2.2 hRecStuck

private theorem eo_interprets_bool_cases
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
    RuleProofs.eo_has_bool_type t ->
    eo_interprets M t true ∨ eo_interprets M t false := by
  intro hTy
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM t hTy with ⟨b, hEval⟩
  cases b with
  | true =>
      exact Or.inl (RuleProofs.eo_interprets_of_bool_eval M t true hTy hEval)
  | false =>
      exact Or.inr (RuleProofs.eo_interprets_of_bool_eval M t false hTy hEval)

private theorem erase_rec_preserves_bool_type {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_erase_rec c e) := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_rec] using RuleProofs.eo_has_bool_type_false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        exact hXsBool
      · have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_rec xs e) :=
          ih hXsBool hE
        have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
        exact RuleProofs.eo_has_bool_type_or_of_bool_args x (__eo_list_erase_rec xs e)
          hXBool hTailBool

private theorem erase_preserves_bool_type {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_erase Term.or c e) := by
  intro hClause hCBool hE
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true) (__eo_list_erase_rec c e))
  rw [orClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact erase_rec_preserves_bool_type hClause hCBool hE

private theorem erase_rec_true_of_good_lit
    (M : SmtModel) (hM : model_total_typed M) {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    (¬ RuleProofs.eo_has_bool_type e ∨ eo_interprets M e false) ->
    e ≠ Term.Stuck ->
    eo_interprets M (__eo_list_erase_rec c e) true := by
  intro hClause hCBool hCTrue hGood hE
  induction hClause generalizing e with
  | false =>
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hCTrue)
        (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_rec xs e) :=
        erase_rec_preserves_bool_type hXs hXsBool hE
      have hOrTrue : eo_interprets M (Term.Apply (Term.Apply Term.or x) xs) true := by
        simpa using hCTrue
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        cases hGood with
        | inl hENotBool =>
            exfalso
            apply hENotBool
            simpa [hEq] using hXBool
        | inr hEFalse =>
            have hXFalse : eo_interprets M x false := by
              simpa [hEq] using hEFalse
            exact eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
      · rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
        · have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
          rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
          exact RuleProofs.eo_interprets_or_left_intro M hM
            x (__eo_list_erase_rec xs e) hXTrue hTailBool
        · have hXsTrue : eo_interprets M xs true :=
            eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
          have hTailTrue : eo_interprets M (__eo_list_erase_rec xs e) true :=
            ih hXsBool hXsTrue hGood hE
          have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
          rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
          exact RuleProofs.eo_interprets_or_right_intro M hM
            x (__eo_list_erase_rec xs e) hXBool hTailTrue

private theorem erase_true_of_good_lit
    (M : SmtModel) (hM : model_total_typed M) {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    (¬ RuleProofs.eo_has_bool_type e ∨ eo_interprets M e false) ->
    e ≠ Term.Stuck ->
    eo_interprets M (__eo_list_erase Term.or c e) true := by
  intro hClause hCBool hCTrue hGood hE
  change eo_interprets M
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true) (__eo_list_erase_rec c e)) true
  rw [orClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact erase_rec_true_of_good_lit M hM hClause hCBool hCTrue hGood hE

private theorem concat_rec_preserves_orClause {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    OrClause (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC2
  have concat_rec_false (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  have concat_rec_cons (x xs z : Term) :
      __eo_list_concat_rec xs z ≠ Term.Stuck ->
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z =
        Term.Apply (Term.Apply Term.or x) (__eo_list_concat_rec xs z) := by
    intro hTail
    cases z with
    | Stuck =>
        have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
          cases xs <;> simp [__eo_list_concat_rec]
        exact False.elim (hTail hStuck)
    | _ =>
        simp [__eo_list_concat_rec, __eo_mk_apply]
  induction hC1 generalizing c2 with
  | false =>
      rw [concat_rec_false c2]
      exact hC2
  | cons x xs hXs ih =>
      have hTail : OrClause (__eo_list_concat_rec xs c2) := ih hC2
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck := orClause_ne_stuck hTail
      rw [concat_rec_cons x xs c2 hTailNe]
      exact OrClause.cons x (__eo_list_concat_rec xs c2) hTail

private theorem concat_preserves_orClause {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    OrClause (__eo_list_concat Term.or c1 c2) := by
  intro hC1 hC2
  change OrClause
    (__eo_requires (__eo_is_list Term.or c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [orClause_is_list_true hC1, orClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact concat_rec_preserves_orClause hC1 hC2

private theorem concat_rec_preserves_bool_type {c1 c2 : Term} :
    OrClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC1Bool hC2Bool
  have concat_rec_false (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  have concat_rec_cons (x xs z : Term) :
      __eo_list_concat_rec xs z ≠ Term.Stuck ->
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z =
        Term.Apply (Term.Apply Term.or x) (__eo_list_concat_rec xs z) := by
    intro hTail
    cases z with
    | Stuck =>
        have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
          cases xs <;> simp [__eo_list_concat_rec]
        exact False.elim (hTail hStuck)
    | _ =>
        simp [__eo_list_concat_rec, __eo_mk_apply]
  induction hC1 generalizing c2 with
  | false =>
      rw [concat_rec_false c2]
      exact hC2Bool
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hC1Bool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        ih hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [concat_rec_cons x xs c2 hTailNe]
      exact RuleProofs.eo_has_bool_type_or_of_bool_args
        x (__eo_list_concat_rec xs c2) hXBool hTailBool

private theorem concat_preserves_bool_type {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat Term.or c1 c2) := by
  intro hC1 hC2 hC1Bool hC2Bool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list Term.or c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [orClause_is_list_true hC1, orClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact concat_rec_preserves_bool_type hC1 hC1Bool hC2Bool

private theorem concat_rec_bool_type_implies_left {c1 c2 : Term} :
    OrClause c1 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat_rec c1 c2) ->
    RuleProofs.eo_has_bool_type c1 := by
  intro hC1 hConcatBool
  have concat_rec_false (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  have concat_rec_cons (x xs z : Term) :
      __eo_list_concat_rec xs z ≠ Term.Stuck ->
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z =
        Term.Apply (Term.Apply Term.or x) (__eo_list_concat_rec xs z) := by
    intro hTail
    cases z with
    | Stuck =>
        have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
          cases xs <;> simp [__eo_list_concat_rec]
        exact False.elim (hTail hStuck)
    | _ =>
        simp [__eo_list_concat_rec, __eo_mk_apply]
  have concat_rec_cons_tail_ne_stuck (x xs z : Term) :
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z ≠ Term.Stuck ->
      __eo_list_concat_rec xs z ≠ Term.Stuck := by
    intro hConcat hTail
    cases z <;> simp [__eo_list_concat_rec, __eo_mk_apply, hTail] at hConcat
  induction hC1 generalizing c2 with
  | false =>
      exact RuleProofs.eo_has_bool_type_false
  | cons x xs hXs ih =>
      have hConcatNe :
          __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hConcatBool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        concat_rec_cons_tail_ne_stuck x xs c2 hConcatNe
      rw [concat_rec_cons x xs c2 hTailNe] at hConcatBool
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x (__eo_list_concat_rec xs c2) hConcatBool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        RuleProofs.eo_has_bool_type_or_right x (__eo_list_concat_rec xs c2) hConcatBool
      have hXsBool : RuleProofs.eo_has_bool_type xs := ih hTailBool
      exact RuleProofs.eo_has_bool_type_or_of_bool_args x xs hXBool hXsBool

private theorem concat_bool_type_implies_left {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat Term.or c1 c2) ->
    RuleProofs.eo_has_bool_type c1 := by
  intro hC1 hC2 hConcatBool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list Term.or c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) at hConcatBool
  rw [orClause_is_list_true hC1, orClause_is_list_true hC2] at hConcatBool
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hConcatBool
  exact concat_rec_bool_type_implies_left hC1 hConcatBool

private theorem concat_rec_bool_type_implies_right {c1 c2 : Term} :
    OrClause c1 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat_rec c1 c2) ->
    RuleProofs.eo_has_bool_type c2 := by
  intro hC1 hConcatBool
  have concat_rec_false (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  have concat_rec_cons (x xs z : Term) :
      __eo_list_concat_rec xs z ≠ Term.Stuck ->
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z =
        Term.Apply (Term.Apply Term.or x) (__eo_list_concat_rec xs z) := by
    intro hTail
    cases z with
    | Stuck =>
        have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
          cases xs <;> simp [__eo_list_concat_rec]
        exact False.elim (hTail hStuck)
    | _ =>
        simp [__eo_list_concat_rec, __eo_mk_apply]
  have concat_rec_cons_tail_ne_stuck (x xs z : Term) :
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z ≠ Term.Stuck ->
      __eo_list_concat_rec xs z ≠ Term.Stuck := by
    intro hConcat hTail
    cases z <;> simp [__eo_list_concat_rec, __eo_mk_apply, hTail] at hConcat
  induction hC1 generalizing c2 with
  | false =>
      rw [concat_rec_false c2] at hConcatBool
      exact hConcatBool
  | cons x xs hXs ih =>
      have hConcatNe :
          __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hConcatBool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        concat_rec_cons_tail_ne_stuck x xs c2 hConcatNe
      rw [concat_rec_cons x xs c2 hTailNe] at hConcatBool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        RuleProofs.eo_has_bool_type_or_right x (__eo_list_concat_rec xs c2) hConcatBool
      exact ih hTailBool

private theorem concat_bool_type_implies_right {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat Term.or c1 c2) ->
    RuleProofs.eo_has_bool_type c2 := by
  intro hC1 hC2 hConcatBool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list Term.or c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) at hConcatBool
  rw [orClause_is_list_true hC1, orClause_is_list_true hC2] at hConcatBool
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hConcatBool
  exact concat_rec_bool_type_implies_right hC1 hConcatBool

private theorem concat_rec_true_of_left_true
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    OrClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c1 true ->
    eo_interprets M (__eo_list_concat_rec c1 c2) true := by
  intro hC1 hC1Bool hC2Bool hC1True
  have concat_rec_false (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  have concat_rec_cons (x xs z : Term) :
      __eo_list_concat_rec xs z ≠ Term.Stuck ->
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z =
        Term.Apply (Term.Apply Term.or x) (__eo_list_concat_rec xs z) := by
    intro hTail
    cases z with
    | Stuck =>
        have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
          cases xs <;> simp [__eo_list_concat_rec]
        exact False.elim (hTail hStuck)
    | _ =>
        simp [__eo_list_concat_rec, __eo_mk_apply]
  induction hC1 generalizing c2 with
  | false =>
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hC1True)
        (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hC1Bool
      have hOrTrue : eo_interprets M (Term.Apply (Term.Apply Term.or x) xs) true := by
        simpa using hC1True
      rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
      · have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
            concat_rec_preserves_bool_type hXs hXsBool hC2Bool
        have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rw [concat_rec_cons x xs c2 hTailNe]
        exact RuleProofs.eo_interprets_or_left_intro M hM
          x (__eo_list_concat_rec xs c2) hXTrue hTailBool
      · have hXsTrue : eo_interprets M xs true :=
          eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
        have hTailTrue : eo_interprets M (__eo_list_concat_rec xs c2) true :=
          ih hXsBool hC2Bool hXsTrue
        have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
          concat_rec_preserves_bool_type hXs hXsBool hC2Bool
        have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rw [concat_rec_cons x xs c2 hTailNe]
        exact RuleProofs.eo_interprets_or_right_intro M hM
          x (__eo_list_concat_rec xs c2) hXBool hTailTrue

private theorem concat_rec_true_of_right_true
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    OrClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c2 true ->
    eo_interprets M (__eo_list_concat_rec c1 c2) true := by
  intro hC1 hC1Bool hC2Bool hC2True
  have concat_rec_false (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  have concat_rec_cons (x xs z : Term) :
      __eo_list_concat_rec xs z ≠ Term.Stuck ->
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z =
        Term.Apply (Term.Apply Term.or x) (__eo_list_concat_rec xs z) := by
    intro hTail
    cases z with
    | Stuck =>
        have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
          cases xs <;> simp [__eo_list_concat_rec]
        exact False.elim (hTail hStuck)
    | _ =>
        simp [__eo_list_concat_rec, __eo_mk_apply]
  induction hC1 generalizing c2 with
  | false =>
      rw [concat_rec_false c2]
      exact hC2True
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hC1Bool
      have hTailTrue : eo_interprets M (__eo_list_concat_rec xs c2) true :=
        ih hXsBool hC2Bool hC2True
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        concat_rec_preserves_bool_type hXs hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [concat_rec_cons x xs c2 hTailNe]
      exact RuleProofs.eo_interprets_or_right_intro M hM
        x (__eo_list_concat_rec xs c2) hXBool hTailTrue

private theorem concat_true_of_left_true
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c1 true ->
    eo_interprets M (__eo_list_concat Term.or c1 c2) true := by
  intro hC1 hC2 hC1Bool hC2Bool hC1True
  change eo_interprets M
    (__eo_requires (__eo_is_list Term.or c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) true
  rw [orClause_is_list_true hC1, orClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact concat_rec_true_of_left_true M hM hC1 hC1Bool hC2Bool hC1True

private theorem concat_true_of_right_true
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c2 true ->
    eo_interprets M (__eo_list_concat Term.or c1 c2) true := by
  intro hC1 hC2 hC1Bool hC2Bool hC2True
  change eo_interprets M
    (__eo_requires (__eo_is_list Term.or c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) true
  rw [orClause_is_list_true hC1, orClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact concat_rec_true_of_right_true M hM hC1 hC1Bool hC2Bool hC2True

private inductive SafeOrClause : Term -> Prop where
  | false : SafeOrClause (Term.Boolean false)
  | cons (x xs : Term) : x ≠ Term.Stuck -> SafeOrClause xs ->
      SafeOrClause (Term.Apply (Term.Apply Term.or x) xs)

private inductive GoodOrClause (M : SmtModel) : Term -> Prop where
  | false : GoodOrClause M (Term.Boolean false)
  | cons (x xs : Term) :
      x ≠ Term.Stuck ->
      (¬ RuleProofs.eo_has_bool_type x ∨ eo_interprets M x false) ->
      GoodOrClause M xs ->
      GoodOrClause M (Term.Apply (Term.Apply Term.or x) xs)

private theorem safe_orClause_of_good {M : SmtModel} {c : Term} :
    GoodOrClause M c -> SafeOrClause c := by
  intro hGood
  induction hGood with
  | false =>
      exact SafeOrClause.false
  | cons x xs hX _ hTail ih =>
      exact SafeOrClause.cons x xs hX ih

private theorem orClause_of_safe {c : Term} :
    SafeOrClause c -> OrClause c := by
  intro hSafe
  induction hSafe with
  | false =>
      exact OrClause.false
  | cons x xs _ hTail ih =>
      exact OrClause.cons x xs ih

private theorem safe_orClause_ne_stuck {c : Term} :
    SafeOrClause c -> c ≠ Term.Stuck := by
  intro hSafe
  exact orClause_ne_stuck (orClause_of_safe hSafe)

private theorem safe_orClause_cons {x xs : Term} :
    x ≠ Term.Stuck ->
    SafeOrClause xs ->
    SafeOrClause (Term.Apply (Term.Apply Term.or x) xs) := by
  intro hX hXs
  exact SafeOrClause.cons x xs hX hXs

private theorem good_orClause_cons {M : SmtModel} {x xs : Term} :
    x ≠ Term.Stuck ->
    (¬ RuleProofs.eo_has_bool_type x ∨ eo_interprets M x false) ->
    GoodOrClause M xs ->
    GoodOrClause M (Term.Apply (Term.Apply Term.or x) xs) := by
  intro hX hGood hXs
  exact GoodOrClause.cons x xs hX hGood hXs

private theorem good_orClause_false_of_bool
    (M : SmtModel) (hM : model_total_typed M) {c : Term} :
    GoodOrClause M c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c false := by
  intro hGood hCBool
  induction hGood with
  | false =>
      exact eo_interprets_false M
  | cons x xs hX hHead hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hXFalse : eo_interprets M x false := by
        cases hHead with
        | inl hNotBool =>
            exact False.elim (hNotBool hXBool)
        | inr hFalse =>
            exact hFalse
      have hXsFalse : eo_interprets M xs false := ih hXsBool
      exact eo_interprets_or_false_intro M hM x xs hXFalse hXsFalse

private theorem eo_list_translation_cons_inv {x xs : Term} :
    EoListAllHaveSmtTranslation (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) ->
    RuleProofs.eo_has_smt_translation x ∧ EoListAllHaveSmtTranslation xs := by
  intro h
  exact h

private theorem eo_list_translation_cases {xs : Term} :
    EoListAllHaveSmtTranslation xs ->
    xs = Term.__eo_List_nil ∨
      ∃ x ts, xs = Term.Apply (Term.Apply Term.__eo_List_cons x) ts := by
  intro hXs
  cases xs with
  | __eo_List_nil =>
      exact Or.inl rfl
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | __eo_List_cons =>
              exact Or.inr ⟨x, a, rfl⟩
          | _ =>
              cases hXs
      | _ =>
          cases hXs
  | _ =>
      cases hXs

private theorem erase_rec_preserves_safe {c e : Term} :
    SafeOrClause c ->
    e ≠ Term.Stuck ->
    SafeOrClause (__eo_list_erase_rec c e) := by
  intro hClause hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_rec] using SafeOrClause.false
  | cons x xs hX hXs ih =>
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        exact hXs
      · have hTail : SafeOrClause (__eo_list_erase_rec xs e) := ih hE
        have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
          safe_orClause_ne_stuck hTail
        rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
        exact SafeOrClause.cons x (__eo_list_erase_rec xs e) hX hTail

private theorem erase_rec_preserves_good
    (M : SmtModel) {c e : Term} :
    GoodOrClause M c ->
    e ≠ Term.Stuck ->
    GoodOrClause M (__eo_list_erase_rec c e) := by
  intro hClause hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_rec] using GoodOrClause.false
  | cons x xs hX hGood hXs ih =>
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        exact hXs
      · have hTail : GoodOrClause M (__eo_list_erase_rec xs e) := ih hE
        have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
          safe_orClause_ne_stuck (safe_orClause_of_good hTail)
        rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
        exact GoodOrClause.cons x (__eo_list_erase_rec xs e) hX hGood hTail

private theorem erase_rec_changed_implies_good
    (M : SmtModel) {c e : Term} :
    GoodOrClause M c ->
    e ≠ Term.Stuck ->
    __eo_list_erase_rec c e ≠ c ->
    (¬ RuleProofs.eo_has_bool_type e ∨ eo_interprets M e false) := by
  intro hClause hE hChanged
  induction hClause generalizing e with
  | false =>
      exfalso
      apply hChanged
      simp [__eo_list_erase_rec]
  | cons x xs hX hGood hXs ih =>
      by_cases hEq : x = e
      · simpa [hEq] using hGood
      · have hTail : GoodOrClause M (__eo_list_erase_rec xs e) :=
          erase_rec_preserves_good M hXs hE
        have hTailSafe : SafeOrClause (__eo_list_erase_rec xs e) :=
          safe_orClause_of_good hTail
        have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
          safe_orClause_ne_stuck hTailSafe
        have hTailChanged : __eo_list_erase_rec xs e ≠ xs := by
          intro hTailEq
          apply hChanged
          rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe, hTailEq]
        exact ih hE hTailChanged

private theorem diff_rec_preserves_orClause {c d : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    SafeOrClause d ->
    OrClause (__eo_list_diff_rec c d) := by
  intro hClause hCBool hD
  induction hClause generalizing d with
  | false =>
      cases hD with
      | false =>
          simpa [__eo_list_diff_rec] using OrClause.false
      | cons _ _ _ _ =>
          simpa [__eo_list_diff_rec] using OrClause.false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      let d' := __eo_list_erase_rec d x
      have hD' : SafeOrClause d' :=
        erase_rec_preserves_safe hD hX
      have hTail : OrClause (__eo_list_diff_rec xs d') := ih hXsBool hD'
      have hDNe : d ≠ Term.Stuck := safe_orClause_ne_stuck hD
      have hD'Ne : d' ≠ Term.Stuck := safe_orClause_ne_stuck hD'
      by_cases hEq : d' = d
      · have hEqTerm : __eo_eq d' d = Term.Boolean true :=
          eo_eq_eq_true_of_eq hEq hD'Ne hDNe
        have hTailNe : __eo_list_diff_rec xs d' ≠ Term.Stuck :=
          orClause_ne_stuck hTail
        have hStep :
            __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
              Term.Apply (Term.Apply Term.or x) (__eo_list_diff_rec xs d') := by
          simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if, hX, hTailNe]
        rw [hStep]
        exact OrClause.cons x (__eo_list_diff_rec xs d') hTail
      · have hEqTerm : __eo_eq d' d = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq hD'Ne hDNe
        have hTailNe : __eo_list_diff_rec xs d' ≠ Term.Stuck :=
          orClause_ne_stuck hTail
        have hStep :
            __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
              __eo_list_diff_rec xs d' := by
          simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if, hX, hTailNe]
        rw [hStep]
        exact hTail

private theorem diff_rec_preserves_bool_type {c d : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    SafeOrClause d ->
    RuleProofs.eo_has_bool_type (__eo_list_diff_rec c d) := by
  intro hClause hCBool hD
  induction hClause generalizing d with
  | false =>
      cases hD with
      | false =>
          simpa [__eo_list_diff_rec] using RuleProofs.eo_has_bool_type_false
      | cons _ _ _ _ =>
          simpa [__eo_list_diff_rec] using RuleProofs.eo_has_bool_type_false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      let d' := __eo_list_erase_rec d x
      have hD' : SafeOrClause d' :=
        erase_rec_preserves_safe hD hX
      have hTail : RuleProofs.eo_has_bool_type (__eo_list_diff_rec xs d') :=
        ih hXsBool hD'
      have hDNe : d ≠ Term.Stuck := safe_orClause_ne_stuck hD
      have hD'Ne : d' ≠ Term.Stuck := safe_orClause_ne_stuck hD'
      by_cases hEq : d' = d
      · have hEqTerm : __eo_eq d' d = Term.Boolean true :=
          eo_eq_eq_true_of_eq hEq hD'Ne hDNe
        have hTailNe : __eo_list_diff_rec xs d' ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTail
        have hStep :
            __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
              Term.Apply (Term.Apply Term.or x) (__eo_list_diff_rec xs d') := by
          simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if, hX, hTailNe]
        rw [hStep]
        exact RuleProofs.eo_has_bool_type_or_of_bool_args x (__eo_list_diff_rec xs d')
          hXBool hTail
      · have hEqTerm : __eo_eq d' d = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq hD'Ne hDNe
        have hTailNe : __eo_list_diff_rec xs d' ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTail
        have hStep :
            __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
              __eo_list_diff_rec xs d' := by
          simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if, hX, hTailNe]
        rw [hStep]
        exact hTail

private theorem diff_rec_true_of_good
    (M : SmtModel) (hM : model_total_typed M) {c d : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    GoodOrClause M d ->
    eo_interprets M (__eo_list_diff_rec c d) true := by
  intro hClause hCBool hCTrue hD
  induction hClause generalizing d with
  | false =>
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hCTrue)
        (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hOrTrue : eo_interprets M (Term.Apply (Term.Apply Term.or x) xs) true := by
        simpa using hCTrue
      let d' := __eo_list_erase_rec d x
      have hD' : GoodOrClause M d' :=
        erase_rec_preserves_good M hD hX
      have hD'Safe : SafeOrClause d' := safe_orClause_of_good hD'
      have hD'Ne : d' ≠ Term.Stuck := safe_orClause_ne_stuck hD'Safe
      have hDNe : d ≠ Term.Stuck := safe_orClause_ne_stuck (safe_orClause_of_good hD)
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_diff_rec xs d') :=
        diff_rec_preserves_bool_type hXs hXsBool hD'Safe
      by_cases hEq : d' = d
      · have hEqTerm : __eo_eq d' d = Term.Boolean true :=
          eo_eq_eq_true_of_eq hEq hD'Ne hDNe
        have hTailNe : __eo_list_diff_rec xs d' ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
        · have hStep :
              __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
                Term.Apply (Term.Apply Term.or x) (__eo_list_diff_rec xs d') := by
            simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if, hX, hTailNe]
          rw [hStep]
          exact RuleProofs.eo_interprets_or_left_intro M hM x (__eo_list_diff_rec xs d')
            hXTrue hTailBool
        · have hXsTrue : eo_interprets M xs true :=
            eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
          have hTailTrue : eo_interprets M (__eo_list_diff_rec xs d') true :=
            ih hXsBool hXsTrue hD'
          have hStep :
              __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
                Term.Apply (Term.Apply Term.or x) (__eo_list_diff_rec xs d') := by
            simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if, hX, hTailNe]
          rw [hStep]
          exact RuleProofs.eo_interprets_or_right_intro M hM x (__eo_list_diff_rec xs d')
            hXBool hTailTrue
      · have hEqTerm : __eo_eq d' d = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq hD'Ne hDNe
        have hTailNe : __eo_list_diff_rec xs d' ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        have hXGood : (¬ RuleProofs.eo_has_bool_type x ∨ eo_interprets M x false) :=
          erase_rec_changed_implies_good M hD hX hEq
        have hXFalse : eo_interprets M x false := by
          cases hXGood with
          | inl hNotBool =>
              exfalso
              exact hNotBool hXBool
          | inr hFalse =>
              exact hFalse
        have hXsTrue : eo_interprets M xs true :=
          eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
        have hTailTrue : eo_interprets M (__eo_list_diff_rec xs d') true :=
          ih hXsBool hXsTrue hD'
        have hStep :
            __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
              __eo_list_diff_rec xs d' := by
          simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if, hX, hTailNe]
        rw [hStep]
        exact hTailTrue

private theorem diff_preserves_orClause {c d : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    SafeOrClause d ->
    OrClause (__eo_list_diff Term.or c d) := by
  intro hC hCBool hD
  change OrClause
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or d) (Term.Boolean true)
        (__eo_list_diff_rec c d)))
  rw [orClause_is_list_true hC, orClause_is_list_true (orClause_of_safe hD)]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact diff_rec_preserves_orClause hC hCBool hD

private theorem diff_preserves_bool_type {c d : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    SafeOrClause d ->
    RuleProofs.eo_has_bool_type (__eo_list_diff Term.or c d) := by
  intro hC hCBool hD
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or d) (Term.Boolean true)
        (__eo_list_diff_rec c d)))
  rw [orClause_is_list_true hC, orClause_is_list_true (orClause_of_safe hD)]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact diff_rec_preserves_bool_type hC hCBool hD

private theorem diff_true_of_good
    (M : SmtModel) (hM : model_total_typed M) {c d : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    GoodOrClause M d ->
    eo_interprets M (__eo_list_diff Term.or c d) true := by
  intro hC hCBool hCTrue hD
  change eo_interprets M
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or d) (Term.Boolean true)
        (__eo_list_diff_rec c d))) true
  rw [orClause_is_list_true hC, orClause_is_list_true (orClause_of_safe (safe_orClause_of_good hD))]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact diff_rec_true_of_good M hM hC hCBool hCTrue hD

private theorem list_diff_nonstuck_input_orClause {a b : Term} :
    __eo_list_diff Term.or a b ≠ Term.Stuck ->
    OrClause a := by
  intro hDiff
  have hList : __eo_is_list Term.or a = Term.Boolean true := by
    cases hIs : __eo_is_list Term.or a with
    | Boolean t =>
        simp [__eo_list_diff, __eo_requires, hIs, native_ite, native_teq, native_not,
          SmtEval.native_not] at hDiff ⊢
        exact hDiff.1
    | _ =>
        simp [__eo_list_diff, __eo_requires, hIs, native_ite, native_teq, native_not,
          SmtEval.native_not] at hDiff
  exact orClause_of_is_list_true hList

private theorem concat_false_implies_left_false
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M (__eo_list_concat Term.or c1 c2) false ->
    eo_interprets M c1 false := by
  intro hC1 hC2 hC1Bool hC2Bool hConcatFalse
  rcases eo_interprets_bool_cases M hM c1 hC1Bool with hC1True | hC1False
  · have hConcatTrue : eo_interprets M (__eo_list_concat Term.or c1 c2) true :=
      concat_true_of_left_true M hM hC1 hC2 hC1Bool hC2Bool hC1True
    exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hConcatTrue) hConcatFalse)
  · exact hC1False

private theorem concat_false_implies_right_false
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M (__eo_list_concat Term.or c1 c2) false ->
    eo_interprets M c2 false := by
  intro hC1 hC2 hC1Bool hC2Bool hConcatFalse
  rcases eo_interprets_bool_cases M hM c2 hC2Bool with hC2True | hC2False
  · have hConcatTrue : eo_interprets M (__eo_list_concat Term.or c1 c2) true :=
      concat_true_of_right_true M hM hC1 hC2 hC1Bool hC2Bool hC2True
    exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hConcatTrue) hConcatFalse)
  · exact hC2False

private theorem not_ne_stuck {t : Term} :
    t ≠ Term.Stuck ->
    Term.Apply Term.not t ≠ Term.Stuck := by
  intro hT
  cases t <;> simp at hT ⊢

private theorem pair_eq_components {a b c d : Term} :
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) a) b =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) c) d ->
    a = c ∧ b = d := by
  intro hEq
  injection hEq with hPair hB
  have hA : a = c := by
    injection hPair with hA
  exact ⟨hA, hB⟩

private theorem pair_ne_stuck {a b : Term} :
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) a) b ≠ Term.Stuck := by
  simp

private theorem premiseAndFormulaList_andList
    (premises : List Term) :
    CnfSupport.AndList (premiseAndFormulaList premises) := by
  induction premises with
  | nil =>
      simpa [premiseAndFormulaList] using CnfSupport.AndList.true
  | cons p premises ih =>
      simpa [premiseAndFormulaList] using
        CnfSupport.AndList.cons p (premiseAndFormulaList premises) ih

private theorem premiseAndFormulaList_ne_stuck
    (premises : List Term) :
    premiseAndFormulaList premises ≠ Term.Stuck := by
  exact CnfSupport.andList_ne_stuck (premiseAndFormulaList_andList premises)

private theorem chain_m_resolve_final_true_of_false_good
    (M : SmtModel) (hM : model_total_typed M) {C1 C2 L rl : Term} :
    OrClause C1 ->
    OrClause C2 ->
    RuleProofs.eo_has_bool_type C1 ->
    eo_interprets M C1 true ->
    eo_interprets M C2 false ->
    GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    eo_interprets M
      (__chain_m_resolve_final C1
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))) true := by
  intro hC1 hC2 hC1Bool hC1True hC2False hPendingGood
  have hPendingSafe :
      SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
    safe_orClause_of_good hPendingGood
  have hC1Ne : C1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type C1 hC1Bool
  have hC2Bool : RuleProofs.eo_has_bool_type C2 :=
    RuleProofs.eo_has_bool_type_of_interprets_false M C2 hC2False
  by_cases hEq : C1 = L
  · cases hPendingGood with
    | cons x xs hX hHead hTail =>
        cases hHead with
        | inl hNotBool =>
            exact False.elim (hNotBool (by simpa [hEq] using hC1Bool))
        | inr hLFalse =>
            have hC1False : eo_interprets M C1 false := by
              simpa [hEq] using hLFalse
            exact False.elim
              ((RuleProofs.eo_interprets_true_not_false M C1 hC1True) hC1False)
  · have hLNe : L ≠ Term.Stuck := by
      cases hPendingSafe with
      | cons x xs hX hXs =>
          simpa using hX
    have hEqTerm : __eo_eq C1 L = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hC1Ne hLNe
    have hDiffClause :
        OrClause
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_orClause hC1 hC1Bool hPendingSafe
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_bool_type hC1 hC1Bool hPendingSafe
    have hDiffTrue :
        eo_interprets M
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) true :=
      diff_true_of_good M hM hC1 hC1Bool hC1True hPendingGood
    have hConcatTrue :
        eo_interprets M
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or C1
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            C2) true :=
      concat_true_of_left_true M hM hDiffClause hC2 hDiffBool hC2Bool hDiffTrue
    unfold __chain_m_resolve_final
    simp [hEqTerm, __eo_ite, native_ite, native_teq]
    exact hConcatTrue

private theorem chain_m_resolve_final_false_implies_residual_false
    (M : SmtModel) (hM : model_total_typed M) {C1 C2 L rl : Term} :
    OrClause C1 ->
    OrClause C2 ->
    RuleProofs.eo_has_bool_type C1 ->
    RuleProofs.eo_has_bool_type C2 ->
    SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    eo_interprets M
      (__chain_m_resolve_final C1
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))) false ->
    eo_interprets M C2 false := by
  intro hC1 hC2 hC1Bool hC2Bool hPendingSafe hFinalFalse
  have hC1Ne : C1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type C1 hC1Bool
  by_cases hEq : C1 = L
  · have hLNe : L ≠ Term.Stuck := by
      simpa [hEq] using hC1Ne
    have hEqTerm : __eo_eq C1 L = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hC1Ne hLNe
    unfold __chain_m_resolve_final at hFinalFalse
    simp [hEqTerm, __eo_ite, native_ite, native_teq] at hFinalFalse
    exact hFinalFalse
  · have hLNe : L ≠ Term.Stuck := by
      cases hPendingSafe with
      | cons x xs hX hXs =>
          simpa using hX
    have hEqTerm : __eo_eq C1 L = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hC1Ne hLNe
    have hDiffClause :
        OrClause
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_orClause hC1 hC1Bool hPendingSafe
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_bool_type hC1 hC1Bool hPendingSafe
    unfold __chain_m_resolve_final at hFinalFalse
    simp [hEqTerm, __eo_ite, native_ite, native_teq] at hFinalFalse
    exact concat_false_implies_right_false M hM hDiffClause hC2 hDiffBool hC2Bool hFinalFalse

private theorem not_has_bool_type_of_not_bool {t : Term} :
    ¬ RuleProofs.eo_has_bool_type t ->
    ¬ RuleProofs.eo_has_bool_type (Term.Apply Term.not t) := by
  intro hT hNotT
  exact hT (RuleProofs.eo_has_bool_type_not_arg t hNotT)

private theorem chain_m_resolve_rec_step_true_false_implies_good
    (M : SmtModel) (hM : model_total_typed M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    eo_interprets M Cr false ->
    GoodOrClause M rl ->
    OrClause Cc ->
    RuleProofs.eo_has_bool_type Cc ->
    eo_interprets M Cc true ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    eo_interprets M Cr' false ->
    GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) := by
  intro hCr hCrFalse hRlGood hCc hCcBool hCcTrue hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck :=
    safe_orClause_ne_stuck (safe_orClause_of_good hRlGood)
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hLBool : RuleProofs.eo_has_bool_type L
  · rcases eo_interprets_bool_cases M hM L hLBool with hLTrue | hLFalse
    · have hNotLFalse : eo_interprets M (Term.Apply Term.not L) false :=
        eo_interprets_not_false_of_true M L hLTrue
      have hDeleteGood :
          GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) :=
        GoodOrClause.cons (Term.Apply Term.not L) rl (not_ne_stuck hLNe) (Or.inr hNotLFalse) hRlGood
      have hCcNe : Cc ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
      by_cases hEq : Term.Apply Term.not L = Cc
      · have hCcFalse : eo_interprets M Cc false := by
          simpa [hEq] using hNotLFalse
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cc hCcTrue) hCcFalse)
      · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
        have hDeleteSafe : SafeOrClause
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) :=
          safe_orClause_of_good hDeleteGood
        have hDiffClause :
            OrClause
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
          diff_preserves_orClause hCc hCcBool hDeleteSafe
        have hDiffBool :
            RuleProofs.eo_has_bool_type
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
          diff_preserves_bool_type hCc hCcBool hDeleteSafe
        have hDiffTrue :
            eo_interprets M
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) true :=
          diff_true_of_good M hM hCc hCcBool hCcTrue hDeleteGood
        have hCrBool : RuleProofs.eo_has_bool_type Cr :=
          RuleProofs.eo_has_bool_type_of_interprets_false M Cr hCrFalse
        have hConcatTrue :
            eo_interprets M
              (__eo_list_concat Term.or
                (__eo_list_diff Term.or Cc
                  (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
                Cr) true :=
          concat_true_of_left_true M hM hDiffClause hCr hDiffBool hCrBool hDiffTrue
        have hConcatNe :
            __eo_list_concat Term.or
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
              Cr ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_interprets_true M _ hConcatTrue
        have hStep' := hStep
        unfold __chain_m_resolve_rec_step at hStep'
        simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hLNe, hRlNe, hConcatNe,
          hEqTerm] at hStep'
        have hCr'True : eo_interprets M Cr' true := by
          rw [← hStep']
          exact hConcatTrue
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cr' hCr'True) hCr'False)
    · exact GoodOrClause.cons L rl
        (RuleProofs.term_ne_stuck_of_interprets_false M L hLFalse)
        (Or.inr hLFalse) hRlGood
  · exact GoodOrClause.cons L rl hLNe (Or.inl hLBool) hRlGood

private theorem chain_m_resolve_rec_step_false_false_implies_good
    (M : SmtModel) (hM : model_total_typed M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    eo_interprets M Cr false ->
    GoodOrClause M rl ->
    OrClause Cc ->
    RuleProofs.eo_has_bool_type Cc ->
    eo_interprets M Cc true ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) ->
    eo_interprets M Cr' false ->
    GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) := by
  intro hCr hCrFalse hRlGood hCc hCcBool hCcTrue hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck :=
    safe_orClause_ne_stuck (safe_orClause_of_good hRlGood)
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hLBool : RuleProofs.eo_has_bool_type L
  · rcases eo_interprets_bool_cases M hM L hLBool with hLTrue | hLFalse
    · have hNotLFalse : eo_interprets M (Term.Apply Term.not L) false :=
        eo_interprets_not_false_of_true M L hLTrue
      exact GoodOrClause.cons (Term.Apply Term.not L) rl
        (not_ne_stuck (RuleProofs.term_ne_stuck_of_interprets_true M L hLTrue))
        (Or.inr hNotLFalse) hRlGood
    · have hDeleteGood :
          GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
        GoodOrClause.cons L rl
          (RuleProofs.term_ne_stuck_of_interprets_false M L hLFalse)
          (Or.inr hLFalse) hRlGood
      have hCcNe : Cc ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
      by_cases hEq : L = Cc
      · have hCcFalse : eo_interprets M Cc false := by
          simpa [hEq] using hLFalse
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cc hCcTrue) hCcFalse)
      · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq hLNe hCcNe
        have hDeleteSafe : SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
          safe_orClause_of_good hDeleteGood
        have hDiffClause :
            OrClause (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
          diff_preserves_orClause hCc hCcBool hDeleteSafe
        have hDiffBool :
            RuleProofs.eo_has_bool_type
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
          diff_preserves_bool_type hCc hCcBool hDeleteSafe
        have hDiffTrue :
            eo_interprets M
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) true :=
          diff_true_of_good M hM hCc hCcBool hCcTrue hDeleteGood
        have hCrBool : RuleProofs.eo_has_bool_type Cr :=
          RuleProofs.eo_has_bool_type_of_interprets_false M Cr hCrFalse
        have hConcatTrue :
            eo_interprets M
              (__eo_list_concat Term.or
                (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
                Cr) true :=
          concat_true_of_left_true M hM hDiffClause hCr hDiffBool hCrBool hDiffTrue
        have hConcatNe :
            __eo_list_concat Term.or
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
              Cr ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_interprets_true M _ hConcatTrue
        have hStep' := hStep
        unfold __chain_m_resolve_rec_step at hStep'
        simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hLNe, hRlNe, hConcatNe,
          hEqTerm] at hStep'
        have hCr'True : eo_interprets M Cr' true := by
          rw [← hStep']
          exact hConcatTrue
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cr' hCr'True) hCr'False)
  · exact GoodOrClause.cons (Term.Apply Term.not L) rl
      (not_ne_stuck hLNe)
      (Or.inl (not_has_bool_type_of_not_bool hLBool)) hRlGood

private theorem chain_m_resolve_rec_step_true_false_implies_prev_false
    (M : SmtModel) (hM : model_total_typed M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    GoodOrClause M rl ->
    OrClause Cc ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    eo_interprets M Cr' false ->
    eo_interprets M Cr false := by
  intro hCr hRlGood hCc hCcBool hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck :=
    safe_orClause_ne_stuck (safe_orClause_of_good hRlGood)
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  by_cases hEq : Term.Apply Term.not L = Cc
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq (not_ne_stuck hLNe) hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe] at hStep'
    rw [hStep']
    exact hCr'False
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) :=
      safe_orClause_cons (not_ne_stuck hLNe) (safe_orClause_of_good hRlGood)
    have hDiffClause :
        OrClause
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
      diff_preserves_orClause hCc hCcBool hDeleteSafe
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
      diff_preserves_bool_type hCc hCcBool hDeleteSafe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
        at hStep'
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcatNe]
      at hStep'
    have hConcatFalse :
        eo_interprets M
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
            Cr) false := by
      rw [hStep']
      exact hCr'False
    have hConcatBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
            Cr) :=
      RuleProofs.eo_has_bool_type_of_interprets_false M _ hConcatFalse
    have hCrBool : RuleProofs.eo_has_bool_type Cr :=
      concat_bool_type_implies_right hDiffClause hCr hConcatBool
    exact concat_false_implies_right_false M hM hDiffClause hCr hDiffBool hCrBool hConcatFalse

private theorem chain_m_resolve_rec_step_false_false_implies_prev_false
    (M : SmtModel) (hM : model_total_typed M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    GoodOrClause M rl ->
    OrClause Cc ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) ->
    eo_interprets M Cr' false ->
    eo_interprets M Cr false := by
  intro hCr hRlGood hCc hCcBool hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck :=
    safe_orClause_ne_stuck (safe_orClause_of_good hRlGood)
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  by_cases hEq : L = Cc
  · have hEqTerm : __eo_eq L Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hLNe hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe] at hStep'
    rw [hStep']
    exact hCr'False
  · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLNe hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
      safe_orClause_cons hLNe (safe_orClause_of_good hRlGood)
    have hDiffClause :
        OrClause (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_orClause hCc hCcBool hDeleteSafe
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_bool_type hCc hCcBool hDeleteSafe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
        at hStep'
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcatNe]
      at hStep'
    have hConcatFalse :
        eo_interprets M
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            Cr) false := by
      rw [hStep']
      exact hCr'False
    have hConcatBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            Cr) :=
      RuleProofs.eo_has_bool_type_of_interprets_false M _ hConcatFalse
    have hCrBool : RuleProofs.eo_has_bool_type Cr :=
      concat_bool_type_implies_right hDiffClause hCr hConcatBool
    exact concat_false_implies_right_false M hM hDiffClause hCr hDiffBool hCrBool hConcatFalse

private theorem chain_m_resolve_rec_step_true_false_implies_prev_false_of_safe
    (M : SmtModel) (hM : model_total_typed M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    RuleProofs.eo_has_bool_type Cr ->
    SafeOrClause rl ->
    OrClause Cc ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    eo_interprets M Cr' false ->
    eo_interprets M Cr false := by
  intro hCr hCrBool hRlSafe hCc hCcBool hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck := safe_orClause_ne_stuck hRlSafe
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  by_cases hEq : Term.Apply Term.not L = Cc
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq (not_ne_stuck hLNe) hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe] at hStep'
    rw [hStep']
    exact hCr'False
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) :=
      safe_orClause_cons (not_ne_stuck hLNe) hRlSafe
    have hDiffClause :
        OrClause
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
      diff_preserves_orClause hCc hCcBool hDeleteSafe
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
      diff_preserves_bool_type hCc hCcBool hDeleteSafe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
        at hStep'
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcatNe]
      at hStep'
    have hConcatFalse :
        eo_interprets M
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
            Cr) false := by
      rw [hStep']
      exact hCr'False
    exact concat_false_implies_right_false M hM hDiffClause hCr hDiffBool hCrBool hConcatFalse

private theorem chain_m_resolve_rec_step_false_false_implies_prev_false_of_safe
    (M : SmtModel) (hM : model_total_typed M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    RuleProofs.eo_has_bool_type Cr ->
    SafeOrClause rl ->
    OrClause Cc ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) ->
    eo_interprets M Cr' false ->
    eo_interprets M Cr false := by
  intro hCr hCrBool hRlSafe hCc hCcBool hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck := safe_orClause_ne_stuck hRlSafe
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  by_cases hEq : L = Cc
  · have hEqTerm : __eo_eq L Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hLNe hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe] at hStep'
    rw [hStep']
    exact hCr'False
  · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLNe hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
      safe_orClause_cons hLNe hRlSafe
    have hDiffClause :
        OrClause (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_orClause hCc hCcBool hDeleteSafe
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_bool_type hCc hCcBool hDeleteSafe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
        at hStep'
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcatNe]
      at hStep'
    have hConcatFalse :
        eo_interprets M
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            Cr) false := by
      rw [hStep']
      exact hCr'False
    exact concat_false_implies_right_false M hM hDiffClause hCr hDiffBool hCrBool hConcatFalse

private theorem list_concat_nonstuck_left_orClause {a b : Term} :
    __eo_list_concat Term.or a b ≠ Term.Stuck ->
    OrClause a := by
  intro hConcat
  have hList : __eo_is_list Term.or a = Term.Boolean true := by
    cases hIs : __eo_is_list Term.or a with
    | Boolean t =>
        simp [__eo_list_concat, __eo_requires, hIs, native_ite, native_teq, native_not,
          SmtEval.native_not] at hConcat ⊢
        exact hConcat.1
    | _ =>
        simp [__eo_list_concat, __eo_requires, hIs, native_ite, native_teq, native_not,
          SmtEval.native_not] at hConcat
  exact orClause_of_is_list_true hList

private theorem list_concat_nonstuck_right_orClause {a b : Term} :
    __eo_list_concat Term.or a b ≠ Term.Stuck ->
    OrClause b := by
  intro hConcat
  have hList : __eo_is_list Term.or b = Term.Boolean true := by
    cases hIsA : __eo_is_list Term.or a with
    | Boolean ta =>
        have hTa : ta = true := by
          simp [__eo_list_concat, __eo_requires, hIsA, native_ite, native_teq, native_not,
            SmtEval.native_not] at hConcat
          exact hConcat.1
        cases hIsB : __eo_is_list Term.or b with
        | Boolean tb =>
            simp [__eo_list_concat, __eo_requires, hIsA, hIsB, native_ite, native_teq,
              native_not, SmtEval.native_not] at hConcat ⊢
            exact hConcat.2.1
        | _ =>
            simp [__eo_list_concat, __eo_requires, hIsA, hIsB, native_ite, native_teq,
              native_not, SmtEval.native_not] at hConcat
    | _ =>
        simp [__eo_list_concat, __eo_requires, hIsA, native_ite, native_teq, native_not,
          SmtEval.native_not] at hConcat
  exact orClause_of_is_list_true hList

private theorem chain_m_resolve_rec_step_true_false_implies_prev_false_of_safe_bool
    (M : SmtModel) (hM : model_total_typed M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    RuleProofs.eo_has_bool_type Cr ->
    SafeOrClause rl ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    eo_interprets M Cr' false ->
    eo_interprets M Cr false := by
  intro hCr hCrBool hRlSafe hCcBool hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck := safe_orClause_ne_stuck hRlSafe
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  by_cases hEq : Term.Apply Term.not L = Cc
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq (not_ne_stuck hLNe) hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe] at hStep'
    rw [hStep']
    exact hCr'False
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) :=
      safe_orClause_cons (not_ne_stuck hLNe) hRlSafe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
        at hStep'
    have hDiffClause :
        OrClause
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
      list_concat_nonstuck_left_orClause hConcatNe
    have hCcClause : OrClause Cc :=
      list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
      diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcatNe]
      at hStep'
    have hConcatFalse :
        eo_interprets M
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
            Cr) false := by
      rw [hStep']
      exact hCr'False
    exact concat_false_implies_right_false M hM hDiffClause hCr hDiffBool hCrBool hConcatFalse

private theorem chain_m_resolve_rec_step_false_false_implies_prev_false_of_safe_bool
    (M : SmtModel) (hM : model_total_typed M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    RuleProofs.eo_has_bool_type Cr ->
    SafeOrClause rl ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) ->
    eo_interprets M Cr' false ->
    eo_interprets M Cr false := by
  intro hCr hCrBool hRlSafe hCcBool hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck := safe_orClause_ne_stuck hRlSafe
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  by_cases hEq : L = Cc
  · have hEqTerm : __eo_eq L Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hLNe hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe] at hStep'
    rw [hStep']
    exact hCr'False
  · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLNe hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
      safe_orClause_cons hLNe hRlSafe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
        at hStep'
    have hDiffClause :
        OrClause (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      list_concat_nonstuck_left_orClause hConcatNe
    have hCcClause : OrClause Cc :=
      list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcatNe]
      at hStep'
    have hConcatFalse :
        eo_interprets M
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            Cr) false := by
      rw [hStep']
      exact hCr'False
    exact concat_false_implies_right_false M hM hDiffClause hCr hDiffBool hCrBool hConcatFalse

private theorem chain_m_resolve_rec_step_true_false_implies_good_of_bool
    (M : SmtModel) (hM : model_total_typed M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    eo_interprets M Cr false ->
    GoodOrClause M rl ->
    RuleProofs.eo_has_bool_type Cc ->
    eo_interprets M Cc true ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    eo_interprets M Cr' false ->
    GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) := by
  intro hCr hCrFalse hRlGood hCcBool hCcTrue hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck :=
    safe_orClause_ne_stuck (safe_orClause_of_good hRlGood)
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hLBool : RuleProofs.eo_has_bool_type L
  · rcases eo_interprets_bool_cases M hM L hLBool with hLTrue | hLFalse
    · have hNotLFalse : eo_interprets M (Term.Apply Term.not L) false :=
        eo_interprets_not_false_of_true M L hLTrue
      have hDeleteGood :
          GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) :=
        GoodOrClause.cons (Term.Apply Term.not L) rl (not_ne_stuck hLNe) (Or.inr hNotLFalse) hRlGood
      have hCcNe : Cc ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
      by_cases hEq : Term.Apply Term.not L = Cc
      · have hCcFalse : eo_interprets M Cc false := by
          simpa [hEq] using hNotLFalse
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cc hCcTrue) hCcFalse)
      · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
        have hConcatNe :
            __eo_list_concat Term.or
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
              Cr ≠ Term.Stuck := by
          intro hConcat
          have hStep' := hStep
          unfold __chain_m_resolve_rec_step at hStep'
          simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
            at hStep'
        have hDiffClause :
            OrClause
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
          list_concat_nonstuck_left_orClause hConcatNe
        have hCcClause : OrClause Cc :=
          list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
        have hDeleteSafe : SafeOrClause
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) :=
          safe_orClause_of_good hDeleteGood
        have hDiffBool :
            RuleProofs.eo_has_bool_type
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
          diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
        have hDiffTrue :
            eo_interprets M
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) true :=
          diff_true_of_good M hM hCcClause hCcBool hCcTrue hDeleteGood
        have hCrBool : RuleProofs.eo_has_bool_type Cr :=
          RuleProofs.eo_has_bool_type_of_interprets_false M Cr hCrFalse
        have hConcatTrue :
            eo_interprets M
              (__eo_list_concat Term.or
                (__eo_list_diff Term.or Cc
                  (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
                Cr) true :=
          concat_true_of_left_true M hM hDiffClause hCr hDiffBool hCrBool hDiffTrue
        have hStep' := hStep
        unfold __chain_m_resolve_rec_step at hStep'
        simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hLNe, hRlNe, hConcatNe,
          hEqTerm] at hStep'
        have hCr'True : eo_interprets M Cr' true := by
          rw [← hStep']
          exact hConcatTrue
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cr' hCr'True) hCr'False)
    · exact GoodOrClause.cons L rl
        (RuleProofs.term_ne_stuck_of_interprets_false M L hLFalse)
        (Or.inr hLFalse) hRlGood
  · exact GoodOrClause.cons L rl hLNe (Or.inl hLBool) hRlGood

private theorem chain_m_resolve_rec_step_false_false_implies_good_of_bool
    (M : SmtModel) (hM : model_total_typed M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    eo_interprets M Cr false ->
    GoodOrClause M rl ->
    RuleProofs.eo_has_bool_type Cc ->
    eo_interprets M Cc true ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) ->
    eo_interprets M Cr' false ->
    GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) := by
  intro hCr hCrFalse hRlGood hCcBool hCcTrue hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck :=
    safe_orClause_ne_stuck (safe_orClause_of_good hRlGood)
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hLBool : RuleProofs.eo_has_bool_type L
  · rcases eo_interprets_bool_cases M hM L hLBool with hLTrue | hLFalse
    · have hNotLFalse : eo_interprets M (Term.Apply Term.not L) false :=
        eo_interprets_not_false_of_true M L hLTrue
      exact GoodOrClause.cons (Term.Apply Term.not L) rl
        (not_ne_stuck (RuleProofs.term_ne_stuck_of_interprets_true M L hLTrue))
        (Or.inr hNotLFalse) hRlGood
    · have hDeleteGood :
          GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
        GoodOrClause.cons L rl
          (RuleProofs.term_ne_stuck_of_interprets_false M L hLFalse)
          (Or.inr hLFalse) hRlGood
      have hCcNe : Cc ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
      by_cases hEq : L = Cc
      · have hCcFalse : eo_interprets M Cc false := by
          simpa [hEq] using hLFalse
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cc hCcTrue) hCcFalse)
      · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq hLNe hCcNe
        have hConcatNe :
            __eo_list_concat Term.or
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
              Cr ≠ Term.Stuck := by
          intro hConcat
          have hStep' := hStep
          unfold __chain_m_resolve_rec_step at hStep'
          simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
            at hStep'
        have hDiffClause :
            OrClause (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
          list_concat_nonstuck_left_orClause hConcatNe
        have hCcClause : OrClause Cc :=
          list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
        have hDeleteSafe : SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
          safe_orClause_of_good hDeleteGood
        have hDiffBool :
            RuleProofs.eo_has_bool_type
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
          diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
        have hDiffTrue :
            eo_interprets M
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) true :=
          diff_true_of_good M hM hCcClause hCcBool hCcTrue hDeleteGood
        have hCrBool : RuleProofs.eo_has_bool_type Cr :=
          RuleProofs.eo_has_bool_type_of_interprets_false M Cr hCrFalse
        have hConcatTrue :
            eo_interprets M
              (__eo_list_concat Term.or
                (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
                Cr) true :=
          concat_true_of_left_true M hM hDiffClause hCr hDiffBool hCrBool hDiffTrue
        have hStep' := hStep
        unfold __chain_m_resolve_rec_step at hStep'
        simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hLNe, hRlNe, hConcatNe,
          hEqTerm] at hStep'
        have hCr'True : eo_interprets M Cr' true := by
          rw [← hStep']
          exact hConcatTrue
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cr' hCr'True) hCr'False)
  · exact GoodOrClause.cons (Term.Apply Term.not L) rl
      (not_ne_stuck hLNe)
      (Or.inl (not_has_bool_type_of_not_bool hLBool)) hRlGood

private theorem ite_eq_stuck_of_ne_true_false (c t e : Term) :
    c ≠ Term.Boolean true ->
    c ≠ Term.Boolean false ->
    __eo_ite c t e = Term.Stuck := by
  intro hTrue hFalse
  cases c <;> simp [__eo_ite, native_ite, native_teq, hTrue, hFalse]

private theorem chain_m_resolve_rec_step_stuck_of_pol_ne_true_false
    {r Cc pol L : Term} :
    Cc ≠ Term.Stuck ->
    L ≠ Term.Stuck ->
    pol ≠ Term.Boolean true ->
    pol ≠ Term.Boolean false ->
    __chain_m_resolve_rec_step r Cc pol L = Term.Stuck := by
  intro hCc hL hPolTrue hPolFalse
  cases r with
  | Stuck =>
      simp [__chain_m_resolve_rec_step]
  | Boolean _ =>
      simp [__chain_m_resolve_rec_step, hCc, hL]
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op <;> unfold __chain_m_resolve_rec_step <;> simp [__eo_mk_apply,
                __eo_ite, native_ite, native_teq, hCc, hL, hPolTrue, hPolFalse]
          | _ =>
              simp [__chain_m_resolve_rec_step, hCc, hL]
      | _ =>
          simp [__chain_m_resolve_rec_step, hCc, hL]
  | _ =>
      simp [__chain_m_resolve_rec_step, hCc, hL]

private theorem chain_m_resolve_rec_step_true_pair_input
    {r Cc Cr' rl' L : Term} :
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step r Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr') rl' ->
    ∃ Cr rl, r = Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
  intro hCcBool hLTrans hStep
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  cases r with
  | Stuck =>
      simp [__chain_m_resolve_rec_step] at hStep
  | Boolean b =>
      simp [__chain_m_resolve_rec_step, hCcNe, hLNe] at hStep
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_pair =>
                  exact ⟨x, a, rfl⟩
              | _ =>
                  simp [__chain_m_resolve_rec_step, hCcNe, hLNe] at hStep
          | _ =>
              simp [__chain_m_resolve_rec_step, hCcNe, hLNe] at hStep
      | _ =>
          simp [__chain_m_resolve_rec_step, hCcNe, hLNe] at hStep
  | _ =>
      simp [__chain_m_resolve_rec_step, hCcNe, hLNe] at hStep

private theorem chain_m_resolve_rec_step_false_pair_input
    {r Cc Cr' rl' L : Term} :
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step r Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr') rl' ->
    ∃ Cr rl, r = Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
  intro hCcBool hLTrans hStep
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  cases r with
  | Stuck =>
      simp [__chain_m_resolve_rec_step] at hStep
  | Boolean b =>
      simp [__chain_m_resolve_rec_step, hCcNe, hLNe] at hStep
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_pair =>
                  exact ⟨x, a, rfl⟩
              | _ =>
                  simp [__chain_m_resolve_rec_step, hCcNe, hLNe] at hStep
          | _ =>
              simp [__chain_m_resolve_rec_step, hCcNe, hLNe] at hStep
      | _ =>
          simp [__chain_m_resolve_rec_step, hCcNe, hLNe] at hStep
  | _ =>
      simp [__chain_m_resolve_rec_step, hCcNe, hLNe] at hStep

private theorem chain_m_resolve_rec_step_true_pair_pending
    {Cr rl Cc Cr' rl' L : Term} :
    SafeOrClause rl ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr') rl' ->
    rl' = Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl := by
  intro hRlSafe hCcBool hLTrans hStep
  have hRlNe : rl ≠ Term.Stuck := safe_orClause_ne_stuck hRlSafe
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hEq : Term.Apply Term.not L = Cc
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq (not_ne_stuck hLNe) hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe] at hStep'
    exact hStep'.2.symm
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
        at hStep'
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcatNe]
      at hStep'
    exact hStep'.2.symm

private theorem chain_m_resolve_rec_step_false_pair_pending
    {Cr rl Cc Cr' rl' L : Term} :
    SafeOrClause rl ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr') rl' ->
    rl' = Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl := by
  intro hRlSafe hCcBool hLTrans hStep
  have hRlNe : rl ≠ Term.Stuck := safe_orClause_ne_stuck hRlSafe
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hEq : L = Cc
  · have hEqTerm : __eo_eq L Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hLNe hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe] at hStep'
    exact hStep'.2.symm
  · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLNe hCcNe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
        at hStep'
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcatNe]
      at hStep'
    exact hStep'.2.symm

private theorem chain_m_resolve_rec_step_true_pair_residual
    {Cr0 rl0 Cc Cr rl L : Term} :
    OrClause Cr0 ->
    RuleProofs.eo_has_bool_type Cr0 ->
    SafeOrClause rl0 ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
    OrClause Cr ∧ RuleProofs.eo_has_bool_type Cr := by
  intro hCr0 hCr0Bool hRl0Safe hCcBool hLTrans hStep
  have hRlNe : rl0 ≠ Term.Stuck := safe_orClause_ne_stuck hRl0Safe
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hEq : Term.Apply Term.not L = Cc
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq (not_ne_stuck hLNe) hCcNe
    have hStep' :
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0) =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
      simpa [__chain_m_resolve_rec_step, __eo_mk_apply, __eo_ite, native_ite, native_teq,
        hEqTerm, hLNe, hRlNe] using hStep
    have hComps := pair_eq_components hStep'
    exact ⟨by simpa [hComps.1] using hCr0, by simpa [hComps.1] using hCr0Bool⟩
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0) :=
      safe_orClause_cons (not_ne_stuck hLNe) hRl0Safe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0))
          Cr0 ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
        at hStep'
    have hDiffClause :
        OrClause
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0)) :=
      list_concat_nonstuck_left_orClause hConcatNe
    have hCcClause : OrClause Cc :=
      list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0)) :=
      diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
    have hResidualClause :
        OrClause
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0))
            Cr0) :=
      concat_preserves_orClause hDiffClause hCr0
    have hResidualBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0))
            Cr0) :=
      concat_preserves_bool_type hDiffClause hCr0 hDiffBool hCr0Bool
    have hStep' :
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_pair)
            (__eo_list_concat Term.or
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0))
              Cr0))
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0) =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
      simpa [__chain_m_resolve_rec_step, __eo_mk_apply, __eo_ite, native_ite, native_teq,
        hEqTerm, hLNe, hRlNe, hConcatNe] using hStep
    have hComps := pair_eq_components hStep'
    exact ⟨by simpa [hComps.1] using hResidualClause, by simpa [hComps.1] using hResidualBool⟩

private theorem chain_m_resolve_rec_step_false_pair_residual
    {Cr0 rl0 Cc Cr rl L : Term} :
    OrClause Cr0 ->
    RuleProofs.eo_has_bool_type Cr0 ->
    SafeOrClause rl0 ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
    OrClause Cr ∧ RuleProofs.eo_has_bool_type Cr := by
  intro hCr0 hCr0Bool hRl0Safe hCcBool hLTrans hStep
  have hRlNe : rl0 ≠ Term.Stuck := safe_orClause_ne_stuck hRl0Safe
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hEq : L = Cc
  · have hEqTerm : __eo_eq L Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hLNe hCcNe
    have hStep' :
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0) =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
      simpa [__chain_m_resolve_rec_step, __eo_mk_apply, __eo_ite, native_ite, native_teq,
        hEqTerm, hLNe, hRlNe] using hStep
    have hComps := pair_eq_components hStep'
    exact ⟨by simpa [hComps.1] using hCr0, by simpa [hComps.1] using hCr0Bool⟩
  · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLNe hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0) :=
      safe_orClause_cons hLNe hRl0Safe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0))
          Cr0 ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hLNe, hRlNe, hConcat]
        at hStep'
    have hDiffClause :
        OrClause (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0)) :=
      list_concat_nonstuck_left_orClause hConcatNe
    have hCcClause : OrClause Cc :=
      list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0)) :=
      diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
    have hResidualClause :
        OrClause
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0))
            Cr0) :=
      concat_preserves_orClause hDiffClause hCr0
    have hResidualBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0))
            Cr0) :=
      concat_preserves_bool_type hDiffClause hCr0 hDiffBool hCr0Bool
    have hStep' :
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_pair)
            (__eo_list_concat Term.or
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0))
              Cr0))
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0) =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
      simpa [__chain_m_resolve_rec_step, __eo_mk_apply, __eo_ite, native_ite, native_teq,
        hEqTerm, hLNe, hRlNe, hConcatNe] using hStep
    have hComps := pair_eq_components hStep'
    exact ⟨by simpa [hComps.1] using hResidualClause, by simpa [hComps.1] using hResidualBool⟩

private theorem chain_m_resolve_rec_step_true_pair_safe
    {Cr0 rl0 Cc Cr rl L : Term} :
    SafeOrClause rl0 ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
    SafeOrClause rl := by
  intro hRl0Safe hCcBool hLTrans hStep
  have hRlEq :
      rl = Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0 :=
    chain_m_resolve_rec_step_true_pair_pending hRl0Safe hCcBool hLTrans hStep
  rw [hRlEq]
  exact safe_orClause_cons
    (RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans) hRl0Safe

private theorem chain_m_resolve_rec_step_false_pair_safe
    {Cr0 rl0 Cc Cr rl L : Term} :
    SafeOrClause rl0 ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
    SafeOrClause rl := by
  intro hRl0Safe hCcBool hLTrans hStep
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  have hRlEq :
      rl = Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0 :=
    chain_m_resolve_rec_step_false_pair_pending hRl0Safe hCcBool hLTrans hStep
  rw [hRlEq]
  exact safe_orClause_cons (not_ne_stuck hLNe) hRl0Safe

private theorem chain_m_resolve_rec_pair_false_implies_good
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ premises pols lits Cr rl,
      AllHaveBoolType premises ->
      AllInterpretedTrue M premises ->
      EoListAllHaveSmtTranslation pols ->
      EoListAllHaveSmtTranslation lits ->
      __chain_m_resolve_rec (premiseAndFormulaList premises) pols lits =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
      OrClause Cr ∧
      RuleProofs.eo_has_bool_type Cr ∧
      SafeOrClause rl ∧
      (eo_interprets M Cr false -> GoodOrClause M rl) := by
  intro premises
  induction premises with
  | nil =>
      intro pols lits Cr rl _ _ hPols hLits hRec
      rcases eo_list_translation_cases hPols with hPolsNil | ⟨pol, pols', hPolsCons⟩
      · subst hPolsNil
        rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsCons⟩
        · subst hLitsNil
          have hBase' := hRec
          simp [premiseAndFormulaList] at hBase'
          have hBase :
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) (Term.Boolean false))
                (Term.Boolean false) =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa [__chain_m_resolve_rec] using hBase'
          have hComps := pair_eq_components hBase
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [hComps.1.symm] using (OrClause.false : OrClause (Term.Boolean false))
          · simpa [hComps.1.symm] using RuleProofs.eo_has_bool_type_false
          · simpa [hComps.2.symm] using (SafeOrClause.false : SafeOrClause (Term.Boolean false))
          · intro _
            simpa [hComps.2.symm] using (GoodOrClause.false : GoodOrClause M (Term.Boolean false))
        · subst hLitsCons
          have hRec' := hRec
          simp [premiseAndFormulaList] at hRec'
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa [__chain_m_resolve_rec] using hRec'
          exact False.elim (pair_ne_stuck hStuck.symm)
      · subst hPolsCons
        rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsCons⟩
        · subst hLitsNil
          have hRec' := hRec
          simp [premiseAndFormulaList] at hRec'
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa [__chain_m_resolve_rec] using hRec'
          exact False.elim (pair_ne_stuck hStuck.symm)
        · subst hLitsCons
          have hRec' := hRec
          simp [premiseAndFormulaList] at hRec'
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa [__chain_m_resolve_rec] using hRec'
          exact False.elim (pair_ne_stuck hStuck.symm)
  | cons Cc premises ih =>
      intro pols lits Cr rl hPremBool hPremTrue hPols hLits hRec
      have hCcBool : RuleProofs.eo_has_bool_type Cc := hPremBool Cc (by simp)
      have hCcTrue : eo_interprets M Cc true := hPremTrue Cc (by simp)
      have hPremisesBool : AllHaveBoolType premises := by
        intro t ht
        exact hPremBool t (by simp [ht])
      have hPremisesTrue : AllInterpretedTrue M premises := by
        intro t ht
        exact hPremTrue t (by simp [ht])
      rcases eo_list_translation_cases hPols with hPolsNil | ⟨pol, pols', hPolsCons⟩
      · subst hPolsNil
        have hRec' := hRec
        simp [premiseAndFormulaList] at hRec'
        have hStuck :
            Term.Stuck =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
          simpa [__chain_m_resolve_rec] using hRec'
        exact False.elim (pair_ne_stuck hStuck.symm)
      · subst hPolsCons
        rcases eo_list_translation_cons_inv hPols with ⟨hPolTrans, hPols'⟩
        rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsCons⟩
        · subst hLitsNil
          have hRec' := hRec
          simp [premiseAndFormulaList] at hRec'
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa [__chain_m_resolve_rec] using hRec'
          exact False.elim (pair_ne_stuck hStuck.symm)
        · subst hLitsCons
          rcases eo_list_translation_cons_inv hLits with ⟨hLTrans, hLits'⟩
          have hStep0 := hRec
          simp [premiseAndFormulaList] at hStep0
          have hStep :
              __chain_m_resolve_rec_step
                (__chain_m_resolve_rec (premiseAndFormulaList premises) pols' lits')
                Cc pol L =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa [__chain_m_resolve_rec] using hStep0
          by_cases hPolTrue : pol = Term.Boolean true
          · subst hPolTrue
            rcases chain_m_resolve_rec_step_true_pair_input hCcBool hLTrans hStep with
              ⟨Cr0, rl0, hTailEq⟩
            rcases ih pols' lits' Cr0 rl0 hPremisesBool hPremisesTrue hPols' hLits' hTailEq with
              ⟨hCr0Clause, hCr0Bool, hRl0Safe, hTailGood⟩
            have hStepPair :
                __chain_m_resolve_rec_step
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
                  Cc (Term.Boolean true) L =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
              simpa [hTailEq] using hStep
            have hResidual :=
              chain_m_resolve_rec_step_true_pair_residual
                hCr0Clause hCr0Bool hRl0Safe hCcBool hLTrans hStepPair
            have hRlSafe :=
              chain_m_resolve_rec_step_true_pair_safe hRl0Safe hCcBool hLTrans hStepPair
            have hRlEq :
                rl = Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0 :=
              chain_m_resolve_rec_step_true_pair_pending hRl0Safe hCcBool hLTrans hStepPair
            refine ⟨hResidual.1, hResidual.2, hRlSafe, ?_⟩
            intro hCrFalse
            have hStep' :
                __chain_m_resolve_rec_step
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
                  Cc (Term.Boolean true) L =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0) := by
              simpa [hRlEq] using hStepPair
            have hCr0False :
                eo_interprets M Cr0 false :=
              chain_m_resolve_rec_step_true_false_implies_prev_false_of_safe_bool M hM
                hCr0Clause hCr0Bool hRl0Safe hCcBool hLTrans hStep' hCrFalse
            have hRl0Good : GoodOrClause M rl0 := hTailGood hCr0False
            have hRlGood :
                GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0) :=
              chain_m_resolve_rec_step_true_false_implies_good_of_bool M hM
                hCr0Clause hCr0False hRl0Good hCcBool hCcTrue hLTrans hStep' hCrFalse
            simpa [hRlEq] using hRlGood
          · by_cases hPolFalse : pol = Term.Boolean false
            · subst hPolFalse
              rcases chain_m_resolve_rec_step_false_pair_input hCcBool hLTrans hStep with
                ⟨Cr0, rl0, hTailEq⟩
              rcases ih pols' lits' Cr0 rl0 hPremisesBool hPremisesTrue hPols' hLits' hTailEq with
                ⟨hCr0Clause, hCr0Bool, hRl0Safe, hTailGood⟩
              have hStepPair :
                  __chain_m_resolve_rec_step
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
                    Cc (Term.Boolean false) L =
                  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
                simpa [hTailEq] using hStep
              have hResidual :=
                chain_m_resolve_rec_step_false_pair_residual
                  hCr0Clause hCr0Bool hRl0Safe hCcBool hLTrans hStepPair
              have hRlSafe :=
                chain_m_resolve_rec_step_false_pair_safe hRl0Safe hCcBool hLTrans hStepPair
              have hRlEq :
                  rl = Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0 :=
                chain_m_resolve_rec_step_false_pair_pending hRl0Safe hCcBool hLTrans hStepPair
              refine ⟨hResidual.1, hResidual.2, hRlSafe, ?_⟩
              intro hCrFalse
              have hStep' :
                  __chain_m_resolve_rec_step
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
                    Cc (Term.Boolean false) L =
                  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0) := by
                simpa [hRlEq] using hStepPair
              have hCr0False :
                  eo_interprets M Cr0 false :=
                chain_m_resolve_rec_step_false_false_implies_prev_false_of_safe_bool M hM
                  hCr0Clause hCr0Bool hRl0Safe hCcBool hLTrans hStep' hCrFalse
              have hRl0Good : GoodOrClause M rl0 := hTailGood hCr0False
              have hRlGood :
                  GoodOrClause M
                    (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0) :=
                chain_m_resolve_rec_step_false_false_implies_good_of_bool M hM
                  hCr0Clause hCr0False hRl0Good hCcBool hCcTrue hLTrans hStep' hCrFalse
              simpa [hRlEq] using hRlGood
            · have hCcNe : Cc ≠ Term.Stuck :=
                RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
              have hLNe : L ≠ Term.Stuck :=
                RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
              have hStuck :
                  __chain_m_resolve_rec_step
                    (__chain_m_resolve_rec (premiseAndFormulaList premises) pols' lits')
                    Cc pol L = Term.Stuck :=
                chain_m_resolve_rec_step_stuck_of_pol_ne_true_false
                  hCcNe hLNe hPolTrue hPolFalse
              rw [hStuck] at hStep
              exact False.elim (pair_ne_stuck hStep.symm)

private theorem from_clause_preserves_bool_type {c : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type (__from_clause c) := by
  intro hClause hCBool
  induction hClause with
  | false =>
      simpa [__from_clause] using RuleProofs.eo_has_bool_type_false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hXsNe : xs ≠ Term.Stuck := orClause_ne_stuck hXs
      by_cases hNil : xs = Term.Boolean false
      · have hEqTerm : __eo_eq xs (Term.Boolean false) = Term.Boolean true :=
          eo_eq_eq_true_of_eq hNil hXsNe (by simp)
        rw [show __from_clause (Term.Apply (Term.Apply Term.or x) xs) =
              __eo_ite (__eo_eq xs (Term.Boolean false)) x
                (Term.Apply (Term.Apply Term.or x) xs) by
              simp [__from_clause]]
        simp [hEqTerm, __eo_ite, native_ite, native_teq]
        exact hXBool
      · have hEqTerm : __eo_eq xs (Term.Boolean false) = Term.Boolean false :=
          eo_eq_eq_false_of_ne hNil hXsNe (by simp)
        rw [show __from_clause (Term.Apply (Term.Apply Term.or x) xs) =
              __eo_ite (__eo_eq xs (Term.Boolean false)) x
                (Term.Apply (Term.Apply Term.or x) xs) by
              simp [__from_clause]]
        simp [hEqTerm, __eo_ite, native_ite, native_teq]
        exact hCBool

private theorem from_clause_true
    (M : SmtModel) (hM : model_total_typed M) {c : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    eo_interprets M (__from_clause c) true := by
  intro hClause hCBool hCTrue
  induction hClause with
  | false =>
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hCTrue)
        (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hXsNe : xs ≠ Term.Stuck := orClause_ne_stuck hXs
      have hOrTrue : eo_interprets M (Term.Apply (Term.Apply Term.or x) xs) true := by
        simpa using hCTrue
      by_cases hNil : xs = Term.Boolean false
      · have hEqTerm : __eo_eq xs (Term.Boolean false) = Term.Boolean true :=
          eo_eq_eq_true_of_eq hNil hXsNe (by simp)
        have hXsFalse : eo_interprets M xs false := by
          simpa [hNil] using eo_interprets_false M
        have hXTrue : eo_interprets M x true :=
          eo_interprets_or_left_of_right_false M hM x xs hXsFalse hOrTrue
        rw [show __from_clause (Term.Apply (Term.Apply Term.or x) xs) =
              __eo_ite (__eo_eq xs (Term.Boolean false)) x
                (Term.Apply (Term.Apply Term.or x) xs) by
              simp [__from_clause]]
        simp [hEqTerm, __eo_ite, native_ite, native_teq]
        exact hXTrue
      · have hEqTerm : __eo_eq xs (Term.Boolean false) = Term.Boolean false :=
          eo_eq_eq_false_of_ne hNil hXsNe (by simp)
        rw [show __from_clause (Term.Apply (Term.Apply Term.or x) xs) =
              __eo_ite (__eo_eq xs (Term.Boolean false)) x
                (Term.Apply (Term.Apply Term.or x) xs) by
              simp [__from_clause]]
        simp [hEqTerm, __eo_ite, native_ite, native_teq]
        exact hOrTrue

private theorem from_clause_arg_ne_stuck {c : Term} :
    __from_clause c ≠ Term.Stuck ->
    c ≠ Term.Stuck := by
  intro hFrom hC
  subst hC
  simp [__from_clause] at hFrom

private def resolutionComponent (lit clause : Term) : Term :=
  __eo_ite (__eo_eq lit clause) (Term.Boolean false) (__eo_list_erase Term.or clause lit)

private theorem resolution_component_lit_ne_stuck {lit clause : Term} :
    clause ≠ Term.Stuck ->
    resolutionComponent lit clause ≠ Term.Stuck ->
    lit ≠ Term.Stuck := by
  intro hClause hComp hLit
  subst hLit
  unfold resolutionComponent at hComp
  simp [__eo_eq, __eo_ite, hClause, native_ite, native_teq] at hComp

private theorem resolution_component_bool_type {lit clause : Term} :
    RuleProofs.eo_has_bool_type clause ->
    OrClause (resolutionComponent lit clause) ->
    RuleProofs.eo_has_bool_type (resolutionComponent lit clause) := by
  intro hClauseBool hCompClause
  have hCompNe : resolutionComponent lit clause ≠ Term.Stuck :=
    orClause_ne_stuck hCompClause
  have hClauseNe : clause ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type clause hClauseBool
  have hLitNe : lit ≠ Term.Stuck :=
    resolution_component_lit_ne_stuck hClauseNe hCompNe
  by_cases hEq : lit = clause
  · have hEqTerm : __eo_eq lit clause = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hLitNe hClauseNe
    unfold resolutionComponent
    simp [hEqTerm, __eo_ite, native_ite, native_teq]
    exact RuleProofs.eo_has_bool_type_false
  · have hEqTerm : __eo_eq lit clause = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLitNe hClauseNe
    have hEraseNe : __eo_list_erase Term.or clause lit ≠ Term.Stuck := by
      unfold resolutionComponent at hCompNe
      simp [hEqTerm, __eo_ite, native_ite, native_teq] at hCompNe
      exact hCompNe
    have hClauseOr : OrClause clause :=
      list_erase_nonstuck_input_orClause hEraseNe
    unfold resolutionComponent
    simp [hEqTerm, __eo_ite, native_ite, native_teq]
    exact erase_preserves_bool_type hClauseOr hClauseBool hLitNe

private theorem resolution_component_true
    (M : SmtModel) (hM : model_total_typed M) {lit clause : Term} :
    RuleProofs.eo_has_bool_type clause ->
    eo_interprets M clause true ->
    (¬ RuleProofs.eo_has_bool_type lit ∨ eo_interprets M lit false) ->
    OrClause (resolutionComponent lit clause) ->
    eo_interprets M (resolutionComponent lit clause) true := by
  intro hClauseBool hClauseTrue hGood hCompClause
  have hCompNe : resolutionComponent lit clause ≠ Term.Stuck :=
    orClause_ne_stuck hCompClause
  have hClauseNe : clause ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type clause hClauseBool
  have hLitNe : lit ≠ Term.Stuck :=
    resolution_component_lit_ne_stuck hClauseNe hCompNe
  by_cases hEq : lit = clause
  · cases hGood with
    | inl hLitNotBool =>
        exfalso
        apply hLitNotBool
        simpa [hEq] using hClauseBool
    | inr hLitFalse =>
        have hClauseFalse : eo_interprets M clause false := by
          simpa [hEq] using hLitFalse
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hClauseTrue) hClauseFalse)
  · have hEqTerm : __eo_eq lit clause = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLitNe hClauseNe
    have hEraseNe : __eo_list_erase Term.or clause lit ≠ Term.Stuck := by
      unfold resolutionComponent at hCompNe
      simp [hEqTerm, __eo_ite, native_ite, native_teq] at hCompNe
      exact hCompNe
    have hClauseOr : OrClause clause :=
      list_erase_nonstuck_input_orClause hEraseNe
    unfold resolutionComponent
    simp [hEqTerm, __eo_ite, native_ite, native_teq]
    exact erase_true_of_good_lit M hM hClauseOr hClauseBool hClauseTrue hGood hLitNe

private theorem prog_resolution_true_eq (L C1 C2 : Term) :
    __eo_prog_resolution (Term.Boolean true) L (Proof.pf C1) (Proof.pf C2) =
      __from_clause (__eo_list_concat Term.or
        (resolutionComponent L (__to_clause C1))
        (resolutionComponent (Term.Apply Term.not L) (__to_clause C2))) := by
  by_cases hL : L = Term.Stuck
  · subst hL
    have hComp1 : resolutionComponent Term.Stuck (__to_clause C1) = Term.Stuck := by
      unfold resolutionComponent
      simp [__eo_eq, __eo_ite, native_ite, native_teq]
    simp [__eo_prog_resolution, hComp1, __eo_list_concat, __eo_requires, __eo_is_list,
      __eo_is_ok, __eo_get_nil_rec, __from_clause, native_ite, native_teq, native_not,
      SmtEval.native_not]
  · unfold __eo_prog_resolution
    simp [hL, resolutionComponent, __eo_ite, native_ite, native_teq]

private theorem prog_resolution_false_eq (L C1 C2 : Term) :
    __eo_prog_resolution (Term.Boolean false) L (Proof.pf C1) (Proof.pf C2) =
      __from_clause (__eo_list_concat Term.or
        (resolutionComponent (Term.Apply Term.not L) (__to_clause C1))
        (resolutionComponent L (__to_clause C2))) := by
  by_cases hL : L = Term.Stuck
  · subst hL
    have hComp2 : resolutionComponent Term.Stuck (__to_clause C2) = Term.Stuck := by
      unfold resolutionComponent
      simp [__eo_eq, __eo_ite, native_ite, native_teq]
    simp [__eo_prog_resolution, hComp2, __eo_list_concat, __eo_requires, __eo_is_list,
      __eo_is_ok, __eo_get_nil_rec, __from_clause, native_ite, native_teq, native_not,
      SmtEval.native_not]
  · unfold __eo_prog_resolution
    simp [hL, resolutionComponent, __eo_ite, native_ite, native_teq]

private theorem prog_resolution_pol_not_bool_stuck
    (pol L C1 C2 : Term) :
    pol ≠ Term.Boolean true ->
    pol ≠ Term.Boolean false ->
    __eo_prog_resolution pol L (Proof.pf C1) (Proof.pf C2) = Term.Stuck := by
  intro hTrue hFalse
  by_cases hPol : pol = Term.Stuck
  · subst hPol
    unfold __eo_prog_resolution
    simp
  · by_cases hL : L = Term.Stuck
    · subst hL
      unfold __eo_prog_resolution
      simp [hPol]
    · unfold __eo_prog_resolution
      simp [hPol, hL]
      have hLit1 : __eo_ite pol L (Term.Apply Term.not L) = Term.Stuck :=
        ite_eq_stuck_of_ne_true_false pol L (Term.Apply Term.not L) hTrue hFalse
      have hLit2 : __eo_ite pol (Term.Apply Term.not L) L = Term.Stuck :=
        ite_eq_stuck_of_ne_true_false pol (Term.Apply Term.not L) L hTrue hFalse
      rw [hLit1, hLit2]
      simp [__eo_list_concat, __eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
        __from_clause, __eo_eq, __eo_ite, native_ite, native_teq, native_not,
        SmtEval.native_not]

private theorem prog_resolution_true_properties
    (M : SmtModel) (hM : model_total_typed M)
    (L C1 C2 : Term) :
    RuleProofs.eo_has_bool_type C1 ->
    RuleProofs.eo_has_bool_type C2 ->
    __eo_prog_resolution (Term.Boolean true) L (Proof.pf C1) (Proof.pf C2) ≠ Term.Stuck ->
    StepRuleProperties M [C1, C2]
      (__eo_prog_resolution (Term.Boolean true) L (Proof.pf C1) (Proof.pf C2)) := by
  intro hC1Bool hC2Bool hProg
  let Cl1 := __to_clause C1
  let Cl2 := __to_clause C2
  let Comp1 := resolutionComponent L Cl1
  let Comp2 := resolutionComponent (Term.Apply Term.not L) Cl2
  have hCl1Bool : RuleProofs.eo_has_bool_type Cl1 := by
    simpa [Cl1] using to_clause_has_bool_type hC1Bool
  have hCl2Bool : RuleProofs.eo_has_bool_type Cl2 := by
    simpa [Cl2] using to_clause_has_bool_type hC2Bool
  have hProgRes :
      __from_clause (__eo_list_concat Term.or Comp1 Comp2) ≠ Term.Stuck := by
    rw [prog_resolution_true_eq L C1 C2] at hProg
    simpa [Cl1, Cl2, Comp1, Comp2] using hProg
  have hConcatNe : __eo_list_concat Term.or Comp1 Comp2 ≠ Term.Stuck :=
    from_clause_arg_ne_stuck hProgRes
  have hComp1Clause : OrClause Comp1 :=
    list_concat_nonstuck_left_orClause hConcatNe
  have hComp2Clause : OrClause Comp2 :=
    list_concat_nonstuck_right_orClause hConcatNe
  have hComp1Bool : RuleProofs.eo_has_bool_type Comp1 :=
    resolution_component_bool_type hCl1Bool hComp1Clause
  have hComp2Bool : RuleProofs.eo_has_bool_type Comp2 :=
    resolution_component_bool_type hCl2Bool hComp2Clause
  have hConcatClause : OrClause (__eo_list_concat Term.or Comp1 Comp2) :=
    concat_preserves_orClause hComp1Clause hComp2Clause
  have hConcatBool : RuleProofs.eo_has_bool_type (__eo_list_concat Term.or Comp1 Comp2) :=
    concat_preserves_bool_type hComp1Clause hComp2Clause hComp1Bool hComp2Bool
  have hFinalBool :
      RuleProofs.eo_has_bool_type
        (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) :=
    from_clause_preserves_bool_type hConcatClause hConcatBool
  refine ⟨?_, ?_⟩
  · intro hTrue
    have hC1True : eo_interprets M C1 true := hTrue C1 (by simp)
    have hC2True : eo_interprets M C2 true := hTrue C2 (by simp)
    have hCl1True : eo_interprets M Cl1 true := by
      simpa [Cl1] using to_clause_interprets_true M hM hC1True
    have hCl2True : eo_interprets M Cl2 true := by
      simpa [Cl2] using to_clause_interprets_true M hM hC2True
    by_cases hLBool : RuleProofs.eo_has_bool_type L
    · rcases eo_interprets_bool_cases M hM L hLBool with hLTrue | hLFalse
      · have hNotLFalse : eo_interprets M (Term.Apply Term.not L) false :=
          eo_interprets_not_false_of_true M L hLTrue
        have hComp2True : eo_interprets M Comp2 true :=
          resolution_component_true M hM hCl2Bool hCl2True (Or.inr hNotLFalse) hComp2Clause
        have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
          concat_true_of_right_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
            hComp2True
        have hFinalTrue :
            eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
          from_clause_true M hM hConcatClause hConcatBool hConcatTrue
        rw [prog_resolution_true_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
      · have hComp1True : eo_interprets M Comp1 true :=
          resolution_component_true M hM hCl1Bool hCl1True (Or.inr hLFalse) hComp1Clause
        have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
          concat_true_of_left_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
            hComp1True
        have hFinalTrue :
            eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
          from_clause_true M hM hConcatClause hConcatBool hConcatTrue
        rw [prog_resolution_true_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
    · have hComp1True : eo_interprets M Comp1 true :=
        resolution_component_true M hM hCl1Bool hCl1True (Or.inl hLBool) hComp1Clause
      have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
        concat_true_of_left_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
          hComp1True
      have hFinalTrue :
          eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
        from_clause_true M hM hConcatClause hConcatBool hConcatTrue
      rw [prog_resolution_true_eq L C1 C2]
      simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (by
        rw [prog_resolution_true_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalBool)

private theorem prog_resolution_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (L C1 C2 : Term) :
    RuleProofs.eo_has_bool_type C1 ->
    RuleProofs.eo_has_bool_type C2 ->
    __eo_prog_resolution (Term.Boolean false) L (Proof.pf C1) (Proof.pf C2) ≠ Term.Stuck ->
    StepRuleProperties M [C1, C2]
      (__eo_prog_resolution (Term.Boolean false) L (Proof.pf C1) (Proof.pf C2)) := by
  intro hC1Bool hC2Bool hProg
  let Cl1 := __to_clause C1
  let Cl2 := __to_clause C2
  let Comp1 := resolutionComponent (Term.Apply Term.not L) Cl1
  let Comp2 := resolutionComponent L Cl2
  have hCl1Bool : RuleProofs.eo_has_bool_type Cl1 := by
    simpa [Cl1] using to_clause_has_bool_type hC1Bool
  have hCl2Bool : RuleProofs.eo_has_bool_type Cl2 := by
    simpa [Cl2] using to_clause_has_bool_type hC2Bool
  have hProgRes :
      __from_clause (__eo_list_concat Term.or Comp1 Comp2) ≠ Term.Stuck := by
    rw [prog_resolution_false_eq L C1 C2] at hProg
    simpa [Cl1, Cl2, Comp1, Comp2] using hProg
  have hConcatNe : __eo_list_concat Term.or Comp1 Comp2 ≠ Term.Stuck :=
    from_clause_arg_ne_stuck hProgRes
  have hComp1Clause : OrClause Comp1 :=
    list_concat_nonstuck_left_orClause hConcatNe
  have hComp2Clause : OrClause Comp2 :=
    list_concat_nonstuck_right_orClause hConcatNe
  have hComp1Bool : RuleProofs.eo_has_bool_type Comp1 :=
    resolution_component_bool_type hCl1Bool hComp1Clause
  have hComp2Bool : RuleProofs.eo_has_bool_type Comp2 :=
    resolution_component_bool_type hCl2Bool hComp2Clause
  have hConcatClause : OrClause (__eo_list_concat Term.or Comp1 Comp2) :=
    concat_preserves_orClause hComp1Clause hComp2Clause
  have hConcatBool : RuleProofs.eo_has_bool_type (__eo_list_concat Term.or Comp1 Comp2) :=
    concat_preserves_bool_type hComp1Clause hComp2Clause hComp1Bool hComp2Bool
  have hFinalBool :
      RuleProofs.eo_has_bool_type
        (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) :=
    from_clause_preserves_bool_type hConcatClause hConcatBool
  refine ⟨?_, ?_⟩
  · intro hTrue
    have hC1True : eo_interprets M C1 true := hTrue C1 (by simp)
    have hC2True : eo_interprets M C2 true := hTrue C2 (by simp)
    have hCl1True : eo_interprets M Cl1 true := by
      simpa [Cl1] using to_clause_interprets_true M hM hC1True
    have hCl2True : eo_interprets M Cl2 true := by
      simpa [Cl2] using to_clause_interprets_true M hM hC2True
    by_cases hLBool : RuleProofs.eo_has_bool_type L
    · rcases eo_interprets_bool_cases M hM L hLBool with hLTrue | hLFalse
      · have hNotLFalse : eo_interprets M (Term.Apply Term.not L) false :=
          eo_interprets_not_false_of_true M L hLTrue
        have hComp1True : eo_interprets M Comp1 true :=
          resolution_component_true M hM hCl1Bool hCl1True (Or.inr hNotLFalse) hComp1Clause
        have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
          concat_true_of_left_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
            hComp1True
        have hFinalTrue :
            eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
          from_clause_true M hM hConcatClause hConcatBool hConcatTrue
        rw [prog_resolution_false_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
      · have hComp2True : eo_interprets M Comp2 true :=
          resolution_component_true M hM hCl2Bool hCl2True (Or.inr hLFalse) hComp2Clause
        have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
          concat_true_of_right_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
            hComp2True
        have hFinalTrue :
            eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
          from_clause_true M hM hConcatClause hConcatBool hConcatTrue
        rw [prog_resolution_false_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
    · have hComp2True : eo_interprets M Comp2 true :=
        resolution_component_true M hM hCl2Bool hCl2True (Or.inl hLBool) hComp2Clause
      have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
        concat_true_of_right_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
          hComp2True
      have hFinalTrue :
          eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
        from_clause_true M hM hConcatClause hConcatBool hConcatTrue
      rw [prog_resolution_false_eq L C1 C2]
      simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (by
        rw [prog_resolution_false_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalBool)

theorem cmd_step_resolution_properties_aux
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.resolution args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.resolution args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.resolution args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.resolution args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons pol args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons L args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n1 premises =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n2 premises =>
                      cases premises with
                      | nil =>
                          let C1 := __eo_state_proven_nth s n1
                          let C2 := __eo_state_proven_nth s n2
                          have hC1Bool : RuleProofs.eo_has_bool_type C1 :=
                            hPremisesBool C1 (by simp [C1, premiseTermList])
                          have hC2Bool : RuleProofs.eo_has_bool_type C2 :=
                            hPremisesBool C2 (by simp [C2, premiseTermList])
                          change __eo_prog_resolution pol L
                            (Proof.pf (__eo_state_proven_nth s n1))
                            (Proof.pf (__eo_state_proven_nth s n2)) ≠ Term.Stuck at hProg
                          by_cases hPolTrue : pol = Term.Boolean true
                          · subst pol
                            change StepRuleProperties M
                              [__eo_state_proven_nth s n1, __eo_state_proven_nth s n2]
                              (__eo_prog_resolution (Term.Boolean true) L
                                (Proof.pf (__eo_state_proven_nth s n1))
                                (Proof.pf (__eo_state_proven_nth s n2)))
                            simpa [C1, C2, premiseTermList] using
                              prog_resolution_true_properties M hM L C1 C2
                                hC1Bool hC2Bool hProg
                          · by_cases hPolFalse : pol = Term.Boolean false
                            · subst pol
                              change StepRuleProperties M
                                [__eo_state_proven_nth s n1, __eo_state_proven_nth s n2]
                                (__eo_prog_resolution (Term.Boolean false) L
                                  (Proof.pf (__eo_state_proven_nth s n1))
                                  (Proof.pf (__eo_state_proven_nth s n2)))
                              simpa [C1, C2, premiseTermList] using
                                prog_resolution_false_properties M hM L C1 C2
                                  hC1Bool hC2Bool hProg
                            · exact False.elim
                                (hProg (prog_resolution_pol_not_bool_stuck
                                  pol L C1 C2 hPolTrue hPolFalse))
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
