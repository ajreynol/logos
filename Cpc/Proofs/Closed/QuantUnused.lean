import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Closed.UOpIndices

open Eo
open SmtEval
open Smtm
open TranslationProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def eoListOfTerms : List Term -> Term
  | [] => Term.__eo_List_nil
  | x :: xs => Term.Apply (Term.Apply Term.__eo_List_cons x) (eoListOfTerms xs)

private theorem native_and_left_eq_true {a b : native_Bool} :
    native_and a b = true ->
    a = true := by
  intro h
  cases a <;> cases b <;> simp [native_and] at h ⊢

private theorem native_and_right_eq_true {a b : native_Bool} :
    native_and a b = true ->
    b = true := by
  intro h
  cases a <;> cases b <;> simp [native_and] at h ⊢

private theorem native_eo_to_smt_term_mem_append_right
    (x : Term) :
    ∀ extra env : List Term,
      native_eo_to_smt_term_mem x env = true ->
        native_eo_to_smt_term_mem x (extra ++ env) = true
  | [], env, h => h
  | y :: extra, env, h => by
      by_cases hxy : x = y
      · simp [native_eo_to_smt_term_mem, hxy, native_or]
      · simp [native_eo_to_smt_term_mem, hxy, native_or,
          native_eo_to_smt_term_mem_append_right x extra env h]

private theorem native_eo_to_smt_term_list_eq_eoListOfTerms :
    ∀ {xsTerm : Term} {xs : List Term},
      native_eo_to_smt_term_list xsTerm = some xs ->
        xsTerm = eoListOfTerms xs
  | Term.__eo_List_nil, [], h => by
      rfl
  | Term.Apply (Term.Apply Term.__eo_List_cons x) xsTerm, xs, h => by
      simp [native_eo_to_smt_term_list] at h
      split at h
      · rename_i ys hYs
        cases h
        have hTail :=
          native_eo_to_smt_term_list_eq_eoListOfTerms
            (xsTerm := xsTerm) (xs := ys) hYs
        simp [eoListOfTerms, hTail]
      · contradiction
  | Term.Stuck, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.UOp op, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.UOp1 op x, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.UOp2 op x y, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.UOp3 op x y z, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.__eo_List, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.__eo_List_cons, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.Bool, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.Boolean b, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.Numeral n, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.Rational q, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.String s, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.Binary w n, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.Type, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.FunType, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.Var s T, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.DatatypeType s d, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.DatatypeTypeRef s, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.DtcAppType T U, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.DtCons s d i, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.DtSel s d i j, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.USort i, xs, h => by
      simp [native_eo_to_smt_term_list] at h
  | Term.UConst i T, xs, h => by
      simp [native_eo_to_smt_term_list] at h

private theorem eoListOfTerms_get_nil_rec :
    ∀ xs : List Term,
      __eo_get_nil_rec Term.__eo_List_cons (eoListOfTerms xs) =
        Term.__eo_List_nil
  | [] => by
      simp [eoListOfTerms, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_requires, native_ite, native_teq, native_not]
  | x :: xs => by
      simpa [eoListOfTerms, __eo_get_nil_rec, __eo_requires,
        native_ite, native_teq, native_not] using
        eoListOfTerms_get_nil_rec xs

private theorem eo_mk_apply_list_cons_eoListOfTerms
    (x : Term) :
    ∀ xs : List Term,
      __eo_mk_apply (Term.Apply Term.__eo_List_cons x)
          (eoListOfTerms xs) =
        eoListOfTerms (x :: xs)
  | [] => by
      simp [eoListOfTerms, __eo_mk_apply]
  | y :: ys => by
      simp [eoListOfTerms, __eo_mk_apply]

private theorem eoListOfTerms_is_list :
    ∀ xs : List Term,
      __eo_is_list Term.__eo_List_cons (eoListOfTerms xs) =
        Term.Boolean true
  | [] => by
      simp [eoListOfTerms, __eo_is_list, __eo_get_nil_rec,
        __eo_is_list_nil, __eo_is_ok, __eo_requires, native_ite,
        native_teq, native_not]
  | x :: xs => by
      simp [eoListOfTerms, __eo_is_list, __eo_get_nil_rec,
        __eo_requires, __eo_is_ok, native_ite, native_teq,
        native_not]
      intro hStuck
      have hGet := eoListOfTerms_get_nil_rec xs
      rw [hGet] at hStuck
      cases hStuck

private theorem eoListOfTerms_concat_rec :
    ∀ xs ys : List Term,
      __eo_list_concat_rec (eoListOfTerms xs) (eoListOfTerms ys) =
        eoListOfTerms (xs ++ ys)
  | [], ys => by
      cases ys <;> simp [eoListOfTerms, __eo_list_concat_rec]
  | x :: xs, [] => by
      change
        __eo_list_concat_rec
            (Term.Apply (Term.Apply Term.__eo_List_cons x)
              (eoListOfTerms xs))
            Term.__eo_List_nil =
          eoListOfTerms (x :: (xs ++ []))
      rw [__eo_list_concat_rec.eq_def]
      change
        __eo_mk_apply (Term.Apply Term.__eo_List_cons x)
            (__eo_list_concat_rec (eoListOfTerms xs) Term.__eo_List_nil) =
          eoListOfTerms (x :: (xs ++ []))
      change
        __eo_mk_apply (Term.Apply Term.__eo_List_cons x)
            (__eo_list_concat_rec (eoListOfTerms xs)
              (eoListOfTerms [])) =
          eoListOfTerms (x :: (xs ++ []))
      rw [eoListOfTerms_concat_rec xs []]
      exact eo_mk_apply_list_cons_eoListOfTerms x (xs ++ [])
  | x :: xs, y :: ys => by
      change
        __eo_list_concat_rec
            (Term.Apply (Term.Apply Term.__eo_List_cons x)
              (eoListOfTerms xs))
            (Term.Apply (Term.Apply Term.__eo_List_cons y)
              (eoListOfTerms ys)) =
          eoListOfTerms (x :: (xs ++ y :: ys))
      rw [__eo_list_concat_rec.eq_def]
      change
        __eo_mk_apply (Term.Apply Term.__eo_List_cons x)
            (__eo_list_concat_rec (eoListOfTerms xs)
              (Term.Apply (Term.Apply Term.__eo_List_cons y)
                (eoListOfTerms ys))) =
          eoListOfTerms (x :: (xs ++ y :: ys))
      change
        __eo_mk_apply (Term.Apply Term.__eo_List_cons x)
            (__eo_list_concat_rec (eoListOfTerms xs)
              (eoListOfTerms (y :: ys))) =
          eoListOfTerms (x :: (xs ++ y :: ys))
      rw [eoListOfTerms_concat_rec xs (y :: ys)]
      exact eo_mk_apply_list_cons_eoListOfTerms x (xs ++ y :: ys)

private theorem eoListOfTerms_concat
    (xs ys : List Term) :
    __eo_list_concat Term.__eo_List_cons
        (eoListOfTerms xs) (eoListOfTerms ys) =
      eoListOfTerms (xs ++ ys) := by
  simp [__eo_list_concat, __eo_requires, eoListOfTerms_is_list,
    native_ite, native_teq, native_not, eoListOfTerms_concat_rec]

private theorem eo_is_closed_rec_var_eoListOfTerms_of_mem :
    ∀ {s T : Term} {env : List Term},
      (∀ x, x ∈ env -> x ≠ Term.Stuck) ->
      native_eo_to_smt_term_mem (Term.Var s T) env = true ->
        __eo_is_closed_rec (Term.Var s T) (eoListOfTerms env) =
          Term.Boolean true
  | s, T, [], _hNoStuck, h => by
      simp [native_eo_to_smt_term_mem] at h
  | s, T, y :: ys, hNoStuck, h => by
      have hyNoStuck : y ≠ Term.Stuck := hNoStuck y (by simp)
      have hysNoStuck : ∀ z, z ∈ ys -> z ≠ Term.Stuck := by
        intro z hz
        exact hNoStuck z (by simp [hz])
      by_cases hEq : Term.Var s T = y
      · subst y
        simp [eoListOfTerms, __eo_is_closed_rec, __eo_ite, __eo_eq,
          native_ite, native_teq]
      · have hTail :
            native_eo_to_smt_term_mem (Term.Var s T) ys = true := by
          simpa [native_eo_to_smt_term_mem, hEq, native_or] using h
        have hEq' : y ≠ Term.Var s T := by
          intro hy
          exact hEq hy.symm
        cases y <;> try contradiction
        all_goals
          simpa [eoListOfTerms, __eo_is_closed_rec, __eo_ite, __eo_eq,
            hEq, hEq', native_ite, native_teq] using
            eo_is_closed_rec_var_eoListOfTerms_of_mem hysNoStuck hTail

/--
Bridge from the native standalone-closed checker to SMT closedness.

This deliberately targets `SmtTermClosedIn`, not `__eo_is_closed`. Native
closedness accepts raw quantifier binder lists, while `__eo_is_closed_rec` can
become `Stuck` if such a list contains `Term.Stuck`; the SMT translation of
that malformed quantifier is `SmtTerm.None`, which is still SMT-closed and is
all the evaluator invariance theorem needs.
-/
private theorem smtTermClosedIn_of_native_eo_to_smt_closed_safe
    (t : Term)
    (hClosed : native_eo_to_smt_closed t = true)
    (hSafe : NativeEoToSmtUOpIndicesSafe t) :
    SmtTermClosedIn [] (__eo_to_smt t) := by
  sorry

private theorem smtx_model_eval_eq_push_of_native_closed_safe
    (M : SmtModel) (F : Term) (s : native_String) (T : SmtType)
    (v : SmtValue)
    (hClosed : native_eo_to_smt_closed F = true)
    (hSafe : NativeEoToSmtUOpIndicesSafe F) :
    __smtx_model_eval (native_model_push M s T v) (__eo_to_smt F) =
      __smtx_model_eval M (__eo_to_smt F) := by
  have hSmtClosed :=
    smtTermClosedIn_of_native_eo_to_smt_closed_safe F hClosed hSafe
  exact
    (smt_model_eval_eq_of_eo_smt_closed
      (P := F) (M := M) (N := native_model_push M s T v)
      hSmtClosed (model_agrees_on_globals_push M s T v)).symm

/--
If `contains_atomic_term` says an EO body does not mention a binder variable,
then changing only that SMT variable assignment does not change the evaluation
of the translated body.

The `NativeEoToSmtUOpIndicesSafe` hypothesis is the bridge that makes the Logos
syntactic check sound for indexed operators: opaque indices cannot hide an
occurrence of the binder because every UOp index is standalone closed.
-/
theorem smtx_model_eval_eq_push_of_contains_atomic_term_false
    (M : SmtModel) (F : Term) (s : native_String) (T : Term)
    (v : SmtValue)
    (hTWF : smtx_type_field_wf_rec (__eo_to_smt_type T) native_reflist_nil)
    (hNoOccur :
      __contains_atomic_term F (Term.Var (Term.String s) T) =
        Term.Boolean false)
    (hSafe : NativeEoToSmtUOpIndicesSafe F) :
    __smtx_model_eval
        (native_model_push M s (__eo_to_smt_type T) v)
        (__eo_to_smt F) =
      __smtx_model_eval M (__eo_to_smt F) := by
  sorry

/--
Semantic core for `quant_unused_vars`: rebuilding the quantifier with
`__mk_quant_unused_vars_rec` preserves the translated SMT evaluation.

This is intentionally phrased below the checker-rule layer. The proof should be
by induction over the EO binder list, using
`smtx_model_eval_eq_push_of_contains_atomic_term_false` for dropped binders and
the usual shadowing/idempotence lemmas for duplicate binders.
-/
theorem smtx_model_eval_quant_unused_vars_mk_core
    (M : SmtModel) (hM : model_total_typed M)
    (Q x F : Term)
    (hQ :
      Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply Q x) F))
          (__mk_quant Q (__mk_quant_unused_vars_rec x F) F)))
    (hSafe :
      NativeEoToSmtUOpIndicesSafe
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply Q x) F))
          (__mk_quant Q (__mk_quant_unused_vars_rec x F) F))) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply Q x) F)) =
      __smtx_model_eval M
        (__eo_to_smt
          (__mk_quant Q (__mk_quant_unused_vars_rec x F) F)) := by
  sorry
