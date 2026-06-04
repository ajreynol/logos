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

private theorem quantVarTerm_ne_stuck {t : Term} :
    IsQuantVarTerm t -> t ≠ Term.Stuck := by
  intro h
  cases t <;> simp [IsQuantVarTerm] at h ⊢

private theorem eoListOfTerms_ne_stuck (xs : List Term) :
    eoListOfTerms xs ≠ Term.Stuck := by
  cases xs <;> simp [eoListOfTerms]

private theorem eoListOfTerms_inj {xs ys : List Term} :
    eoListOfTerms xs = eoListOfTerms ys -> xs = ys := by
  intro h
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp [eoListOfTerms] at h ⊢
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [eoListOfTerms] at h
      | cons y ys =>
          simp [eoListOfTerms] at h
          rcases h with ⟨hxy, htail⟩
          subst y
          exact congrArg (List.cons x) (ih htail)

private theorem eoListOfTerms_is_list_true (xs : List Term) :
    __eo_is_list Term.__eo_List_cons (eoListOfTerms xs) =
      Term.Boolean true := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, __eo_is_list, __eo_get_nil_rec, __eo_requires,
        __eo_is_ok, __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not]
  | cons _ xs ih =>
      simp [eoListOfTerms, __eo_is_list, __eo_get_nil_rec, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]
      simpa [__eo_is_list, eoListOfTerms_ne_stuck xs] using ih

private theorem eo_eq_eq_true_of_eq_local {x y : Term} :
    x = y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean true := by
  intro hEq _ _
  subst y
  simp [__eo_eq, native_teq]

private theorem eo_eq_eq_false_of_ne_local {x y : Term} :
    x ≠ y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean false := by
  intro hNe _ _
  have hNeYX : y ≠ x := by
    intro h
    exact hNe h.symm
  simp [__eo_eq, native_teq, hNeYX]

private theorem eo_prepend_if_false_of_ne_stuck
    (f x res : Term) :
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    res ≠ Term.Stuck ->
      __eo_prepend_if (Term.Boolean false) f x res = res := by
  intro hf hx hRes
  cases f <;> cases x <;> cases res <;>
    simp [__eo_prepend_if] at hf hx hRes ⊢

private theorem eo_list_erase_all_rec_eoListOfTerms_eq
    {xs : List Term} {e : Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (he : e ≠ Term.Stuck) :
    __eo_list_erase_all_rec (eoListOfTerms xs) e =
      eoListOfTerms (xs.filter fun x => x != e) := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, __eo_list_erase_all_rec]
  | cons x xs ih =>
      have hx : x ≠ Term.Stuck := hxs x (by simp)
      have htail : ∀ t ∈ xs, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (by simp [ht])
      by_cases hxe : x = e
      · subst e
        have hEqTerm : __eo_eq x x = Term.Boolean true :=
          eo_eq_eq_true_of_eq_local rfl hx hx
        have hTailEq := ih htail
        have hTailNe :
            eoListOfTerms (xs.filter fun y => y != x) ≠ Term.Stuck :=
          eoListOfTerms_ne_stuck _
        rw [show
          __eo_list_erase_all_rec (eoListOfTerms (x :: xs)) x =
            __eo_prepend_if (__eo_not (__eo_eq x x))
              Term.__eo_List_cons x
              (__eo_list_erase_all_rec (eoListOfTerms xs) x) by
            simp [eoListOfTerms, __eo_list_erase_all_rec]]
        rw [hEqTerm, hTailEq]
        simp [__eo_not, native_not,
          eo_prepend_if_false_of_ne_stuck Term.__eo_List_cons x
            (eoListOfTerms (xs.filter fun y => y != x)) (by simp) hx hTailNe]
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local (by
            intro h
            exact hxe h.symm) he hx
        have hTailEq := ih htail
        simp [eoListOfTerms, __eo_list_erase_all_rec, __eo_prepend_if,
          __eo_not, hEqTerm, native_not, hxe, hTailEq,
          eoListOfTerms_ne_stuck]

private def setofTermList : List Term -> List Term
  | [] => []
  | x :: xs => x :: (setofTermList xs).filter (fun y => y != x)

private theorem setofTermList_mem {xs : List Term} {t : Term} :
    t ∈ setofTermList xs -> t ∈ xs := by
  induction xs with
  | nil =>
      simp [setofTermList]
  | cons x xs ih =>
      intro ht
      simp [setofTermList] at ht
      rcases ht with ht | ht
      · simp [ht]
      · simp [ih ht.1]

private theorem nodup_filter_of_nodup
    (p : Term -> Bool) {xs : List Term} :
    List.Nodup xs -> List.Nodup (xs.filter p) := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro h
      rcases List.nodup_cons.mp h with ⟨hxNotMem, hxs⟩
      cases hp : p x
      · simp [List.filter, hp, ih hxs]
      · simp [List.filter, hp]
        exact ⟨hxNotMem, ih hxs⟩

private theorem setofTermList_nodup (xs : List Term) :
    List.Nodup (setofTermList xs) := by
  induction xs with
  | nil =>
      simp [setofTermList]
  | cons x xs ih =>
      rw [setofTermList]
      rw [List.nodup_cons]
      constructor
      · simp
      · exact nodup_filter_of_nodup _ ih

private theorem setofTermList_eq_self_nodup
    (xs : List Term) :
    setofTermList xs = xs -> List.Nodup xs := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro hSet
      have hTail :
          (setofTermList xs).filter (fun y => y != x) = xs := by
        simpa [setofTermList] using congrArg List.tail hSet
      have hxNotMem : x ∉ xs := by
        intro hxMem
        have hxMemFilter :
            x ∈ (setofTermList xs).filter (fun y => y != x) := by
          simpa [hTail] using hxMem
        simp at hxMemFilter
      have hTailNodup : List.Nodup xs := by
        have hFilterNodup :
            List.Nodup ((setofTermList xs).filter (fun y => y != x)) :=
          nodup_filter_of_nodup _ (setofTermList_nodup xs)
        simpa [hTail] using hFilterNodup
      rw [List.nodup_cons]
      exact ⟨hxNotMem, hTailNodup⟩

private theorem eo_list_setof_rec_eoListOfTerms_eq
    {xs : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck) :
    __eo_list_setof_rec (eoListOfTerms xs) =
      eoListOfTerms (setofTermList xs) := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, setofTermList, __eo_list_setof_rec]
  | cons x xs ih =>
      have hx : x ≠ Term.Stuck := hxs x (by simp)
      have htail : ∀ t ∈ xs, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (by simp [ht])
      have hErase :
          __eo_list_erase_all_rec (__eo_list_setof_rec (eoListOfTerms xs)) x =
            eoListOfTerms ((setofTermList xs).filter (fun y => y != x)) := by
        rw [ih htail]
        exact eo_list_erase_all_rec_eoListOfTerms_eq
          (xs := setofTermList xs) (e := x)
          (by
            intro t ht
            exact hxs t (by
              simp [setofTermList_mem (xs := xs) ht]))
          hx
      simp [eoListOfTerms, setofTermList, __eo_list_setof_rec,
        __eo_mk_apply, hErase, eoListOfTerms_ne_stuck]

private theorem eo_list_setof_eoListOfTerms_eq_self_nodup
    {xs : List Term}
    (hxs : ∀ t ∈ xs, IsQuantVarTerm t) :
    __eo_list_setof Term.__eo_List_cons (eoListOfTerms xs) =
        eoListOfTerms xs ->
      List.Nodup xs := by
  intro hSetof
  have hxsNe : ∀ t ∈ xs, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hxs t ht)
  have hRec :
      __eo_list_setof_rec (eoListOfTerms xs) = eoListOfTerms xs := by
    simpa [__eo_list_setof, eoListOfTerms_is_list_true, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not] using hSetof
  have hSetofList : setofTermList xs = xs :=
    eoListOfTerms_inj (by
      simpa [eo_list_setof_rec_eoListOfTerms_eq hxsNe] using hRec)
  exact setofTermList_eq_self_nodup xs hSetofList

private theorem eo_list_find_rec_not_quant_var_eoListOfTerms
    (vars : List Term) (target : Term) (start : native_Int)
    (hTargetNe : target ≠ Term.Stuck)
    (hTarget : ¬ IsQuantVarTerm target)
    (hVars : ∀ t ∈ vars, IsQuantVarTerm t) :
    __eo_list_find_rec (eoListOfTerms vars) target (Term.Numeral start) =
      Term.Numeral (-1 : native_Int) := by
  induction vars generalizing start with
  | nil =>
      simp [eoListOfTerms, __eo_list_find_rec]
  | cons x xs ih =>
      have hx : IsQuantVarTerm x := hVars x (by simp)
      have htail : ∀ t ∈ xs, IsQuantVarTerm t := by
        intro t ht
        exact hVars t (by simp [ht])
      cases x <;> simp [IsQuantVarTerm] at hx
      case Var name T =>
        cases name <;> simp at hx
        case String s =>
          have hne : Term.Var (Term.String s) T ≠ target := by
            intro hEq
            subst target
            exact hTarget (by simp [IsQuantVarTerm])
          have hne' : target ≠ Term.Var (Term.String s) T := hne.symm
          have hTailEval :
              __eo_list_find_rec (eoListOfTerms xs) target
                  (Term.Numeral (native_zplus start 1)) =
                Term.Numeral (-1 : native_Int) :=
            ih (native_zplus start 1) htail
          simp [eoListOfTerms, __eo_list_find_rec, __eo_eq,
            native_teq, hne', __eo_ite, native_ite]
          simpa [__eo_add, native_zplus] using hTailEval

private theorem eo_list_find_not_quant_var_eoListOfTerms
    (vars : List Term) (target : Term)
    (hTargetNe : target ≠ Term.Stuck)
    (hTarget : ¬ IsQuantVarTerm target)
    (hVars : ∀ t ∈ vars, IsQuantVarTerm t) :
    __eo_list_find Term.__eo_List_cons (eoListOfTerms vars) target =
      Term.Numeral (-1 : native_Int) := by
  simp [__eo_list_find, eoListOfTerms_is_list_true, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not,
    eo_list_find_rec_not_quant_var_eoListOfTerms vars target 0
      hTargetNe hTarget hVars]

private def skolemTermList (F : Term) : native_Int -> List Term -> Term
  | _, [] => Term.__eo_List_nil
  | i, _ :: xs =>
      Term.Apply
        (Term.Apply Term.__eo_List_cons
          (Term.UOp2 UserOp2._at_quantifiers_skolemize F (Term.Numeral i)))
        (skolemTermList F (native_zplus i 1) xs)

private theorem skolemTermList_ne_stuck
    (xs : List Term) (F : Term) (i : native_Int) :
    skolemTermList F i xs ≠ Term.Stuck := by
  induction xs generalizing i with
  | nil =>
      simp [skolemTermList]
  | cons x xs ih =>
      simp [skolemTermList]

private theorem eo_mk_apply_of_ne_stuck
    {f x : Term} (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem eo_requires_result_eq_of_ne_stuck_local
    (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
      __eo_requires x y z = z := by
  intro hReq
  by_cases hEq : x = y
  · subst y
    by_cases hStuck : x = Term.Stuck
    · subst x
      exact False.elim <| hReq (by
        simp [__eo_requires, native_teq, native_ite, native_not,
          SmtEval.native_not])
    · cases x <;> simp [__eo_requires, native_teq, native_ite,
        native_not, SmtEval.native_not] at hStuck ⊢
  · exact False.elim <| hReq (by
      simp [__eo_requires, native_teq, hEq, native_ite])

private theorem eo_requires_args_eq_of_ne_stuck_local
    (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
      x = y := by
  intro hReq
  by_cases hEq : x = y
  · exact hEq
  · exact False.elim <| hReq (by
      simp [__eo_requires, native_teq, hEq, native_ite])

private theorem mk_skolems_eoListOfTerms_numeral
    (xs : List Term) (F : Term) (i : native_Int)
    (hF : F ≠ Term.Stuck) :
    __mk_skolems (eoListOfTerms xs) F (Term.Numeral i) =
      skolemTermList F i xs := by
  induction xs generalizing i with
  | nil =>
      simp [eoListOfTerms, skolemTermList, __mk_skolems]
  | cons x xs ih =>
      have hTail : skolemTermList F (native_zplus i 1) xs ≠ Term.Stuck :=
        skolemTermList_ne_stuck xs F (native_zplus i 1)
      have hTailEq :
          __mk_skolems (eoListOfTerms xs) F
              (Term.Numeral (native_zplus i 1)) =
            skolemTermList F (native_zplus i 1) xs :=
        ih (native_zplus i 1)
      simp [eoListOfTerms, skolemTermList, __mk_skolems]
      rw [show __eo_add (Term.Numeral i) (Term.Numeral 1) =
          Term.Numeral (native_zplus i 1) by rfl]
      rw [hTailEq]
      exact eo_mk_apply_of_ne_stuck (by simp) hTail

private theorem contains_atomic_term_list_free_rec_nil_atom_false
    (vars : List Term)
    (hVars : ∀ t ∈ vars, IsQuantVarTerm t) :
    __contains_atomic_term_list_free_rec Term.__eo_List_nil
        (eoListOfTerms vars) Term.__eo_List_nil =
      Term.Boolean false := by
  have hFind :
      __eo_list_find Term.__eo_List_cons (eoListOfTerms vars)
          Term.__eo_List_nil =
        Term.Numeral (-1 : native_Int) :=
    eo_list_find_not_quant_var_eoListOfTerms
      vars Term.__eo_List_nil (by simp) (by simp [IsQuantVarTerm]) hVars
  rw [__contains_atomic_term_list_free_rec.eq_6]
  rw [hFind]
  rfl
  all_goals simp [eoListOfTerms_ne_stuck]

private theorem contains_atomic_term_list_free_rec_cons_atom_false
    (vars : List Term)
    (hVars : ∀ t ∈ vars, IsQuantVarTerm t) :
    __contains_atomic_term_list_free_rec Term.__eo_List_cons
        (eoListOfTerms vars) Term.__eo_List_nil =
      Term.Boolean false := by
  have hFind :
      __eo_list_find Term.__eo_List_cons (eoListOfTerms vars)
          Term.__eo_List_cons =
        Term.Numeral (-1 : native_Int) :=
    eo_list_find_not_quant_var_eoListOfTerms
      vars Term.__eo_List_cons (by simp) (by simp [IsQuantVarTerm]) hVars
  rw [__contains_atomic_term_list_free_rec.eq_6]
  rw [hFind]
  rfl
  all_goals simp [eoListOfTerms_ne_stuck]

private theorem contains_atomic_term_list_free_rec_skolem_atom_false
    (vars : List Term) (F : Term) (i : native_Int)
    (hVars : ∀ t ∈ vars, IsQuantVarTerm t) :
    __contains_atomic_term_list_free_rec
        (Term.UOp2 UserOp2._at_quantifiers_skolemize F (Term.Numeral i))
        (eoListOfTerms vars) Term.__eo_List_nil =
      Term.Boolean false := by
  have hFind :
      __eo_list_find Term.__eo_List_cons (eoListOfTerms vars)
          (Term.UOp2 UserOp2._at_quantifiers_skolemize F (Term.Numeral i)) =
        Term.Numeral (-1 : native_Int) :=
    eo_list_find_not_quant_var_eoListOfTerms
      vars
        (Term.UOp2 UserOp2._at_quantifiers_skolemize F (Term.Numeral i))
      (by simp) (by simp [IsQuantVarTerm]) hVars
  rw [__contains_atomic_term_list_free_rec.eq_6]
  rw [hFind]
  rfl
  all_goals simp [eoListOfTerms_ne_stuck]

private theorem contains_atomic_term_list_free_rec_skolemTermList_false
    (vars xs : List Term) (F : Term) (i : native_Int)
    (hVars : ∀ t ∈ vars, IsQuantVarTerm t) :
    __contains_atomic_term_list_free_rec (skolemTermList F i xs)
        (eoListOfTerms vars) Term.__eo_List_nil =
      Term.Boolean false := by
  induction xs generalizing i with
  | nil =>
      exact contains_atomic_term_list_free_rec_nil_atom_false vars hVars
  | cons x xs ih =>
      have hCons :=
        contains_atomic_term_list_free_rec_cons_atom_false vars hVars
      have hSkolem :=
        contains_atomic_term_list_free_rec_skolem_atom_false vars F i hVars
      have hHead :
          __contains_atomic_term_list_free_rec
              (Term.Apply Term.__eo_List_cons
                (Term.UOp2 UserOp2._at_quantifiers_skolemize F
                  (Term.Numeral i)))
              (eoListOfTerms vars) Term.__eo_List_nil =
            Term.Boolean false := by
        rw [__contains_atomic_term_list_free_rec.eq_5]
        rw [hCons, hSkolem]
        rfl
        all_goals simp [eoListOfTerms_ne_stuck]
      have hTail := ih (native_zplus i 1)
      simp [skolemTermList]
      rw [__contains_atomic_term_list_free_rec.eq_5]
      rw [hHead, hTail]
      rfl
      all_goals simp [eoListOfTerms_ne_stuck]

private theorem contains_atomic_term_list_free_rec_mk_skolems_false
    (vars xs : List Term) (F : Term)
    (hF : F ≠ Term.Stuck)
    (hVars : ∀ t ∈ vars, IsQuantVarTerm t) :
    __contains_atomic_term_list_free_rec
        (__mk_skolems (eoListOfTerms xs) F (Term.Numeral 0))
        (eoListOfTerms vars) Term.__eo_List_nil =
      Term.Boolean false := by
  rw [mk_skolems_eoListOfTerms_numeral xs F 0 hF]
  exact contains_atomic_term_list_free_rec_skolemTermList_false
    vars xs F 0 hVars

private theorem mk_skolems_eoListOfTerms_ne_stuck
    (xs : List Term) (F : Term) (i : native_Int)
    (hF : F ≠ Term.Stuck) :
    __mk_skolems (eoListOfTerms xs) F (Term.Numeral i) ≠ Term.Stuck := by
  rw [mk_skolems_eoListOfTerms_numeral xs F i hF]
  exact skolemTermList_ne_stuck xs F i

private theorem substitute_simul_not_op_eoListOfTerms
    (vars : List Term) (ss : Term)
    (hss : ss ≠ Term.Stuck)
    (hVars : ∀ t ∈ vars, IsQuantVarTerm t) :
    __substitute_simul (Term.UOp UserOp.not) (eoListOfTerms vars) ss =
      Term.UOp UserOp.not := by
  have hFind :
      __eo_list_find Term.__eo_List_cons (eoListOfTerms vars)
          (Term.UOp UserOp.not) =
        Term.Numeral (-1 : native_Int) :=
    eo_list_find_not_quant_var_eoListOfTerms
      vars (Term.UOp UserOp.not) (by simp) (by simp [IsQuantVarTerm]) hVars
  rw [__substitute_simul.eq_6]
  rw [hFind]
  rfl
  all_goals simp [eoListOfTerms_ne_stuck, hss]

private theorem substitute_simul_not_apply_eoListOfTerms
    (vars : List Term) (G ss : Term)
    (hss : ss ≠ Term.Stuck)
    (hVars : ∀ t ∈ vars, IsQuantVarTerm t) :
    __substitute_simul (Term.Apply (Term.UOp UserOp.not) G)
        (eoListOfTerms vars) ss =
      __eo_mk_apply (Term.UOp UserOp.not)
        (__substitute_simul G (eoListOfTerms vars) ss) := by
  rw [__substitute_simul.eq_5] <;> try
    simp [eoListOfTerms_ne_stuck, hss,
      substitute_simul_not_op_eoListOfTerms vars ss hss hVars]

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
      __eo_list_setof Term.__eo_List_cons xs = xs ∧
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
                              let result :=
                                __substitute_simul
                                  (Term.Apply (Term.UOp UserOp.not) G) xs
                                  (__mk_skolems xs
                                    (Term.Apply
                                      (Term.Apply
                                        (Term.UOp UserOp.forall) xs) G)
                                    (Term.Numeral 0))
                              have hReqNe :
                                  __eo_requires
                                      (__eo_list_setof
                                        Term.__eo_List_cons xs) xs result ≠
                                    Term.Stuck := by
                                simpa [__eo_prog_skolemize, result] using hProg
                              have hReqEq :
                                  __eo_requires
                                      (__eo_list_setof
                                        Term.__eo_List_cons xs) xs result =
                                    result :=
                                eo_requires_result_eq_of_ne_stuck_local
                                  _ _ _ hReqNe
                              have hSetof :
                                  __eo_list_setof
                                      Term.__eo_List_cons xs = xs :=
                                eo_requires_args_eq_of_ne_stuck_local
                                  _ _ _ hReqNe
                              refine ⟨xs, G, rfl, hSetof, ?_⟩
                              simpa [__eo_prog_skolemize, result] using hReqEq
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

private theorem smtx_typeof_not_arg_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  cases h : __smtx_typeof t <;>
    simp [h, native_ite, native_Teq] at hTy ⊢

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

/--
A true Boolean `not (forall xs G)` supplies the concrete zero-index choice
witnesses that make `not G` true.
-/
private theorem pushChoiceWitnesses_eval_true_of_not_forall
    (M : SmtModel) (xs G : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) G)))
    (hTrue :
      eo_interprets M
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) G)) true) :
    ∃ ts,
      xs = eoListOfTerms ts ∧
        (∀ t ∈ ts, IsQuantVarTerm t) ∧
        __smtx_model_eval
            (pushChoiceWitnesses M xs (SmtTerm.not (__eo_to_smt G)))
            (SmtTerm.not (__eo_to_smt G)) =
          SmtValue.Boolean true := by
  let existsBody := __eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt G))
  have hxs : xs ≠ Term.__eo_List_nil :=
    not_forall_vars_non_nil_of_has_bool_type xs G hBool
  have hExistsEval :
      __smtx_model_eval M existsBody = SmtValue.Boolean true := by
    simpa [existsBody] using
      not_forall_true_implies_exists_not_true M xs G hxs hTrue
  have hNotNotTy :
      __smtx_typeof (SmtTerm.not (SmtTerm.not existsBody)) = SmtType.Bool := by
    unfold RuleProofs.eo_has_bool_type at hBool
    rw [eo_to_smt_not_forall_eq xs G hxs] at hBool
    simpa [existsBody] using hBool
  have hNotTy :
      __smtx_typeof (SmtTerm.not existsBody) = SmtType.Bool :=
    smtx_typeof_not_arg_bool (SmtTerm.not existsBody) hNotNotTy
  have hExistsTy : __smtx_typeof existsBody = SmtType.Bool :=
    smtx_typeof_not_arg_bool existsBody hNotTy
  simpa [existsBody] using
    pushChoiceWitnesses_eval_true_of_bool_exists
      M xs (SmtTerm.not (__eo_to_smt G)) hExistsTy hExistsEval

private theorem pushChoiceWitnesses_agrees_on_globals
    (M : SmtModel) (xs : List Term) (body : SmtTerm)
    (hxs : ∀ t ∈ xs, IsQuantVarTerm t) :
    model_agrees_on_globals M
      (pushChoiceWitnesses M (eoListOfTerms xs) body) := by
  induction xs generalizing M body with
  | nil =>
      simpa [eoListOfTerms, pushChoiceWitnesses] using
        model_agrees_on_globals_refl M
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
          simpa [eoListOfTerms, pushChoiceWitnesses, tailBody, v] using
            model_agrees_on_globals_trans
              (model_agrees_on_globals_push M s (__eo_to_smt_type T) v)
              (ih (M := native_model_push M s (__eo_to_smt_type T) v)
                (body := body) htail)

/--
The witness model recovered from a true negated forall also agrees with the
original model on globals.
-/
private theorem pushChoiceWitnesses_not_forall_package
    (M : SmtModel) (xs G : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) G)))
    (hTrue :
      eo_interprets M
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) G)) true) :
    ∃ ts,
      xs = eoListOfTerms ts ∧
        (∀ t ∈ ts, IsQuantVarTerm t) ∧
        __smtx_model_eval
            (pushChoiceWitnesses M xs (SmtTerm.not (__eo_to_smt G)))
            (SmtTerm.not (__eo_to_smt G)) =
          SmtValue.Boolean true ∧
        model_agrees_on_globals M
          (pushChoiceWitnesses M xs (SmtTerm.not (__eo_to_smt G))) := by
  rcases pushChoiceWitnesses_eval_true_of_not_forall
      M xs G hBool hTrue with
    ⟨ts, hxs, hAll, hEval⟩
  subst xs
  refine ⟨ts, rfl, hAll, hEval, ?_⟩
  exact pushChoiceWitnesses_agrees_on_globals
    M ts (SmtTerm.not (__eo_to_smt G)) hAll

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

private theorem skolemize_valid_case_properties
    (M : SmtModel) (hM : model_total_typed M)
    (x1 : Term)
    (hX1Bool : RuleProofs.eo_has_bool_type x1)
    (hResultTy :
      __eo_typeof (__eo_prog_skolemize (Proof.pf x1)) = Term.Bool) :
    StepRuleProperties M [x1] (__eo_prog_skolemize (Proof.pf x1)) := by
  refine ⟨?_, ?_⟩
  · intro hEvidence
    have hPremTrue : eo_interprets M x1 true :=
      hEvidence x1 (by simp)
    have hProg : __eo_prog_skolemize (Proof.pf x1) ≠ Term.Stuck :=
      term_ne_stuck_of_typeof_bool hResultTy
    rcases skolemize_shape_of_not_stuck x1 hProg with
      ⟨xs, G, hShape, hSetof, hProgEq⟩
    subst x1
    rcases pushChoiceWitnesses_not_forall_package M xs G hX1Bool hPremTrue with
      ⟨ts, hxs, hAll, hWitnessEval, hWitnessAgree⟩
    subst xs
    have hNoDup : List.Nodup ts :=
      eo_list_setof_eoListOfTerms_eq_self_nodup hAll (by
        simpa using hSetof)
    let F :=
      Term.Apply
        (Term.Apply (Term.UOp UserOp.forall) (eoListOfTerms ts)) G
    have hFNe : F ≠ Term.Stuck := by
      simp [F]
    have hSkolemsNe :
        __mk_skolems (eoListOfTerms ts) F (Term.Numeral 0) ≠
          Term.Stuck :=
      mk_skolems_eoListOfTerms_ne_stuck ts F 0 hFNe
    rw [hProgEq]
    change
      eo_interprets M
        (__substitute_simul (Term.Apply (Term.UOp UserOp.not) G)
          (eoListOfTerms ts) (__mk_skolems (eoListOfTerms ts) F
            (Term.Numeral 0))) true
    rw [substitute_simul_not_apply_eoListOfTerms ts G
      (__mk_skolems (eoListOfTerms ts) F (Term.Numeral 0)) hSkolemsNe hAll]
    sorry
  · sorry

theorem cmd_step_skolemize_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.skolemize args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.skolemize args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.skolemize args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.skolemize args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              have hX1Bool :
                  RuleProofs.eo_has_bool_type (__eo_state_proven_nth s n1) :=
                hPremisesBool (__eo_state_proven_nth s n1)
                  (by simp [premiseTermList])
              change StepRuleProperties M [__eo_state_proven_nth s n1]
                (__eo_prog_skolemize
                  (Proof.pf (__eo_state_proven_nth s n1)))
              exact skolemize_valid_case_properties M hM
                (__eo_state_proven_nth s n1) hX1Bool (by
                  simpa using hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
