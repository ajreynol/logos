import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CoreSupport
import Cpc.Proofs.RuleSupport.ContainsAtomicSupport

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

private theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.not) t) =
      SmtTerm.not (__eo_to_smt t) := by
  rfl

private theorem eo_to_smt_or_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) =
      SmtTerm.or (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

private theorem eo_to_smt_and_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

private theorem eo_to_smt_imp_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) =
      SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

private theorem eo_to_smt_xor_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) =
      SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

private theorem eo_to_smt_eq_eq (A B : Term) :
    __eo_to_smt (qeq A B) =
      SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

private theorem eo_to_smt_ite_eq (c t e : Term) :
    __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e) =
      SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e) := by
  rfl

private def quantUnusedFormula (Q x F G : Term) : Term :=
  qeq (qterm Q x F) G

private def qexists (x F : Term) : Term :=
  qterm (Term.UOp UserOp.exists) x F

private def qforall (x F : Term) : Term :=
  qterm (Term.UOp UserOp.forall) x F

private theorem eoSmtVarEnv_ne_stuck
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
    env ≠ Term.Stuck := by
  cases hEnv <;> simp

private theorem eoSmtVarEnv_ne_nil_of_vars_ne_nil
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hVars : vars ≠ []) :
    env ≠ Term.__eo_List_nil := by
  cases hEnv with
  | nil =>
      exact False.elim (hVars rfl)
  | cons _hTail =>
      simp

private theorem eo_eq_bool_of_ne_stuck {x y : Term}
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    ∃ b, __eo_eq x y = Term.Boolean b := by
  cases x <;> cases y <;>
    simp [__eo_eq] at hx hy ⊢

private theorem eoSmtVarEnv_erase_rec_exists :
    ∀ {env : Term} {vars : List SmtVarKey} {z : Term},
      EoSmtVarEnv env vars ->
        z ≠ Term.Stuck ->
          ∃ vars', EoSmtVarEnv (__eo_list_erase_rec env z) vars'
  | _, _, _, EoSmtVarEnv.nil, _hz =>
      by
        exact ⟨[], by simp [__eo_list_erase_rec, EoSmtVarEnv.nil]⟩
  | _, _, z, EoSmtVarEnv.cons (s := s) (T := T) (env := tail) hTail, hz =>
      by
        have hHead :
            Term.Var (Term.String s) T ≠ Term.Stuck := by simp
        rcases eo_eq_bool_of_ne_stuck hHead hz with ⟨b, hEq⟩
        rcases eoSmtVarEnv_erase_rec_exists hTail hz with
          ⟨tailVars, hTailErase⟩
        cases b
        · refine ⟨(s, __eo_to_smt_type T) :: tailVars, ?_⟩
          simpa [__eo_list_erase_rec, hEq, __eo_ite, native_ite,
            native_teq, native_not, SmtEval.native_not]
            using EoSmtVarEnv.cons_mk_apply (s := s) (T := T)
              hTailErase
        · exact ⟨_, by
            simpa [__eo_list_erase_rec, hEq, __eo_ite, native_ite,
              native_teq, native_not, SmtEval.native_not] using hTail⟩

private theorem eoSmtVarEnv_erase_all_rec_exists :
    ∀ {env : Term} {vars : List SmtVarKey} {z : Term},
      EoSmtVarEnv env vars ->
        z ≠ Term.Stuck ->
          ∃ vars', EoSmtVarEnv (__eo_list_erase_all_rec env z) vars'
  | _, _, _, EoSmtVarEnv.nil, _hz =>
      by
        exact ⟨[], by simp [__eo_list_erase_all_rec, EoSmtVarEnv.nil]⟩
  | _, _, z, EoSmtVarEnv.cons (s := s) (T := T) hTail, hz =>
      by
        have hHead :
            Term.Var (Term.String s) T ≠ Term.Stuck := by simp
        rcases eo_eq_bool_of_ne_stuck hz hHead with ⟨b, hEq⟩
        rcases eoSmtVarEnv_erase_all_rec_exists hTail hz with
          ⟨tailVars, hTailErase⟩
        have hTailEraseNe :=
          eoSmtVarEnv_ne_stuck hTailErase
        cases b
        · refine ⟨(s, __eo_to_smt_type T) :: tailVars, ?_⟩
          simpa [__eo_list_erase_all_rec, hEq, __eo_not, native_not,
            __eo_prepend_if, __eo_mk_apply, hz, hHead, hTailEraseNe,
            native_ite, native_teq, native_not, SmtEval.native_not]
            using EoSmtVarEnv.cons_mk_apply (s := s) (T := T)
              hTailErase
        · exact ⟨_, by
            simpa [__eo_list_erase_all_rec, hEq, __eo_not, native_not,
              __eo_prepend_if, __eo_mk_apply, hz, hHead, hTailEraseNe,
              native_ite, native_teq, native_not, SmtEval.native_not]
              using hTailErase⟩

private theorem eoSmtVarEnv_setof_rec_exists :
    ∀ {env : Term} {vars : List SmtVarKey},
      EoSmtVarEnv env vars ->
        ∃ vars', EoSmtVarEnv (__eo_list_setof_rec env) vars'
  | _, _, EoSmtVarEnv.nil =>
      by
        exact ⟨[], by simp [__eo_list_setof_rec, EoSmtVarEnv.nil]⟩
  | _, _, EoSmtVarEnv.cons (s := s) (T := T) hTail =>
      by
        rcases eoSmtVarEnv_setof_rec_exists hTail with
          ⟨tailVars, hTailSet⟩
        have hHead :
            Term.Var (Term.String s) T ≠ Term.Stuck := by simp
        rcases eoSmtVarEnv_erase_all_rec_exists hTailSet hHead with
          ⟨erasedVars, hErased⟩
        refine ⟨(s, __eo_to_smt_type T) :: erasedVars, ?_⟩
        simpa [__eo_list_setof_rec] using
          EoSmtVarEnv.cons_mk_apply (s := s) (T := T) hErased

private theorem eoSmtVarEnv_setof_exists
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
    ∃ vars',
      EoSmtVarEnv (__eo_list_setof Term.__eo_List_cons env) vars' := by
  rcases eoSmtVarEnv_setof_rec_exists hEnv with ⟨vars', hSet⟩
  exact ⟨vars', by
    simpa [__eo_list_setof, __eo_requires, EoSmtVarEnv.is_list hEnv,
      native_ite, native_teq, native_not, SmtEval.native_not] using hSet⟩

private theorem eoSmtVarEnv_diff_rec_exists :
    ∀ {env z : Term} {vars zVars : List SmtVarKey},
      EoSmtVarEnv env vars ->
        EoSmtVarEnv z zVars ->
          ∃ vars', EoSmtVarEnv (__eo_list_diff_rec env z) vars'
  | _, _, _, _, EoSmtVarEnv.nil, hZ =>
      by
        exact ⟨[], by
          cases hZ <;> simpa [__eo_list_diff_rec] using EoSmtVarEnv.nil⟩
  | _, z, _, zVars,
      EoSmtVarEnv.cons (s := s) (T := T) (env := tail) hTail, hZ =>
      by
        have hHead :
            Term.Var (Term.String s) T ≠ Term.Stuck := by simp
        have hZNe : z ≠ Term.Stuck :=
          eoSmtVarEnv_ne_stuck hZ
        rcases eoSmtVarEnv_erase_rec_exists hZ hHead with
          ⟨erasedVars, hErased⟩
        have hErasedNe :
            __eo_list_erase_rec z (Term.Var (Term.String s) T) ≠
              Term.Stuck :=
          eoSmtVarEnv_ne_stuck hErased
        rcases eoSmtVarEnv_diff_rec_exists hTail hErased with
          ⟨tailVars, hTailDiff⟩
        have hTailDiffNe :=
          eoSmtVarEnv_ne_stuck hTailDiff
        rcases eo_eq_bool_of_ne_stuck hErasedNe hZNe with
          ⟨b, hEq⟩
        cases b
        · exact ⟨_, by
            simpa [__eo_list_diff_rec, hEq, __eo_prepend_if,
              __eo_mk_apply, hHead, hZNe, hErasedNe, hTailDiffNe,
              native_ite, native_teq, native_not, SmtEval.native_not]
              using hTailDiff⟩
        · refine ⟨(s, __eo_to_smt_type T) :: tailVars, ?_⟩
          simpa [__eo_list_diff_rec, hEq, __eo_prepend_if,
            __eo_mk_apply, hHead, hZNe, hErasedNe, hTailDiffNe, native_ite,
            native_teq, native_not, SmtEval.native_not]
            using EoSmtVarEnv.cons_mk_apply (s := s) (T := T)
              hTailDiff

private theorem eoSmtVarEnv_diff_exists
    {env z : Term} {vars zVars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) (hZ : EoSmtVarEnv z zVars) :
    ∃ vars',
      EoSmtVarEnv (__eo_list_diff Term.__eo_List_cons env z) vars' := by
  rcases eoSmtVarEnv_diff_rec_exists hEnv hZ with ⟨vars', hDiff⟩
  exact ⟨vars', by
    simpa [__eo_list_diff, __eo_requires, EoSmtVarEnv.is_list hEnv,
      EoSmtVarEnv.is_list hZ, native_ite, native_teq, native_not,
      SmtEval.native_not] using hDiff⟩

private theorem eo_list_concat_ne_nil_of_left_env_ne_nil
    {left right : Term} {leftVars rightVars : List SmtVarKey}
    (hLeft : EoSmtVarEnv left leftVars)
    (hRight : EoSmtVarEnv right rightVars)
    (hLeftNe : left ≠ Term.__eo_List_nil) :
    __eo_list_concat Term.__eo_List_cons left right ≠
      Term.__eo_List_nil := by
  cases hLeft with
  | nil =>
      exact False.elim (hLeftNe rfl)
  | cons hTail =>
      rename_i s T tail tailVars
      have hConcat :
          EoSmtVarEnv
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply
                (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) tail)
              right)
            (((s, __eo_to_smt_type T) :: tailVars) ++ rightVars) :=
        EoSmtVarEnv.concat (EoSmtVarEnv.cons hTail) hRight
      exact eoSmtVarEnv_ne_nil_of_vars_ne_nil hConcat (by simp)

private theorem eo_list_concat_rec_nil_right_eq
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
    __eo_list_concat_rec env Term.__eo_List_nil = env := by
  cases hEnv with
  | nil =>
      simp [__eo_list_concat_rec]
  | cons hTail =>
      rename_i s T tail tailVars
      have hTailEq := eo_list_concat_rec_nil_right_eq hTail
      simp [__eo_list_concat_rec, hTailEq, __eo_mk_apply,
        eoSmtVarEnv_ne_stuck hTail]

private theorem eo_list_concat_nil_right_eq
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
    __eo_list_concat Term.__eo_List_cons env Term.__eo_List_nil = env := by
  have hEnvList := hEnv.is_list
  have hNilList : EoSmtVarEnv Term.__eo_List_nil ([] : List SmtVarKey) :=
    EoSmtVarEnv.nil
  simpa [__eo_list_concat, __eo_requires, hEnvList, hNilList.is_list,
    native_ite, native_teq, native_not] using
      eo_list_concat_rec_nil_right_eq hEnv

private def eoListOfTerms : List Term -> Term
  | [] => Term.__eo_List_nil
  | x :: xs => Term.Apply (Term.Apply Term.__eo_List_cons x) (eoListOfTerms xs)

private def IsQuantVarTerm : Term -> Prop
  | Term.Var (Term.String _) _ => True
  | _ => False

private def quantTermBinder : Term -> SmtVarKey
  | Term.Var (Term.String s) T => (s, __eo_to_smt_type T)
  | _ => (native_string_lit "", SmtType.None)

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
          rcases h with ⟨hHead, hTail⟩
          subst y
          rw [ih hTail]

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

private theorem eo_list_concat_rec_eoListOfTerms_eq
    (xs ys : List Term) :
    __eo_list_concat_rec (eoListOfTerms xs) (eoListOfTerms ys) =
      eoListOfTerms (xs ++ ys) := by
  induction xs with
  | nil =>
      cases ys <;> simp [eoListOfTerms, __eo_list_concat_rec]
  | cons x xs ih =>
      simp [eoListOfTerms, __eo_list_concat_rec, ih, __eo_mk_apply,
        eoListOfTerms_ne_stuck]

private theorem eo_list_concat_eoListOfTerms_eq
    (xs ys : List Term) :
    __eo_list_concat Term.__eo_List_cons (eoListOfTerms xs)
        (eoListOfTerms ys) =
      eoListOfTerms (xs ++ ys) := by
  simpa [__eo_list_concat, eoListOfTerms_is_list_true, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not]
    using eo_list_concat_rec_eoListOfTerms_eq xs ys

private theorem eo_get_elements_rec_eoListOfTerms (xs : List Term) :
    __eo_get_elements_rec (eoListOfTerms xs) = eoListOfTerms xs := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, __eo_get_elements_rec]
  | cons _ xs ih =>
      simp [eoListOfTerms, __eo_get_elements_rec, __eo_mk_apply,
        eoListOfTerms_ne_stuck, ih]

private theorem eo_list_erase_rec_eoListOfTerms_eq
    {xs : List Term} {e : Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (he : e ≠ Term.Stuck) :
    __eo_list_erase_rec (eoListOfTerms xs) e =
      eoListOfTerms (xs.erase e) := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, __eo_list_erase_rec]
  | cons x xs ih =>
      have hx : x ≠ Term.Stuck := hxs x (by simp)
      have htail : ∀ t ∈ xs, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (by simp [ht])
      by_cases hxe : x = e
      · subst e
        simp [eoListOfTerms, __eo_list_erase_rec, __eo_ite,
          eoEq_true_of_eq_ne_stuck hx, List.erase_cons_head,
          native_ite, native_teq]
      · have hEqTerm : __eo_eq x e = Term.Boolean false :=
          eoEq_false_of_ne_nonstuck hxe hx he
        have hTailEq := ih htail
        have hBeq : ¬(x == e) = true := by
          simp [hxe]
        rw [List.erase_cons_tail hBeq]
        simp [eoListOfTerms, __eo_list_erase_rec, __eo_ite, __eo_mk_apply,
          hEqTerm, hTailEq, eoListOfTerms_ne_stuck, native_ite, native_teq]

private theorem eo_list_erase_rec_eoList_mem_of_changed
    {xs : List Term} {e : Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (he : e ≠ Term.Stuck) :
    __eo_not (__eo_eq (__eo_list_erase_rec (eoListOfTerms xs) e)
        (eoListOfTerms xs)) = Term.Boolean true ->
    e ∈ xs := by
  intro hChanged
  by_cases hMem : e ∈ xs
  · exact hMem
  · have hEraseList : xs.erase e = xs := (List.erase_eq_self_iff).2 hMem
    have hEraseTerm := eo_list_erase_rec_eoListOfTerms_eq hxs he
    rw [hEraseList] at hEraseTerm
    have hEqTerm :
        __eo_eq (__eo_list_erase_rec (eoListOfTerms xs) e)
            (eoListOfTerms xs) = Term.Boolean true := by
      rw [hEraseTerm]
      exact eoEq_true_of_eq_ne_stuck (eoListOfTerms_ne_stuck xs)
    simp [__eo_not, hEqTerm, native_not] at hChanged

private theorem raw_minclude_rec_eq_not_flag_true
    {y z orig : Term} :
    y ≠ Term.Stuck ->
    z ≠ Term.Stuck ->
    orig ≠ Term.Stuck ->
    __eo_list_minclude_rec y z (__eo_not (__eo_eq y orig)) =
      Term.Boolean true ->
    __eo_not (__eo_eq y orig) = Term.Boolean true := by
  intro hY hZ hOrig hIncl
  by_cases hEq : y = orig
  · subst orig
    have hEqTerm : __eo_eq y y = Term.Boolean true :=
      eoEq_true_of_eq_ne_stuck hY
    have hFlag :
        __eo_not (__eo_eq y y) = Term.Boolean false := by
      simp [__eo_not, hEqTerm, native_not]
    rw [hFlag] at hIncl
    cases y <;> cases z <;> simp [__eo_list_minclude_rec] at hIncl hY hZ
  · have hEqTerm : __eo_eq y orig = Term.Boolean false :=
      eoEq_false_of_ne_nonstuck hEq hY hOrig
    simp [__eo_not, hEqTerm, native_not]

private theorem raw_minclude_rec_eoList_perm_append
    {xs ys : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hys : ∀ t ∈ ys, t ≠ Term.Stuck) :
    __eo_list_minclude_rec (eoListOfTerms xs) (eoListOfTerms ys)
        (Term.Boolean true) = Term.Boolean true ->
    ∃ zs, xs.Perm (ys ++ zs) := by
  induction ys generalizing xs with
  | nil =>
      intro _hIncl
      exact ⟨xs, by simp⟩
  | cons y ys ih =>
      intro hIncl
      have hy : y ≠ Term.Stuck := hys y (by simp)
      have hysTail : ∀ t ∈ ys, t ≠ Term.Stuck := by
        intro t ht
        exact hys t (by simp [ht])
      let erased := __eo_list_erase_rec (eoListOfTerms xs) y
      have hInclRaw :
          __eo_list_minclude_rec erased (eoListOfTerms ys)
              (__eo_not (__eo_eq erased (eoListOfTerms xs))) =
            Term.Boolean true := by
        simpa [eoListOfTerms, __eo_list_minclude_rec, erased,
          eoListOfTerms_ne_stuck] using hIncl
      have hEraseEq : erased = eoListOfTerms (xs.erase y) := by
        simpa [erased] using eo_list_erase_rec_eoListOfTerms_eq hxs hy
      have hErasedNe : erased ≠ Term.Stuck := by
        rw [hEraseEq]
        exact eoListOfTerms_ne_stuck (xs.erase y)
      have hFlag :
          __eo_not (__eo_eq erased (eoListOfTerms xs)) =
            Term.Boolean true :=
        raw_minclude_rec_eq_not_flag_true hErasedNe
          (eoListOfTerms_ne_stuck ys) (eoListOfTerms_ne_stuck xs) hInclRaw
      have hTailIncl :
          __eo_list_minclude_rec (eoListOfTerms (xs.erase y))
              (eoListOfTerms ys) (Term.Boolean true) = Term.Boolean true := by
        rw [hFlag] at hInclRaw
        simpa [hEraseEq] using hInclRaw
      have hyMem : y ∈ xs := by
        apply eo_list_erase_rec_eoList_mem_of_changed hxs hy
        simpa [erased] using hFlag
      have hEraseNonStuck : ∀ t ∈ xs.erase y, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (List.mem_of_mem_erase ht)
      rcases ih hEraseNonStuck hysTail hTailIncl with ⟨zs, hPermTail⟩
      exact ⟨zs,
        (List.perm_cons_erase hyMem).trans (List.Perm.cons y hPermTail)⟩

private theorem minclude_eoList_perm_append
    {xs ys : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hys : ∀ t ∈ ys, t ≠ Term.Stuck) :
    __eo_list_minclude Term.__eo_List_cons (eoListOfTerms xs)
        (eoListOfTerms ys) = Term.Boolean true ->
    ∃ zs, xs.Perm (ys ++ zs) := by
  intro hIncl
  apply raw_minclude_rec_eoList_perm_append hxs hys
  simpa [__eo_list_minclude, eoListOfTerms_is_list_true,
    eo_get_elements_rec_eoListOfTerms, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hIncl

private def termListDiff : List Term -> List Term -> List Term
  | [], _ => []
  | x :: xs, ys =>
      let ys' := ys.erase x
      if ys' = ys then x :: termListDiff xs ys'
      else termListDiff xs ys'

private theorem termListDiff_mem_left :
    ∀ {xs ys : List Term} {t : Term},
      t ∈ termListDiff xs ys -> t ∈ xs
  | [], _, _, h => by simp [termListDiff] at h
  | x :: xs, ys, t, h => by
      by_cases hSame : ys.erase x = ys
      · simp [termListDiff, hSame] at h
        rcases h with h | h
        · subst t
          simp
        · exact List.mem_cons_of_mem x (termListDiff_mem_left h)
      · simp [termListDiff, hSame] at h
        exact List.mem_cons_of_mem x (termListDiff_mem_left h)

private theorem eo_list_diff_rec_eoListOfTerms_eq
    {xs ys : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hys : ∀ t ∈ ys, t ≠ Term.Stuck) :
    __eo_list_diff_rec (eoListOfTerms xs) (eoListOfTerms ys) =
      eoListOfTerms (termListDiff xs ys) := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp [eoListOfTerms, termListDiff, __eo_list_diff_rec]
  | cons x xs ih =>
      have hx : x ≠ Term.Stuck := hxs x (by simp)
      have hxsTail : ∀ t ∈ xs, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (by simp [ht])
      have hEraseEq :
          __eo_list_erase_rec (eoListOfTerms ys) x =
            eoListOfTerms (ys.erase x) :=
        eo_list_erase_rec_eoListOfTerms_eq hys hx
      have hEraseNonStuck :
          ∀ t ∈ ys.erase x, t ≠ Term.Stuck := by
        intro t ht
        exact hys t (List.mem_of_mem_erase ht)
      have hTailEq := ih hxsTail hEraseNonStuck
      have hDiffStep :
          __eo_list_diff_rec (eoListOfTerms (x :: xs))
              (eoListOfTerms ys) =
            __eo_prepend_if
              (__eo_eq (__eo_list_erase_rec (eoListOfTerms ys) x)
                (eoListOfTerms ys))
              Term.__eo_List_cons x
              (__eo_list_diff_rec (eoListOfTerms xs)
                (__eo_list_erase_rec (eoListOfTerms ys) x)) := by
        cases ys <;> simp [eoListOfTerms, __eo_list_diff_rec]
      by_cases hSame : ys.erase x = ys
      · have hEqTerm :
            __eo_eq (eoListOfTerms (ys.erase x)) (eoListOfTerms ys) =
              Term.Boolean true := by
          rw [hSame]
          exact eoEq_true_of_eq_ne_stuck (eoListOfTerms_ne_stuck ys)
        rw [hDiffStep, hEraseEq, hEqTerm, hTailEq]
        simp [eoListOfTerms, termListDiff, hSame, __eo_prepend_if,
          eoListOfTerms_ne_stuck]
      · have hListNe : eoListOfTerms (ys.erase x) ≠ eoListOfTerms ys := by
          intro hEq
          exact hSame (eoListOfTerms_inj hEq)
        have hEqTerm :
            __eo_eq (eoListOfTerms (ys.erase x)) (eoListOfTerms ys) =
              Term.Boolean false :=
          eoEq_false_of_ne_nonstuck hListNe
            (eoListOfTerms_ne_stuck (ys.erase x))
            (eoListOfTerms_ne_stuck ys)
        rw [hDiffStep, hEraseEq, hEqTerm, hTailEq]
        simp [termListDiff, hSame, __eo_prepend_if,
          eoListOfTerms_ne_stuck]

private theorem eo_list_diff_eoListOfTerms_eq
    {xs ys : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hys : ∀ t ∈ ys, t ≠ Term.Stuck) :
    __eo_list_diff Term.__eo_List_cons (eoListOfTerms xs)
        (eoListOfTerms ys) =
      eoListOfTerms (termListDiff xs ys) := by
  simpa [__eo_list_diff, eoListOfTerms_is_list_true, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not]
    using eo_list_diff_rec_eoListOfTerms_eq hxs hys

private theorem termListDiff_nil_right (xs : List Term) :
    termListDiff xs [] = xs := by
  induction xs with
  | nil =>
      simp [termListDiff]
  | cons x xs ih =>
      simp [termListDiff, ih]

private theorem termListDiff_cons_right_eq_erase :
    ∀ {xs ys : List Term} {y : Term},
      y ∈ xs ->
        termListDiff xs (y :: ys) = termListDiff (xs.erase y) ys
  | [], _, _, h => by simp at h
  | x :: xs, ys, y, hMem => by
      by_cases hxy : x = y
      · subst x
        simp [termListDiff]
      · have hyTail : y ∈ xs := by
          have hMem' : y = x ∨ y ∈ xs := by
            simpa using hMem
          rcases hMem' with hHead | hTail
          · exact False.elim (hxy hHead.symm)
          · exact hTail
        have ih :
            termListDiff xs (y :: ys) =
              termListDiff (xs.erase y) ys :=
          termListDiff_cons_right_eq_erase hyTail
        have ihErase :
            termListDiff xs (y :: ys.erase x) =
              termListDiff (xs.erase y) (ys.erase x) :=
          termListDiff_cons_right_eq_erase (xs := xs)
            (ys := ys.erase x) hyTail
        have hyx : y ≠ x := by
          intro h
          exact hxy h.symm
        have hEraseConsYX : (y :: ys).erase x = y :: ys.erase x := by
          have hBeq : ¬(y == x) = true := by
            simp [hyx]
          simpa using List.erase_cons_tail hBeq
        have hEraseConsXY : (x :: xs).erase y = x :: xs.erase y := by
          have hBeq : ¬(x == y) = true := by
            simp [hxy]
          simpa using List.erase_cons_tail hBeq
        by_cases hSame : ys.erase x = ys
        · simp [termListDiff, hEraseConsYX, hEraseConsXY, hSame, ih]
        · simp [termListDiff, hEraseConsYX, hEraseConsXY, hSame, ihErase]

private theorem raw_minclude_rec_eoList_perm_diff
    {xs ys : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hys : ∀ t ∈ ys, t ≠ Term.Stuck) :
    __eo_list_minclude_rec (eoListOfTerms xs) (eoListOfTerms ys)
        (Term.Boolean true) = Term.Boolean true ->
    xs.Perm (ys ++ termListDiff xs ys) := by
  induction ys generalizing xs with
  | nil =>
      intro _hIncl
      simpa [termListDiff_nil_right xs]
  | cons y ys ih =>
      intro hIncl
      have hy : y ≠ Term.Stuck := hys y (by simp)
      have hysTail : ∀ t ∈ ys, t ≠ Term.Stuck := by
        intro t ht
        exact hys t (by simp [ht])
      let erased := __eo_list_erase_rec (eoListOfTerms xs) y
      have hInclRaw :
          __eo_list_minclude_rec erased (eoListOfTerms ys)
              (__eo_not (__eo_eq erased (eoListOfTerms xs))) =
            Term.Boolean true := by
        simpa [eoListOfTerms, __eo_list_minclude_rec, erased,
          eoListOfTerms_ne_stuck] using hIncl
      have hEraseEq : erased = eoListOfTerms (xs.erase y) := by
        simpa [erased] using eo_list_erase_rec_eoListOfTerms_eq hxs hy
      have hErasedNe : erased ≠ Term.Stuck := by
        rw [hEraseEq]
        exact eoListOfTerms_ne_stuck (xs.erase y)
      have hFlag :
          __eo_not (__eo_eq erased (eoListOfTerms xs)) =
            Term.Boolean true :=
        raw_minclude_rec_eq_not_flag_true hErasedNe
          (eoListOfTerms_ne_stuck ys) (eoListOfTerms_ne_stuck xs) hInclRaw
      have hTailIncl :
          __eo_list_minclude_rec (eoListOfTerms (xs.erase y))
              (eoListOfTerms ys) (Term.Boolean true) = Term.Boolean true := by
        rw [hFlag] at hInclRaw
        simpa [hEraseEq] using hInclRaw
      have hyMem : y ∈ xs := by
        apply eo_list_erase_rec_eoList_mem_of_changed hxs hy
        simpa [erased] using hFlag
      have hEraseNonStuck : ∀ t ∈ xs.erase y, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (List.mem_of_mem_erase ht)
      have hPermTail :
          (xs.erase y).Perm
            (ys ++ termListDiff (xs.erase y) ys) :=
        ih hEraseNonStuck hysTail hTailIncl
      have hDiff :
          termListDiff xs (y :: ys) =
            termListDiff (xs.erase y) ys :=
        termListDiff_cons_right_eq_erase hyMem
      exact
        (List.perm_cons_erase hyMem).trans
          (by simpa [List.cons_append, hDiff] using
            List.Perm.cons y hPermTail)

private theorem minclude_eoList_perm_diff
    {xs ys : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hys : ∀ t ∈ ys, t ≠ Term.Stuck) :
    __eo_list_minclude Term.__eo_List_cons (eoListOfTerms xs)
        (eoListOfTerms ys) = Term.Boolean true ->
    xs.Perm (ys ++ termListDiff xs ys) := by
  intro hIncl
  apply raw_minclude_rec_eoList_perm_diff hxs hys
  simpa [__eo_list_minclude, eoListOfTerms_is_list_true,
    eo_get_elements_rec_eoListOfTerms, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hIncl

private def termListEraseAll : List Term -> Term -> List Term
  | [], _ => []
  | x :: xs, z =>
      if z = x then termListEraseAll xs z
      else x :: termListEraseAll xs z

private def termListSetOf : List Term -> List Term
  | [] => []
  | x :: xs => x :: termListEraseAll (termListSetOf xs) x

private theorem termListEraseAll_mem :
    ∀ {xs : List Term} {z t : Term},
      t ∈ termListEraseAll xs z ↔ t ∈ xs ∧ t ≠ z
  | [], _, _ => by simp [termListEraseAll]
  | x :: xs, z, t => by
      by_cases hzx : z = x
      · subst z
        simp [termListEraseAll]
        constructor
        · intro h
          have h' := (termListEraseAll_mem (xs := xs) (z := x)
            (t := t)).1 h
          exact ⟨Or.inr h'.1, h'.2⟩
        · intro h
          rcases h with ⟨hMem, hNe⟩
          rcases hMem with hHead | hTail
          · exact False.elim (hNe hHead)
          · exact (termListEraseAll_mem (xs := xs) (z := x)
              (t := t)).2 ⟨hTail, hNe⟩
      · simp [termListEraseAll, hzx, termListEraseAll_mem]
        constructor
        · intro h
          rcases h with h | h
          · subst t
            exact ⟨Or.inl rfl, by
              intro hxz
              exact hzx hxz.symm⟩
          · exact ⟨Or.inr h.1, h.2⟩
        · intro h
          rcases h with ⟨hMem, hNe⟩
          rcases hMem with hHead | hTail
          · subst t
            exact Or.inl rfl
          · exact Or.inr ⟨hTail, hNe⟩

private theorem termListSetOf_mem :
    ∀ {xs : List Term} {t : Term},
      t ∈ termListSetOf xs ↔ t ∈ xs
  | [], _ => by simp [termListSetOf]
  | x :: xs, t => by
      simp [termListSetOf, termListEraseAll_mem, termListSetOf_mem]
      constructor
      · intro h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      · intro h
        rcases h with h | h
        · exact Or.inl h
        · by_cases htx : t = x
          · exact Or.inl htx
          · exact Or.inr ⟨h, htx⟩

private theorem termListSetOf_mem_left
    {xs : List Term} {t : Term} :
    t ∈ termListSetOf xs -> t ∈ xs :=
  (termListSetOf_mem).1

private theorem termListEraseAll_not_mem_self
    {xs : List Term} {z : Term} :
    z ∉ termListEraseAll xs z := by
  intro hMem
  exact ((termListEraseAll_mem (xs := xs) (z := z) (t := z)).1
    hMem).2 rfl

private theorem termListEraseAll_nodup :
    ∀ {xs : List Term} {z : Term},
      xs.Nodup -> (termListEraseAll xs z).Nodup
  | [], _z, _h => by
      simp [termListEraseAll]
  | x :: xs, z, hNodup => by
      rcases List.nodup_cons.mp hNodup with ⟨hxNotMem, hTailNodup⟩
      by_cases hzx : z = x
      · subst z
        simpa [termListEraseAll] using
          termListEraseAll_nodup (xs := xs) (z := x) hTailNodup
      · simp [termListEraseAll, hzx]
        constructor
        · intro hMem
          exact hxNotMem
            ((termListEraseAll_mem (xs := xs) (z := z) (t := x)).1
              hMem).1
        · exact termListEraseAll_nodup (xs := xs) (z := z)
            hTailNodup

private theorem termListSetOf_nodup :
    ∀ {xs : List Term}, (termListSetOf xs).Nodup
  | [] => by
      simp [termListSetOf]
  | x :: xs => by
      simp [termListSetOf]
      exact ⟨termListEraseAll_not_mem_self,
        termListEraseAll_nodup termListSetOf_nodup⟩

private theorem termListDiff_not_mem_right_of_nodup_left :
    ∀ {xs ys : List Term} {t : Term},
      xs.Nodup ->
        t ∈ termListDiff xs ys ->
          t ∉ ys
  | [], _ys, _t, _hNodup, hMem => by
      simp [termListDiff] at hMem
  | x :: xs, ys, t, hNodup, hMem => by
      rcases List.nodup_cons.mp hNodup with ⟨hxNotMem, hTailNodup⟩
      by_cases hSame : ys.erase x = ys
      · simp [termListDiff, hSame] at hMem
        rcases hMem with hHead | hTail
        · subst t
          exact (List.erase_eq_self_iff).1 hSame
        · exact termListDiff_not_mem_right_of_nodup_left
            hTailNodup hTail
      · simp [termListDiff, hSame] at hMem
        intro hInYs
        have htInXs : t ∈ xs :=
          termListDiff_mem_left hMem
        have htx : t ≠ x := by
          intro htx
          subst t
          exact hxNotMem htInXs
        have hInErase : t ∈ ys.erase x :=
          (List.mem_erase_of_ne htx).2 hInYs
        exact termListDiff_not_mem_right_of_nodup_left
          hTailNodup hMem hInErase

private theorem termListSetOf_ne_nil_of_ne_nil :
    ∀ {xs : List Term}, xs ≠ [] -> termListSetOf xs ≠ []
  | [], h => by
      exact False.elim (h rfl)
  | _x :: _xs, _h => by
      simp [termListSetOf]

private theorem eo_list_erase_all_rec_eoListOfTerms_eq
    {xs : List Term} {z : Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hz : z ≠ Term.Stuck) :
    __eo_list_erase_all_rec (eoListOfTerms xs) z =
      eoListOfTerms (termListEraseAll xs z) := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, termListEraseAll, __eo_list_erase_all_rec]
  | cons x xs ih =>
      have hx : x ≠ Term.Stuck := hxs x (by simp)
      have hxsTail : ∀ t ∈ xs, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (by simp [ht])
      have hTailEq := ih hxsTail
      have hEraseStep :
          __eo_list_erase_all_rec (eoListOfTerms (x :: xs)) z =
            __eo_prepend_if (__eo_not (__eo_eq z x))
              Term.__eo_List_cons x
              (__eo_list_erase_all_rec (eoListOfTerms xs) z) := by
        simp [eoListOfTerms, __eo_list_erase_all_rec]
      by_cases hzx : z = x
      · subst z
        have hEqTerm : __eo_eq x x = Term.Boolean true :=
          eoEq_true_of_eq_ne_stuck hx
        rw [hEraseStep, hEqTerm, hTailEq]
        simp [termListEraseAll, __eo_not, __eo_prepend_if,
          eoListOfTerms_ne_stuck, native_not]
      · have hEqTerm : __eo_eq z x = Term.Boolean false :=
          eoEq_false_of_ne_nonstuck hzx hz hx
        rw [hEraseStep, hEqTerm, hTailEq]
        simp [eoListOfTerms, termListEraseAll, hzx, __eo_prepend_if,
          __eo_not, eoListOfTerms_ne_stuck, native_not]

private theorem eo_list_setof_rec_eoListOfTerms_eq
    {xs : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck) :
    __eo_list_setof_rec (eoListOfTerms xs) =
      eoListOfTerms (termListSetOf xs) := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, termListSetOf, __eo_list_setof_rec]
  | cons x xs ih =>
      have hx : x ≠ Term.Stuck := hxs x (by simp)
      have hxsTail : ∀ t ∈ xs, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (by simp [ht])
      have hSetTailNonStuck :
          ∀ t ∈ termListSetOf xs, t ≠ Term.Stuck := by
        intro t ht
        exact hxsTail t (termListSetOf_mem_left ht)
      have hEraseEq :
          __eo_list_erase_all_rec
              (eoListOfTerms (termListSetOf xs)) x =
            eoListOfTerms (termListEraseAll (termListSetOf xs) x) :=
        eo_list_erase_all_rec_eoListOfTerms_eq hSetTailNonStuck hx
      have hSetTailEq := ih hxsTail
      rw [show
          __eo_list_setof_rec (eoListOfTerms (x :: xs)) =
            __eo_mk_apply (Term.Apply Term.__eo_List_cons x)
              (__eo_list_erase_all_rec
                (__eo_list_setof_rec (eoListOfTerms xs)) x) by
          simp [eoListOfTerms, __eo_list_setof_rec]]
      rw [hSetTailEq, hEraseEq]
      simp [eoListOfTerms, termListSetOf, __eo_mk_apply,
        eoListOfTerms_ne_stuck]

private theorem eo_list_setof_eoListOfTerms_eq
    {xs : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck) :
    __eo_list_setof Term.__eo_List_cons (eoListOfTerms xs) =
      eoListOfTerms (termListSetOf xs) := by
  simpa [__eo_list_setof, eoListOfTerms_is_list_true, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not]
    using eo_list_setof_rec_eoListOfTerms_eq hxs

private theorem eoListOfTerms_termMem_iff :
    ∀ {ts : List Term} {z : Term},
      EoSmtVarEnvTermMem z (eoListOfTerms ts) ↔ z ∈ ts
  | [], _ => by simp [eoListOfTerms, EoSmtVarEnvTermMem]
  | t :: ts, z => by
      simp [eoListOfTerms, EoSmtVarEnvTermMem,
        eoListOfTerms_termMem_iff]
      constructor
      · intro h
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
      · intro h
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr h

private theorem eoSmtVarEnv_as_eoListOfTerms
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
    ∃ ts,
      env = eoListOfTerms ts ∧
      vars = ts.map quantTermBinder ∧
      ∀ t ∈ ts, IsQuantVarTerm t := by
  induction hEnv with
  | nil =>
      exact ⟨[], rfl, rfl, by simp⟩
  | cons hTail ih =>
      rename_i s T tail varsTail
      rcases ih with ⟨ts, hTailEq, hVarsEq, hAll⟩
      refine
        ⟨Term.Var (Term.String s) T :: ts, ?_, ?_, ?_⟩
      · simp [eoListOfTerms, hTailEq]
      · simp [quantTermBinder, hVarsEq]
      · intro t ht
        simp at ht
        rcases ht with ht | ht
        · subst t
          simp [IsQuantVarTerm]
        · exact hAll t ht

private theorem quantVarTerm_ne_stuck {t : Term} :
    IsQuantVarTerm t -> t ≠ Term.Stuck := by
  cases t <;> simp [IsQuantVarTerm]

private theorem eoSmtVarEnv_of_eoListOfTerms
    {ts : List Term}
    (hAll : ∀ t ∈ ts, IsQuantVarTerm t) :
    EoSmtVarEnv (eoListOfTerms ts) (ts.map quantTermBinder) := by
  induction ts with
  | nil =>
      simpa [eoListOfTerms] using EoSmtVarEnv.nil
  | cons t ts ih =>
      have ht : IsQuantVarTerm t := hAll t (by simp)
      have hTail : ∀ u ∈ ts, IsQuantVarTerm u := by
        intro u hu
        exact hAll u (by simp [hu])
      cases t <;> simp [IsQuantVarTerm] at ht
      case Var name T =>
        cases name <;> simp at ht
        case String s =>
          simpa [eoListOfTerms, quantTermBinder, __eo_mk_apply,
            eoListOfTerms_ne_stuck] using
              EoSmtVarEnv.cons_mk_apply (s := s) (T := T)
                (ih hTail)

private theorem termListDiff_quant_terms
    {xs ys : List Term}
    (hAll : ∀ t ∈ xs, IsQuantVarTerm t) :
    ∀ t ∈ termListDiff xs ys, IsQuantVarTerm t := by
  intro t ht
  exact hAll t (termListDiff_mem_left ht)

private theorem termListSetOf_quant_terms
    {xs : List Term}
    (hAll : ∀ t ∈ xs, IsQuantVarTerm t) :
    ∀ t ∈ termListSetOf xs, IsQuantVarTerm t := by
  intro t ht
  exact hAll t ((termListSetOf_mem).1 ht)

private theorem eoSmtVarEnv_diff_eoListOfTerms
    {xs ys : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hys : ∀ t ∈ ys, t ≠ Term.Stuck)
    (hAll : ∀ t ∈ xs, IsQuantVarTerm t) :
    EoSmtVarEnv
      (__eo_list_diff Term.__eo_List_cons (eoListOfTerms xs)
        (eoListOfTerms ys))
      ((termListDiff xs ys).map quantTermBinder) := by
  rw [eo_list_diff_eoListOfTerms_eq hxs hys]
  exact eoSmtVarEnv_of_eoListOfTerms (termListDiff_quant_terms hAll)

private theorem eoSmtVarEnv_setof_eoListOfTerms
    {xs : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hAll : ∀ t ∈ xs, IsQuantVarTerm t) :
    EoSmtVarEnv
      (__eo_list_setof Term.__eo_List_cons (eoListOfTerms xs))
      ((termListSetOf xs).map quantTermBinder) := by
  rw [eo_list_setof_eoListOfTerms_eq hxs]
  exact eoSmtVarEnv_of_eoListOfTerms (termListSetOf_quant_terms hAll)

private theorem eoSmtVarEnvTermMem_setof_of_mem
    {env : Term} {vars : List SmtVarKey} {z : Term}
    (hEnv : EoSmtVarEnv env vars)
    (hMem : EoSmtVarEnvTermMem z env) :
    EoSmtVarEnvTermMem z
      (__eo_list_setof Term.__eo_List_cons env) := by
  rcases eoSmtVarEnv_as_eoListOfTerms hEnv with
    ⟨ts, hEnvEq, _hVarsEq, hAll⟩
  subst env
  have hStuck : ∀ t ∈ ts, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hAll t ht)
  rw [eo_list_setof_eoListOfTerms_eq hStuck]
  exact (eoListOfTerms_termMem_iff).2
    ((termListSetOf_mem).2 ((eoListOfTerms_termMem_iff).1 hMem))

private theorem eoSmtVarEnvTermMem_concat_right
    {left right : Term} {leftVars rightVars : List SmtVarKey} {z : Term}
    (hLeft : EoSmtVarEnv left leftVars)
    (hRight : EoSmtVarEnv right rightVars)
    (hMem : EoSmtVarEnvTermMem z right) :
    EoSmtVarEnvTermMem z
      (__eo_list_concat Term.__eo_List_cons left right) := by
  rcases eoSmtVarEnv_as_eoListOfTerms hLeft with
    ⟨leftTerms, hLeftEq, _hLeftVars, _hLeftAll⟩
  rcases eoSmtVarEnv_as_eoListOfTerms hRight with
    ⟨rightTerms, hRightEq, _hRightVars, _hRightAll⟩
  subst left
  subst right
  rw [eo_list_concat_eoListOfTerms_eq]
  exact (eoListOfTerms_termMem_iff).2
    (List.mem_append.2
      (Or.inr ((eoListOfTerms_termMem_iff).1 hMem)))

private theorem eoSmtVarEnvTermMem_diff_setof_not_right
    {x y z : Term} {xVars yVars : List SmtVarKey}
    (hX : EoSmtVarEnv x xVars)
    (hY : EoSmtVarEnv y yVars)
    (hMem :
      EoSmtVarEnvTermMem z
        (__eo_list_diff Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y)) :
    ¬ EoSmtVarEnvTermMem z y := by
  rcases eoSmtVarEnv_as_eoListOfTerms hX with
    ⟨xTerms, hXEq, _hXVars, hXAll⟩
  rcases eoSmtVarEnv_as_eoListOfTerms hY with
    ⟨yTerms, hYEq, _hYVars, hYAll⟩
  subst x
  subst y
  have hXStuck : ∀ t ∈ xTerms, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hXAll t ht)
  have hYStuck : ∀ t ∈ yTerms, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hYAll t ht)
  have hSetStuck : ∀ t ∈ termListSetOf xTerms, t ≠ Term.Stuck := by
    intro t ht
    exact hXStuck t ((termListSetOf_mem).1 ht)
  rw [eo_list_setof_eoListOfTerms_eq hXStuck] at hMem
  rw [eo_list_diff_eoListOfTerms_eq hSetStuck hYStuck] at hMem
  have hMemDiff :
      z ∈ termListDiff (termListSetOf xTerms) yTerms :=
    (eoListOfTerms_termMem_iff).1 hMem
  intro hMemY
  have hMemYList : z ∈ yTerms :=
    (eoListOfTerms_termMem_iff).1 hMemY
  exact termListDiff_not_mem_right_of_nodup_left
    termListSetOf_nodup hMemDiff hMemYList

private theorem eoSmtVarEnv_findRec_false_of_termMem :
    ∀ {env : Term} {vars : List SmtVarKey} {z : Term},
      EoSmtVarEnv env vars ->
        z ≠ Term.Stuck ->
          EoSmtVarEnvTermMem z env ->
            ∀ n : native_Int,
              native_zlt n 0 = false ->
                __eo_is_neg
                    (__eo_list_find_rec env z (Term.Numeral n)) =
                  Term.Boolean false
  | _, _, _, EoSmtVarEnv.nil, _hz, hMem, _n, _hN =>
      by
        exact False.elim hMem
  | _, _, z, EoSmtVarEnv.cons (s := s) (T := T) (env := tail) hTail,
      hz, hMem, n, hN =>
      by
        have hHeadNe :
            Term.Var (Term.String s) T ≠ Term.Stuck :=
          termVarString_ne_stuck s T
        by_cases hEq :
            Term.Var (Term.String s) T = z
        · subst z
          have hEqTerm :
              __eo_eq (Term.Var (Term.String s) T)
                  (Term.Var (Term.String s) T) =
                Term.Boolean true :=
            eoEq_true_of_eq_ne_stuck hHeadNe
          simp [__eo_list_find_rec, hEqTerm, __eo_ite, __eo_is_neg,
            hN, native_ite, native_teq]
        · have hTailMem : EoSmtVarEnvTermMem z tail := by
            rcases hMem with hHead | hTailMem
            · exact False.elim (hEq hHead)
            · exact hTailMem
          have hEqTerm :
              __eo_eq (Term.Var (Term.String s) T) z =
                Term.Boolean false :=
            eoEq_false_of_ne_nonstuck hEq hHeadNe hz
          have hN' :
              native_zlt (native_zplus n 1) 0 = false :=
            nativeZlt_plus_one_nonneg hN
          have hTailFind :=
            eoSmtVarEnv_findRec_false_of_termMem hTail hz hTailMem
              (native_zplus n 1) hN'
          simpa [__eo_list_find_rec, hEqTerm, __eo_ite, native_ite,
            native_teq] using hTailFind

private theorem eoSmtVarEnv_find_false_of_termMem
    {env : Term} {vars : List SmtVarKey} {z : Term}
    (hEnv : EoSmtVarEnv env vars)
    (hz : z ≠ Term.Stuck)
    (hMem : EoSmtVarEnvTermMem z env) :
    __eo_is_neg (__eo_list_find Term.__eo_List_cons env z) =
      Term.Boolean false := by
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hRec :=
    eoSmtVarEnv_findRec_false_of_termMem hEnv hz hMem 0 hZero
  simpa [__eo_list_find, hEnv.is_list, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hRec

private theorem eoSmtVarEnv_setof_find_false_of_mem
    {env : Term} {vars : List SmtVarKey} {z : Term}
    (hEnv : EoSmtVarEnv env vars)
    (hz : z ≠ Term.Stuck)
    (hMem : EoSmtVarEnvTermMem z env) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons env) z) =
      Term.Boolean false := by
  rcases eoSmtVarEnv_setof_exists hEnv with ⟨setVars, hSetEnv⟩
  exact eoSmtVarEnv_find_false_of_termMem hSetEnv hz
    (eoSmtVarEnvTermMem_setof_of_mem hEnv hMem)

private theorem minclude_env_diff_perm_append
    {a b : Term} {aVars bVars : List SmtVarKey}
    (hA : EoSmtVarEnv a aVars) (hB : EoSmtVarEnv b bVars)
    (hIncl :
      __eo_list_minclude Term.__eo_List_cons a b = Term.Boolean true) :
    ∃ diffVars,
      EoSmtVarEnv (__eo_list_diff Term.__eo_List_cons a b) diffVars ∧
      aVars.Perm (bVars ++ diffVars) := by
  rcases eoSmtVarEnv_as_eoListOfTerms hA with
    ⟨ats, hAEq, hAVars, hAAll⟩
  rcases eoSmtVarEnv_as_eoListOfTerms hB with
    ⟨bts, hBEq, hBVars, hBAll⟩
  subst a
  subst b
  subst aVars
  subst bVars
  have hAStuck : ∀ t ∈ ats, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hAAll t ht)
  have hBStuck : ∀ t ∈ bts, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hBAll t ht)
  have hPermTerms :
      ats.Perm (bts ++ termListDiff ats bts) :=
    minclude_eoList_perm_diff hAStuck hBStuck hIncl
  have hPermVars :
      (ats.map quantTermBinder).Perm
        (bts.map quantTermBinder ++
          (termListDiff ats bts).map quantTermBinder) := by
    simpa [List.map_append] using hPermTerms.map quantTermBinder
  exact
    ⟨(termListDiff ats bts).map quantTermBinder,
      eoSmtVarEnv_diff_eoListOfTerms hAStuck hBStuck hAAll,
      hPermVars⟩

private def smtExistsOfBinders : List SmtVarKey -> SmtTerm -> SmtTerm
  | [], body => body
  | b :: bs, body => SmtTerm.exists b.1 b.2 (smtExistsOfBinders bs body)

private theorem smtExistsOfBinders_append
    (xs ys : List SmtVarKey) (body : SmtTerm) :
    smtExistsOfBinders (xs ++ ys) body =
      smtExistsOfBinders xs (smtExistsOfBinders ys body) := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      rcases b with ⟨s, T⟩
      simp [smtExistsOfBinders, ih]

private theorem native_model_push_same
    (M : SmtModel) (s : native_String) (T : SmtType) (v w : SmtValue) :
    native_model_push (native_model_push M s T v) s T w =
      native_model_push M s T w := by
  cases M with
  | mk values nativeFuns =>
      change
        SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then w
              else
                (if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then v
                else values k))
            nativeFuns =
          SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then w
              else values k)
            nativeFuns
      congr
      funext k
      by_cases hk : k = ({ isVar := true, name := s, ty := T } : SmtModelKey)
      · simp [hk]
      · simp [hk]

private theorem native_model_push_comm
    (M : SmtModel) (s1 s2 : native_String) (T1 T2 : SmtType)
    (v1 v2 : SmtValue)
    (hNe :
      ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) ≠
        { isVar := true, name := s2, ty := T2 }) :
    native_model_push (native_model_push M s1 T1 v1) s2 T2 v2 =
      native_model_push (native_model_push M s2 T2 v2) s1 T1 v1 := by
  cases M with
  | mk values nativeFuns =>
      change
        SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
              else
                (if k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) then v1
                else values k))
            nativeFuns =
          SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) then v1
              else
                (if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
                else values k))
            nativeFuns
      congr
      funext k
      by_cases h1 : k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey)
      · subst k
        by_cases h2 :
            ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
              { isVar := true, name := s2, ty := T2 }
        · exact False.elim (hNe h2)
        · simp [h2]
      · by_cases h2 : k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey)
        · subst k
          have h21 :
              ¬ ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) =
                { isVar := true, name := s1, ty := T1 } := by
            intro h
            exact hNe h.symm
          simp [h21]
        · simp [h1, h2]

private theorem smtExistsOfBinders_cons_congr
    (M : SmtModel) (b : SmtVarKey) (t u : SmtTerm) :
    (∀ M2, __smtx_model_eval M2 t = __smtx_model_eval M2 u) ->
    __smtx_model_eval M (smtExistsOfBinders [b] t) =
      __smtx_model_eval M (smtExistsOfBinders [b] u) := by
  rcases b with ⟨s, T⟩
  intro hEval
  classical
  let P : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) t =
          SmtValue.Boolean true
  let Q : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) u =
          SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    constructor
    · intro hSat
      rcases hSat with ⟨v, hv, hCan, hT⟩
      exact ⟨v, hv, hCan, by
        simpa [hEval (native_model_push M s T v)] using hT⟩
    · intro hSat
      rcases hSat with ⟨v, hv, hCan, hU⟩
      exact ⟨v, hv, hCan, by
        simpa [hEval (native_model_push M s T v)] using hU⟩
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, hPropEq]

private theorem smtx_model_eval_exists_congr
    (M : SmtModel) (s : native_String) (T : SmtType)
    (body body' : SmtTerm)
    (hEval : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push M s T v) body') :
    __smtx_model_eval M (SmtTerm.exists s T body) =
      __smtx_model_eval M (SmtTerm.exists s T body') := by
  classical
  let P : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true
  let Q : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) body' =
          SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    constructor
    · intro hSat
      rcases hSat with ⟨v, hv, hc, hBody⟩
      exact ⟨v, hv, hc, by
        simpa [hEval v hv hc] using hBody⟩
    · intro hSat
      rcases hSat with ⟨v, hv, hc, hBody'⟩
      exact ⟨v, hv, hc, by
        simpa [hEval v hv hc] using hBody'⟩
  have hPropEq : P = Q := propext hPQ
  simp [__smtx_model_eval, P, Q, hPropEq]

private theorem smtExistsOfBinders_swap
    (M : SmtModel) (b1 b2 : SmtVarKey) (tail : List SmtVarKey)
    (body : SmtTerm) :
    __smtx_model_eval M (smtExistsOfBinders (b1 :: b2 :: tail) body) =
      __smtx_model_eval M (smtExistsOfBinders (b2 :: b1 :: tail) body) := by
  rcases b1 with ⟨s1, T1⟩
  rcases b2 with ⟨s2, T2⟩
  classical
  let rest := smtExistsOfBinders tail body
  let P : Prop :=
    ∃ v1 : SmtValue,
      __smtx_typeof_value v1 = T1 ∧
        __smtx_value_canonical_bool v1 = true ∧
        ∃ v2 : SmtValue,
          __smtx_typeof_value v2 = T2 ∧
            __smtx_value_canonical_bool v2 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s1 T1 v1) s2 T2 v2)
                rest =
              SmtValue.Boolean true
  let Q : Prop :=
    ∃ v2 : SmtValue,
      __smtx_typeof_value v2 = T2 ∧
        __smtx_value_canonical_bool v2 = true ∧
        ∃ v1 : SmtValue,
          __smtx_typeof_value v1 = T1 ∧
            __smtx_value_canonical_bool v1 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s2 T2 v2) s1 T1 v1)
                rest =
              SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    by_cases hKey :
        ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
          { isVar := true, name := s2, ty := T2 }
    · cases hKey
      constructor
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        exact ⟨v1, hv1, hc1, v2, hv2, hc2, by
          simpa [native_model_push_same] using hEval⟩
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        exact ⟨v1, hv1, hc1, v2, hv2, hc2, by
          simpa [native_model_push_same] using hEval⟩
    · constructor
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        refine ⟨v2, hv2, hc2, v1, hv1, hc1, ?_⟩
        simpa [native_model_push_comm M s1 s2 T1 T2 v1 v2 hKey] using
          hEval
      · intro hSat
        rcases hSat with ⟨v2, hv2, hc2, v1, hv1, hc1, hEval⟩
        refine ⟨v1, hv1, hc1, v2, hv2, hc2, ?_⟩
        simpa [native_model_push_comm M s1 s2 T1 T2 v1 v2 hKey] using
          hEval
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, rest, hPropEq]

private theorem smtExistsOfBinders_duplicate_head
    (M : SmtModel) (b : SmtVarKey) (tail : List SmtVarKey)
    (body : SmtTerm) :
    __smtx_model_eval M (smtExistsOfBinders (b :: b :: tail) body) =
      __smtx_model_eval M (smtExistsOfBinders (b :: tail) body) := by
  rcases b with ⟨s, T⟩
  classical
  let rest := smtExistsOfBinders tail body
  let P : Prop :=
    ∃ v1 : SmtValue,
      __smtx_typeof_value v1 = T ∧
        __smtx_value_canonical_bool v1 = true ∧
        ∃ v2 : SmtValue,
          __smtx_typeof_value v2 = T ∧
            __smtx_value_canonical_bool v2 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s T v1) s T v2)
                rest =
              SmtValue.Boolean true
  let Q : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) rest =
          SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    constructor
    · intro hSat
      rcases hSat with
        ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
      exact ⟨v2, hv2, hc2, by
        simpa [native_model_push_same] using hEval⟩
    · intro hSat
      rcases hSat with ⟨v, hv, hc, hEval⟩
      exact ⟨v, hv, hc, v, hv, hc, by
        simpa [native_model_push_same] using hEval⟩
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, rest, hPropEq]

private theorem smtExistsOfBinders_eval_perm
    (body : SmtTerm) {xs ys : List SmtVarKey}
    (hperm : xs.Perm ys) :
    ∀ M, __smtx_model_eval M (smtExistsOfBinders xs body) =
      __smtx_model_eval M (smtExistsOfBinders ys body) := by
  induction hperm with
  | nil =>
      intro M
      rfl
  | cons b _h ih =>
      intro M
      exact smtExistsOfBinders_cons_congr M b
        (smtExistsOfBinders _ body) (smtExistsOfBinders _ body) ih
  | swap b1 b2 tail =>
      intro M
      exact (smtExistsOfBinders_swap M b1 b2 tail body).symm
  | trans _h1 _h2 ih1 ih2 =>
      intro M
      exact (ih1 M).trans (ih2 M)

private theorem smtExistsOfBinders_eval_map_erase_all_after_head
    (body : SmtTerm) (z : Term) :
    ∀ (xs : List Term) (M : SmtModel),
      __smtx_model_eval M
          (smtExistsOfBinders
            (quantTermBinder z :: xs.map quantTermBinder) body) =
        __smtx_model_eval M
          (smtExistsOfBinders
            (quantTermBinder z ::
              (termListEraseAll xs z).map quantTermBinder) body)
  | [], M => by
      rfl
  | x :: xs, M => by
      by_cases hzx : z = x
      · subst z
        have hDropHead :
            __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder x :: quantTermBinder x ::
                    xs.map quantTermBinder) body) =
              __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder x :: xs.map quantTermBinder) body) :=
          smtExistsOfBinders_duplicate_head M (quantTermBinder x)
            (xs.map quantTermBinder) body
        have hTail :=
          smtExistsOfBinders_eval_map_erase_all_after_head body x xs M
        calc
          __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder x ::
                  (x :: xs).map quantTermBinder) body)
              =
            __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder x :: xs.map quantTermBinder) body) := by
              simpa using hDropHead
          _ =
            __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder x ::
                  (termListEraseAll xs x).map quantTermBinder) body) :=
              hTail
          _ =
            __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder x ::
                  (termListEraseAll (x :: xs) x).map quantTermBinder) body) := by
              simp [termListEraseAll]
      · have hSwap₁ :
            __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder z :: quantTermBinder x ::
                    xs.map quantTermBinder) body) =
              __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder x :: quantTermBinder z ::
                    xs.map quantTermBinder) body) :=
          smtExistsOfBinders_swap M (quantTermBinder z)
            (quantTermBinder x) (xs.map quantTermBinder) body
        have hInner :
            __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder x :: quantTermBinder z ::
                    xs.map quantTermBinder) body) =
              __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder x :: quantTermBinder z ::
                    (termListEraseAll xs z).map quantTermBinder) body) :=
          smtExistsOfBinders_cons_congr M (quantTermBinder x)
            (smtExistsOfBinders
              (quantTermBinder z :: xs.map quantTermBinder) body)
            (smtExistsOfBinders
              (quantTermBinder z ::
                (termListEraseAll xs z).map quantTermBinder) body)
            (smtExistsOfBinders_eval_map_erase_all_after_head body z xs)
        have hSwap₂ :
            __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder x :: quantTermBinder z ::
                    (termListEraseAll xs z).map quantTermBinder) body) =
              __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder z :: quantTermBinder x ::
                    (termListEraseAll xs z).map quantTermBinder) body) :=
          smtExistsOfBinders_swap M (quantTermBinder x)
            (quantTermBinder z)
            ((termListEraseAll xs z).map quantTermBinder) body
        calc
          __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder z ::
                  (x :: xs).map quantTermBinder) body)
              =
            __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder x :: quantTermBinder z ::
                  xs.map quantTermBinder) body) := by
              simpa using hSwap₁
          _ =
            __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder x :: quantTermBinder z ::
                  (termListEraseAll xs z).map quantTermBinder) body) :=
              hInner
          _ =
            __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder z :: quantTermBinder x ::
                  (termListEraseAll xs z).map quantTermBinder) body) :=
              hSwap₂
          _ =
            __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder z ::
                  (termListEraseAll (x :: xs) z).map quantTermBinder)
                body) := by
              simp [termListEraseAll, hzx]

private theorem smtExistsOfBinders_eval_map_setof
    (body : SmtTerm) :
    ∀ (xs : List Term) (M : SmtModel),
      __smtx_model_eval M
          (smtExistsOfBinders (xs.map quantTermBinder) body) =
        __smtx_model_eval M
          (smtExistsOfBinders
            ((termListSetOf xs).map quantTermBinder) body)
  | [], M => by
      rfl
  | x :: xs, M => by
      have hTail :
          __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder x :: xs.map quantTermBinder) body) =
            __smtx_model_eval M
              (smtExistsOfBinders
                (quantTermBinder x ::
                  (termListSetOf xs).map quantTermBinder) body) :=
        smtExistsOfBinders_cons_congr M (quantTermBinder x)
          (smtExistsOfBinders (xs.map quantTermBinder) body)
          (smtExistsOfBinders
            ((termListSetOf xs).map quantTermBinder) body)
          (smtExistsOfBinders_eval_map_setof body xs)
      have hErase :=
        smtExistsOfBinders_eval_map_erase_all_after_head body x
          (termListSetOf xs) M
      calc
        __smtx_model_eval M
            (smtExistsOfBinders
              ((x :: xs).map quantTermBinder) body)
            =
          __smtx_model_eval M
            (smtExistsOfBinders
              (quantTermBinder x ::
                (termListSetOf xs).map quantTermBinder) body) :=
            hTail
        _ =
          __smtx_model_eval M
            (smtExistsOfBinders
              (quantTermBinder x ::
                (termListEraseAll (termListSetOf xs) x).map
                  quantTermBinder) body) :=
            hErase
        _ =
          __smtx_model_eval M
            (smtExistsOfBinders
              ((termListSetOf (x :: xs)).map quantTermBinder) body) := by
            simp [termListSetOf]

private theorem eo_to_smt_exists_of_env
    {env : Term} {vars : List SmtVarKey} (body : SmtTerm)
    (hEnv : EoSmtVarEnv env vars) :
    __eo_to_smt_exists env body = smtExistsOfBinders vars body := by
  induction hEnv with
  | nil =>
      simp [__eo_to_smt_exists, smtExistsOfBinders]
  | cons hTail ih =>
      rename_i s T tail varsTail
      simp [__eo_to_smt_exists, smtExistsOfBinders, ih]

private theorem smtx_model_eval_eo_to_smt_exists_setof
    (M : SmtModel) (x : Term) (body : SmtTerm)
    {xVars : List SmtVarKey}
    (hEnv : EoSmtVarEnv x xVars) :
    __smtx_model_eval M (__eo_to_smt_exists x body) =
      __smtx_model_eval M
        (__eo_to_smt_exists
          (__eo_list_setof Term.__eo_List_cons x) body) := by
  rcases eoSmtVarEnv_as_eoListOfTerms hEnv with
    ⟨ts, hXEq, hVarsEq, hAll⟩
  subst x
  subst xVars
  have hStuck : ∀ t ∈ ts, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hAll t ht)
  rw [eo_list_setof_eoListOfTerms_eq hStuck]
  rw [eo_to_smt_exists_of_env body
      (eoSmtVarEnv_of_eoListOfTerms hAll)]
  rw [eo_to_smt_exists_of_env body
      (eoSmtVarEnv_of_eoListOfTerms
        (termListSetOf_quant_terms hAll))]
  exact smtExistsOfBinders_eval_map_setof body ts M

private theorem eo_to_smt_exists_concat_eq
    {x y : Term} {xVars yVars : List SmtVarKey}
    (body : SmtTerm)
    (hX : EoSmtVarEnv x xVars)
    (hY : EoSmtVarEnv y yVars) :
    __eo_to_smt_exists
        (__eo_list_concat Term.__eo_List_cons x y) body =
      __eo_to_smt_exists x (__eo_to_smt_exists y body) := by
  rw [eo_to_smt_exists_of_env body (EoSmtVarEnv.concat hX hY)]
  rw [eo_to_smt_exists_of_env body hY]
  rw [eo_to_smt_exists_of_env (smtExistsOfBinders yVars body) hX]
  exact smtExistsOfBinders_append xVars yVars body

private theorem eo_list_setof_ne_nil_of_env_ne_nil
    {x : Term} {xVars : List SmtVarKey}
    (hEnv : EoSmtVarEnv x xVars)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_list_setof Term.__eo_List_cons x ≠ Term.__eo_List_nil := by
  rcases eoSmtVarEnv_as_eoListOfTerms hEnv with
    ⟨ts, hXEq, _hVarsEq, hAll⟩
  subst x
  have hTs : ts ≠ [] := by
    intro hNil
    subst ts
    exact hx rfl
  have hSetTs : termListSetOf ts ≠ [] :=
    termListSetOf_ne_nil_of_ne_nil hTs
  have hStuck : ∀ t ∈ ts, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hAll t ht)
  rw [eo_list_setof_eoListOfTerms_eq hStuck]
  intro hSetNil
  cases hSetEq : termListSetOf ts with
  | nil =>
      exact hSetTs hSetEq
  | cons head tail =>
      rw [hSetEq] at hSetNil
      simp [eoListOfTerms] at hSetNil

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

private theorem smtx_model_eval_qexists_env_perm
    (M : SmtModel) (x y F : Term)
    {xVars yVars : List SmtVarKey}
    (hXEnv : EoSmtVarEnv x xVars) (hYEnv : EoSmtVarEnv y yVars)
    (hPerm : xVars.Perm yVars)
    (hx : x ≠ Term.__eo_List_nil) (hy : y ≠ Term.__eo_List_nil) :
    __smtx_model_eval M (__eo_to_smt (qexists x F)) =
      __smtx_model_eval M (__eo_to_smt (qexists y F)) := by
  rw [eo_to_smt_exists_eq x F hx, eo_to_smt_exists_eq y F hy]
  rw [eo_to_smt_exists_of_env (__eo_to_smt F) hXEnv,
    eo_to_smt_exists_of_env (__eo_to_smt F) hYEnv]
  exact smtExistsOfBinders_eval_perm (__eo_to_smt F) hPerm M

private theorem smtx_model_eval_qforall_env_perm
    (M : SmtModel) (x y F : Term)
    {xVars yVars : List SmtVarKey}
    (hXEnv : EoSmtVarEnv x xVars) (hYEnv : EoSmtVarEnv y yVars)
    (hPerm : xVars.Perm yVars)
    (hx : x ≠ Term.__eo_List_nil) (hy : y ≠ Term.__eo_List_nil) :
    __smtx_model_eval M (__eo_to_smt (qforall x F)) =
      __smtx_model_eval M (__eo_to_smt (qforall y F)) := by
  rw [eo_to_smt_forall_eq x F hx, eo_to_smt_forall_eq y F hy]
  rw [eo_to_smt_exists_of_env (SmtTerm.not (__eo_to_smt F)) hXEnv,
    eo_to_smt_exists_of_env (SmtTerm.not (__eo_to_smt F)) hYEnv]
  have hExists :=
    smtExistsOfBinders_eval_perm (SmtTerm.not (__eo_to_smt F)) hPerm M
  simp [__smtx_model_eval, hExists]

private theorem smtx_model_eval_qterm_env_perm
    (M : SmtModel) (Q x y F : Term)
    {xVars yVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hXEnv : EoSmtVarEnv x xVars) (hYEnv : EoSmtVarEnv y yVars)
    (hPerm : xVars.Perm yVars)
    (hx : x ≠ Term.__eo_List_nil) (hy : y ≠ Term.__eo_List_nil) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M (__eo_to_smt (qterm Q y F)) := by
  rcases hQ with hQ | hQ
  · subst Q
    exact smtx_model_eval_qforall_env_perm M x y F hXEnv hYEnv hPerm hx hy
  · subst Q
    exact smtx_model_eval_qexists_env_perm M x y F hXEnv hYEnv hPerm hx hy

private theorem smtx_model_eval_qterm_setof
    (M : SmtModel) (Q x F : Term) {xVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hEnv : EoSmtVarEnv x xVars)
    (hx : x ≠ Term.__eo_List_nil) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M
        (__eo_to_smt
          (qterm Q (__eo_list_setof Term.__eo_List_cons x) F)) := by
  have hSetNe :
      __eo_list_setof Term.__eo_List_cons x ≠ Term.__eo_List_nil :=
    eo_list_setof_ne_nil_of_env_ne_nil hEnv hx
  rcases hQ with hQ | hQ
  · subst Q
    rw [show qterm (Term.UOp UserOp.forall) x F = qforall x F by rfl]
    rw [show
        qterm (Term.UOp UserOp.forall)
            (__eo_list_setof Term.__eo_List_cons x) F =
          qforall (__eo_list_setof Term.__eo_List_cons x) F by rfl]
    rw [eo_to_smt_forall_eq x F hx,
      eo_to_smt_forall_eq (__eo_list_setof Term.__eo_List_cons x) F hSetNe]
    have hExists :=
      smtx_model_eval_eo_to_smt_exists_setof M x
        (SmtTerm.not (__eo_to_smt F)) hEnv
    simp [__smtx_model_eval, hExists]
  · subst Q
    rw [show qterm (Term.UOp UserOp.exists) x F = qexists x F by rfl]
    rw [show
        qterm (Term.UOp UserOp.exists)
            (__eo_list_setof Term.__eo_List_cons x) F =
          qexists (__eo_list_setof Term.__eo_List_cons x) F by rfl]
    rw [eo_to_smt_exists_eq x F hx,
      eo_to_smt_exists_eq (__eo_list_setof Term.__eo_List_cons x) F hSetNe]
    exact smtx_model_eval_eo_to_smt_exists_setof M x (__eo_to_smt F) hEnv

private theorem smtx_model_eval_qterm_setof_perm_concat
    (M : SmtModel) (Q x y diff F : Term)
    {xVars setVars yVars diffVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hXEnv : EoSmtVarEnv x xVars)
    (hSetEnv :
      EoSmtVarEnv (__eo_list_setof Term.__eo_List_cons x) setVars)
    (hYEnv : EoSmtVarEnv y yVars)
    (hDiffEnv : EoSmtVarEnv diff diffVars)
    (hPerm : setVars.Perm (yVars ++ diffVars))
    (hx : x ≠ Term.__eo_List_nil)
    (hy : y ≠ Term.__eo_List_nil) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M
        (__eo_to_smt
          (qterm Q (__eo_list_concat Term.__eo_List_cons y diff) F)) := by
  have hSetEval :
      __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
        __smtx_model_eval M
          (__eo_to_smt
            (qterm Q (__eo_list_setof Term.__eo_List_cons x) F)) :=
    smtx_model_eval_qterm_setof M Q x F hQ hXEnv hx
  have hSetNe :
      __eo_list_setof Term.__eo_List_cons x ≠ Term.__eo_List_nil :=
    eo_list_setof_ne_nil_of_env_ne_nil hXEnv hx
  have hConcatEnv :
      EoSmtVarEnv (__eo_list_concat Term.__eo_List_cons y diff)
        (yVars ++ diffVars) :=
    EoSmtVarEnv.concat hYEnv hDiffEnv
  have hConcatNe :
      __eo_list_concat Term.__eo_List_cons y diff ≠
        Term.__eo_List_nil :=
    eo_list_concat_ne_nil_of_left_env_ne_nil hYEnv hDiffEnv hy
  have hPermEval :
      __smtx_model_eval M
          (__eo_to_smt
            (qterm Q (__eo_list_setof Term.__eo_List_cons x) F)) =
        __smtx_model_eval M
          (__eo_to_smt
            (qterm Q (__eo_list_concat Term.__eo_List_cons y diff) F)) :=
    smtx_model_eval_qterm_env_perm M Q
      (__eo_list_setof Term.__eo_List_cons x)
      (__eo_list_concat Term.__eo_List_cons y diff) F
      hQ hSetEnv hConcatEnv hPerm hSetNe hConcatNe
  exact hSetEval.trans hPermEval

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

private theorem smtx_typeof_exists_body_bool_of_bool
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool ->
      __smtx_typeof body = SmtType.Bool := by
  intro hTy
  have hNN :
      term_has_non_none_type (SmtTerm.exists s T body) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact exists_body_bool_of_non_none hNN

private theorem smtx_type_wf_of_exists_bool
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool ->
      __smtx_type_wf T = true := by
  intro hTy
  have hBody : __smtx_typeof body = SmtType.Bool :=
    smtx_typeof_exists_body_bool_of_bool s T body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
    intro hNone
    rw [smtx_typeof_exists_term_eq, hBody] at hTy
    simp [native_ite, native_Teq, hNone] at hTy
  exact smtx_typeof_guard_wf_wf_of_non_none T SmtType.Bool hGuardNN

private theorem smtx_typeof_exists_bool_of_wf_body_bool
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBody : __smtx_typeof body = SmtType.Bool) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool := by
  rw [smtx_typeof_exists_term_eq, hBody]
  simp [native_ite, native_Teq, __smtx_typeof_guard_wf, hWF]

private theorem smtExistsOfBinders_type_bool_of_perm
    (body : SmtTerm) {xs ys : List SmtVarKey}
    (hPerm : xs.Perm ys) :
    __smtx_typeof (smtExistsOfBinders xs body) = SmtType.Bool ->
      __smtx_typeof (smtExistsOfBinders ys body) = SmtType.Bool := by
  induction hPerm with
  | nil =>
      intro hTy
      exact hTy
  | cons b _h ih =>
      rcases b with ⟨s, T⟩
      intro hTy
      have hTail :
          __smtx_typeof (smtExistsOfBinders _ body) = SmtType.Bool :=
        smtx_typeof_exists_body_bool_of_bool s T
          (smtExistsOfBinders _ body) hTy
      have hWF :
          __smtx_type_wf T = true :=
        smtx_type_wf_of_exists_bool s T
          (smtExistsOfBinders _ body) hTy
      exact smtx_typeof_exists_bool_of_wf_body_bool s T
        (smtExistsOfBinders _ body) hWF (ih hTail)
  | swap b1 b2 tail =>
      rcases b1 with ⟨s1, T1⟩
      rcases b2 with ⟨s2, T2⟩
      intro hTy
      have hTail₂ :
          __smtx_typeof
              (SmtTerm.exists s1 T1
                (smtExistsOfBinders tail body)) =
            SmtType.Bool :=
        smtx_typeof_exists_body_bool_of_bool s2 T2
          (SmtTerm.exists s1 T1 (smtExistsOfBinders tail body)) hTy
      have hWF₂ :
          __smtx_type_wf T2 = true :=
        smtx_type_wf_of_exists_bool s2 T2
          (SmtTerm.exists s1 T1 (smtExistsOfBinders tail body)) hTy
      have hRest :
          __smtx_typeof (smtExistsOfBinders tail body) = SmtType.Bool :=
        smtx_typeof_exists_body_bool_of_bool s1 T1
          (smtExistsOfBinders tail body) hTail₂
      have hWF₁ :
          __smtx_type_wf T1 = true :=
        smtx_type_wf_of_exists_bool s1 T1
          (smtExistsOfBinders tail body) hTail₂
      have hInner :
          __smtx_typeof
              (SmtTerm.exists s2 T2
                (smtExistsOfBinders tail body)) =
            SmtType.Bool :=
        smtx_typeof_exists_bool_of_wf_body_bool s2 T2
          (smtExistsOfBinders tail body) hWF₂ hRest
      exact smtx_typeof_exists_bool_of_wf_body_bool s1 T1
        (SmtTerm.exists s2 T2 (smtExistsOfBinders tail body))
        hWF₁ hInner
  | trans _h1 _h2 ih1 ih2 =>
      intro hTy
      exact ih2 (ih1 hTy)

private theorem smtExistsOfBinders_type_duplicate_head
    (b : SmtVarKey) (tail : List SmtVarKey) (body : SmtTerm) :
    __smtx_typeof (smtExistsOfBinders (b :: b :: tail) body) =
        SmtType.Bool ->
      __smtx_typeof (smtExistsOfBinders (b :: tail) body) =
        SmtType.Bool := by
  rcases b with ⟨s, T⟩
  intro hTy
  have hInner :
      __smtx_typeof
          (SmtTerm.exists s T (smtExistsOfBinders tail body)) =
        SmtType.Bool :=
    smtx_typeof_exists_body_bool_of_bool s T
      (SmtTerm.exists s T (smtExistsOfBinders tail body)) hTy
  have hWF :
      __smtx_type_wf T = true :=
    smtx_type_wf_of_exists_bool s T
      (SmtTerm.exists s T (smtExistsOfBinders tail body)) hTy
  have hRest :
      __smtx_typeof (smtExistsOfBinders tail body) = SmtType.Bool :=
    smtx_typeof_exists_body_bool_of_bool s T
      (smtExistsOfBinders tail body) hInner
  exact smtx_typeof_exists_bool_of_wf_body_bool s T
    (smtExistsOfBinders tail body) hWF hRest

private theorem smtExistsOfBinders_type_map_erase_all_after_head
    (body : SmtTerm) (z : Term) :
    ∀ (xs : List Term),
      __smtx_typeof
          (smtExistsOfBinders
            (quantTermBinder z :: xs.map quantTermBinder) body) =
        SmtType.Bool ->
      __smtx_typeof
          (smtExistsOfBinders
            (quantTermBinder z ::
              (termListEraseAll xs z).map quantTermBinder) body) =
        SmtType.Bool
  | [], hTy => by
      simpa [termListEraseAll] using hTy
  | x :: xs, hTy => by
      by_cases hzx : z = x
      · subst z
        have hDrop :
            __smtx_typeof
                (smtExistsOfBinders
                  (quantTermBinder x :: xs.map quantTermBinder) body) =
              SmtType.Bool :=
          smtExistsOfBinders_type_duplicate_head (quantTermBinder x)
            (xs.map quantTermBinder) body (by simpa using hTy)
        have hTail :=
          smtExistsOfBinders_type_map_erase_all_after_head body x xs hDrop
        simpa [termListEraseAll] using hTail
      · have hSwap₁ :
            __smtx_typeof
                (smtExistsOfBinders
                  (quantTermBinder x :: quantTermBinder z ::
                    xs.map quantTermBinder) body) =
              SmtType.Bool :=
          smtExistsOfBinders_type_bool_of_perm body
            (List.Perm.swap (quantTermBinder x)
              (quantTermBinder z) (xs.map quantTermBinder))
            (by simpa using hTy)
        rcases hBind : quantTermBinder x with ⟨s, T⟩
        have hOuter :
            __smtx_typeof
                (SmtTerm.exists s T
                  (smtExistsOfBinders
                    (quantTermBinder z :: xs.map quantTermBinder) body)) =
              SmtType.Bool := by
          simpa [smtExistsOfBinders, hBind] using hSwap₁
        have hTailTy :
            __smtx_typeof
                (smtExistsOfBinders
                  (quantTermBinder z :: xs.map quantTermBinder) body) =
              SmtType.Bool :=
          smtx_typeof_exists_body_bool_of_bool s T
            (smtExistsOfBinders
              (quantTermBinder z :: xs.map quantTermBinder) body) hOuter
        have hWF :
            __smtx_type_wf T = true :=
          smtx_type_wf_of_exists_bool s T
            (smtExistsOfBinders
              (quantTermBinder z :: xs.map quantTermBinder) body) hOuter
        have hTailErased :=
          smtExistsOfBinders_type_map_erase_all_after_head body z xs hTailTy
        have hInner :
            __smtx_typeof
                (smtExistsOfBinders
                  (quantTermBinder x :: quantTermBinder z ::
                    (termListEraseAll xs z).map quantTermBinder) body) =
              SmtType.Bool := by
          have hInner' :
              __smtx_typeof
                  (SmtTerm.exists s T
                    (smtExistsOfBinders
                      (quantTermBinder z ::
                        (termListEraseAll xs z).map quantTermBinder) body)) =
                SmtType.Bool :=
            smtx_typeof_exists_bool_of_wf_body_bool s T
              (smtExistsOfBinders
                (quantTermBinder z ::
                  (termListEraseAll xs z).map quantTermBinder) body)
              hWF hTailErased
          simpa [smtExistsOfBinders, hBind] using hInner'
        have hSwap₂ :
            __smtx_typeof
                (smtExistsOfBinders
                  (quantTermBinder z :: quantTermBinder x ::
                    (termListEraseAll xs z).map quantTermBinder) body) =
              SmtType.Bool :=
          smtExistsOfBinders_type_bool_of_perm body
            (List.Perm.swap (quantTermBinder z)
              (quantTermBinder x)
              ((termListEraseAll xs z).map quantTermBinder))
            hInner
        simpa [termListEraseAll, hzx] using hSwap₂

private theorem smtExistsOfBinders_type_map_setof
    (body : SmtTerm) :
    ∀ (xs : List Term),
      __smtx_typeof
          (smtExistsOfBinders (xs.map quantTermBinder) body) =
        SmtType.Bool ->
      __smtx_typeof
          (smtExistsOfBinders
            ((termListSetOf xs).map quantTermBinder) body) =
        SmtType.Bool
  | [], hTy => by
      simpa [termListSetOf] using hTy
  | x :: xs, hTy => by
      rcases hBind : quantTermBinder x with ⟨s, T⟩
      have hOuter :
          __smtx_typeof
              (SmtTerm.exists s T
                (smtExistsOfBinders (xs.map quantTermBinder) body)) =
            SmtType.Bool := by
        simpa [smtExistsOfBinders, hBind] using hTy
      have hTailTy :
          __smtx_typeof
              (smtExistsOfBinders (xs.map quantTermBinder) body) =
            SmtType.Bool :=
        smtx_typeof_exists_body_bool_of_bool s T
          (smtExistsOfBinders (xs.map quantTermBinder) body) hOuter
      have hWF :
          __smtx_type_wf T = true :=
        smtx_type_wf_of_exists_bool s T
          (smtExistsOfBinders (xs.map quantTermBinder) body) hOuter
      have hTailSet :=
        smtExistsOfBinders_type_map_setof body xs hTailTy
      have hWrapped :
          __smtx_typeof
              (smtExistsOfBinders
                (quantTermBinder x ::
                  (termListSetOf xs).map quantTermBinder) body) =
            SmtType.Bool := by
        have hWrapped' :
            __smtx_typeof
                (SmtTerm.exists s T
                  (smtExistsOfBinders
                    ((termListSetOf xs).map quantTermBinder) body)) =
              SmtType.Bool :=
          smtx_typeof_exists_bool_of_wf_body_bool s T
            (smtExistsOfBinders
              ((termListSetOf xs).map quantTermBinder) body)
            hWF hTailSet
        simpa [smtExistsOfBinders, hBind] using hWrapped'
      have hErase :=
        smtExistsOfBinders_type_map_erase_all_after_head body x
          (termListSetOf xs) hWrapped
      simpa [termListSetOf] using hErase

private theorem smtx_typeof_eo_to_smt_exists_setof
    (x : Term) (body : SmtTerm) {xVars : List SmtVarKey}
    (hEnv : EoSmtVarEnv x xVars) :
    __smtx_typeof (__eo_to_smt_exists x body) = SmtType.Bool ->
      __smtx_typeof
          (__eo_to_smt_exists
            (__eo_list_setof Term.__eo_List_cons x) body) =
        SmtType.Bool := by
  intro hTy
  rcases eoSmtVarEnv_as_eoListOfTerms hEnv with
    ⟨ts, hXEq, hVarsEq, hAll⟩
  subst x
  subst xVars
  have hStuck : ∀ t ∈ ts, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hAll t ht)
  rw [eo_list_setof_eoListOfTerms_eq hStuck]
  rw [eo_to_smt_exists_of_env body
      (eoSmtVarEnv_of_eoListOfTerms hAll)] at hTy
  rw [eo_to_smt_exists_of_env body
      (eoSmtVarEnv_of_eoListOfTerms
        (termListSetOf_quant_terms hAll))]
  exact smtExistsOfBinders_type_map_setof body ts hTy

private theorem smtx_typeof_qterm_setof
    (Q x F : Term) {xVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hEnv : EoSmtVarEnv x xVars)
    (hx : x ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool) :
    __smtx_typeof
        (__eo_to_smt
          (qterm Q (__eo_list_setof Term.__eo_List_cons x) F)) =
      SmtType.Bool := by
  have hSetNe :
      __eo_list_setof Term.__eo_List_cons x ≠ Term.__eo_List_nil :=
    eo_list_setof_ne_nil_of_env_ne_nil hEnv hx
  rcases hQ with hQ | hQ
  · subst Q
    have hNN :
        __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None := by
      have hForallTy :
          __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
        simpa [qforall] using hTy
      rw [hForallTy]
      simp
    have hExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool := by
      have hNN' := hNN
      rw [eo_to_smt_forall_eq x F hx] at hNN'
      exact smtx_typeof_not_arg_of_non_none
        (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) hNN'
    have hSetExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists
              (__eo_list_setof Term.__eo_List_cons x)
              (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool :=
      smtx_typeof_eo_to_smt_exists_setof x
        (SmtTerm.not (__eo_to_smt F)) hEnv hExistsTy
    rw [show
        qterm (Term.UOp UserOp.forall)
            (__eo_list_setof Term.__eo_List_cons x) F =
          qforall (__eo_list_setof Term.__eo_List_cons x) F by rfl]
    rw [eo_to_smt_forall_eq
      (__eo_list_setof Term.__eo_List_cons x) F hSetNe]
    exact smtx_typeof_not_bool_of_arg_bool _ hSetExistsTy
  · subst Q
    have hExistsTy :
        __smtx_typeof (__eo_to_smt_exists x (__eo_to_smt F)) =
          SmtType.Bool := by
      have hExistsTopTy :
          __smtx_typeof (__eo_to_smt (qexists x F)) =
            SmtType.Bool := by
        simpa [qexists] using hTy
      simpa [eo_to_smt_exists_eq x F hx] using hExistsTopTy
    have hSetExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists
              (__eo_list_setof Term.__eo_List_cons x) (__eo_to_smt F)) =
          SmtType.Bool :=
      smtx_typeof_eo_to_smt_exists_setof x (__eo_to_smt F) hEnv
        hExistsTy
    rw [show
        qterm (Term.UOp UserOp.exists)
            (__eo_list_setof Term.__eo_List_cons x) F =
          qexists (__eo_list_setof Term.__eo_List_cons x) F by rfl]
    rw [eo_to_smt_exists_eq
      (__eo_list_setof Term.__eo_List_cons x) F hSetNe]
    exact hSetExistsTy

private theorem smtx_typeof_qterm_setof_perm_concat
    (Q x y diff F : Term)
    {xVars setVars yVars diffVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hXEnv : EoSmtVarEnv x xVars)
    (hSetEnv :
      EoSmtVarEnv (__eo_list_setof Term.__eo_List_cons x) setVars)
    (hYEnv : EoSmtVarEnv y yVars)
    (hDiffEnv : EoSmtVarEnv diff diffVars)
    (hPerm : setVars.Perm (yVars ++ diffVars))
    (hx : x ≠ Term.__eo_List_nil)
    (hy : y ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool) :
    __smtx_typeof
        (__eo_to_smt
          (qterm Q (__eo_list_concat Term.__eo_List_cons y diff) F)) =
      SmtType.Bool := by
  have hSetTy :
      __smtx_typeof
          (__eo_to_smt
            (qterm Q (__eo_list_setof Term.__eo_List_cons x) F)) =
        SmtType.Bool :=
    smtx_typeof_qterm_setof Q x F hQ hXEnv hx hTy
  have hConcatEnv :
      EoSmtVarEnv (__eo_list_concat Term.__eo_List_cons y diff)
        (yVars ++ diffVars) :=
    EoSmtVarEnv.concat hYEnv hDiffEnv
  have hConcatNe :
      __eo_list_concat Term.__eo_List_cons y diff ≠
        Term.__eo_List_nil :=
    eo_list_concat_ne_nil_of_left_env_ne_nil hYEnv hDiffEnv hy
  have hSetNe :
      __eo_list_setof Term.__eo_List_cons x ≠ Term.__eo_List_nil :=
    eo_list_setof_ne_nil_of_env_ne_nil hXEnv hx
  rcases hQ with hQ | hQ
  · subst Q
    have hSetExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists
              (__eo_list_setof Term.__eo_List_cons x)
              (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool := by
      have hNN :
          __smtx_typeof
              (__eo_to_smt
                (qforall (__eo_list_setof Term.__eo_List_cons x) F)) ≠
            SmtType.None := by
        have hSetForallTy :
            __smtx_typeof
                (__eo_to_smt
                  (qforall (__eo_list_setof Term.__eo_List_cons x) F)) =
              SmtType.Bool := by
          simpa [qforall] using hSetTy
        rw [hSetForallTy]
        simp
      have hNN' := hNN
      rw [eo_to_smt_forall_eq
        (__eo_list_setof Term.__eo_List_cons x) F hSetNe] at hNN'
      exact smtx_typeof_not_arg_of_non_none
        (__eo_to_smt_exists
          (__eo_list_setof Term.__eo_List_cons x)
          (SmtTerm.not (__eo_to_smt F))) hNN'
    have hSetBindTy :
        __smtx_typeof
            (smtExistsOfBinders setVars (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool := by
      simpa [eo_to_smt_exists_of_env
        (SmtTerm.not (__eo_to_smt F)) hSetEnv] using hSetExistsTy
    have hConcatBindTy :
        __smtx_typeof
            (smtExistsOfBinders (yVars ++ diffVars)
              (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool :=
      smtExistsOfBinders_type_bool_of_perm
        (SmtTerm.not (__eo_to_smt F)) hPerm hSetBindTy
    have hConcatExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists
              (__eo_list_concat Term.__eo_List_cons y diff)
              (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool := by
      rw [eo_to_smt_exists_of_env
        (SmtTerm.not (__eo_to_smt F)) hConcatEnv]
      exact hConcatBindTy
    rw [show
        qterm (Term.UOp UserOp.forall)
            (__eo_list_concat Term.__eo_List_cons y diff) F =
          qforall (__eo_list_concat Term.__eo_List_cons y diff) F by rfl]
    rw [eo_to_smt_forall_eq
      (__eo_list_concat Term.__eo_List_cons y diff) F hConcatNe]
    exact smtx_typeof_not_bool_of_arg_bool _ hConcatExistsTy
  · subst Q
    have hSetExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists
              (__eo_list_setof Term.__eo_List_cons x) (__eo_to_smt F)) =
          SmtType.Bool := by
      have hSetExistsTopTy :
          __smtx_typeof
              (__eo_to_smt
                (qexists (__eo_list_setof Term.__eo_List_cons x) F)) =
            SmtType.Bool := by
        simpa [qexists] using hSetTy
      simpa [eo_to_smt_exists_eq
        (__eo_list_setof Term.__eo_List_cons x) F hSetNe] using
          hSetExistsTopTy
    have hSetBindTy :
        __smtx_typeof
            (smtExistsOfBinders setVars (__eo_to_smt F)) =
          SmtType.Bool := by
      simpa [eo_to_smt_exists_of_env (__eo_to_smt F) hSetEnv] using
        hSetExistsTy
    have hConcatBindTy :
        __smtx_typeof
            (smtExistsOfBinders (yVars ++ diffVars) (__eo_to_smt F)) =
          SmtType.Bool :=
      smtExistsOfBinders_type_bool_of_perm (__eo_to_smt F) hPerm
        hSetBindTy
    have hConcatExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists
              (__eo_list_concat Term.__eo_List_cons y diff)
              (__eo_to_smt F)) =
          SmtType.Bool := by
      rw [eo_to_smt_exists_of_env (__eo_to_smt F) hConcatEnv]
      exact hConcatBindTy
    rw [show
        qterm (Term.UOp UserOp.exists)
            (__eo_list_concat Term.__eo_List_cons y diff) F =
          qexists (__eo_list_concat Term.__eo_List_cons y diff) F by rfl]
    rw [eo_to_smt_exists_eq
      (__eo_list_concat Term.__eo_List_cons y diff) F hConcatNe]
    exact hConcatExistsTy

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

private theorem smtx_type_wf_of_eo_to_smt_exists_mem_bool :
    ∀ {xs : Term} {vars : List SmtVarKey},
      EoSmtVarEnv xs vars ->
        ∀ {s : native_String} {T : Term} {body : SmtTerm},
          EoSmtVarEnvTermMem (Term.Var (Term.String s) T) xs ->
            __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
              __smtx_type_wf (__eo_to_smt_type T) = true
  | _, _, EoSmtVarEnv.nil, _s, _T, _body, hMem, _hTy =>
      by
        exact False.elim hMem
  | _, _, EoSmtVarEnv.cons (s := s0) (T := T0) (env := tail) hTail,
      s, T, body, hMem, hTy =>
      by
        rcases hMem with hHead | hTailMem
        · cases hHead
          exact smtx_type_wf_of_exists_cons_bool s0 T0 tail body hTy
        · have hTailTy :
              __smtx_typeof (__eo_to_smt_exists tail body) =
                SmtType.Bool :=
            smtx_typeof_exists_tail_bool_of_cons_bool s0 T0 tail body hTy
          exact smtx_type_wf_of_eo_to_smt_exists_mem_bool hTail
            hTailMem hTailTy

private theorem smtx_type_wf_of_qterm_binder_mem_bool
    (Q x F : Term) {vars : List SmtVarKey}
    {s : native_String} {T : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hEnv : EoSmtVarEnv x vars)
    (hx : x ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool)
    (hMem : EoSmtVarEnvTermMem (Term.Var (Term.String s) T) x) :
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  rcases hQ with hQ | hQ
  · subst Q
    have hForallTy :
        __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
      simpa [qforall] using hTy
    have hNN :
        __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None := by
      rw [hForallTy]
      simp
    have hExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool :=
      qforall_inner_exists_bool_of_non_none x F hNN
    exact smtx_type_wf_of_eo_to_smt_exists_mem_bool hEnv hMem hExistsTy
  · subst Q
    have hExistsTop :
        __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool := by
      simpa [qexists] using hTy
    have hExistsTy :
        __smtx_typeof (__eo_to_smt_exists x (__eo_to_smt F)) =
          SmtType.Bool := by
      simpa [eo_to_smt_exists_eq x F hx] using hExistsTop
    exact smtx_type_wf_of_eo_to_smt_exists_mem_bool hEnv hMem hExistsTy

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

private theorem eo_type_eq_of_smt_type_eq_of_type_wf
    {T U : Term}
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hEq : __eo_to_smt_type U = __eo_to_smt_type T) :
    U = T := by
  by_cases hReg : T = Term.UOp UserOp.RegLan
  · subst T
    exact TranslationProofs.eo_to_smt_type_eq_reglan hEq
  · have hValid : TranslationProofs.eo_type_valid_rec [] T := by
      have hTop := TranslationProofs.eo_type_valid_of_smt_wf T hWF
      simpa [TranslationProofs.eo_type_valid, hReg] using hTop
    exact (TranslationProofs.eo_to_smt_type_eq_of_valid hValid
      hEq.symm).symm

private theorem model_agrees_for_free_check_push_of_diff_mem
    (diff y : Term) {diffVars yVars : List SmtVarKey}
    (hDiffEnv : EoSmtVarEnv diff diffVars)
    (hYEnv : EoSmtVarEnv y yVars)
    (M : SmtModel) (s : native_String) (T : Term) (v : SmtValue)
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hMem :
      EoSmtVarEnvTermMem (Term.Var (Term.String s) T) diff)
    (hNotY :
      ¬ EoSmtVarEnvTermMem (Term.Var (Term.String s) T) y) :
    model_agrees_for_free_check diff
      (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil)
      (native_model_push M s (__eo_to_smt_type T) v) M := by
  refine
    ⟨model_agrees_on_globals_symm
      (model_agrees_on_globals_push M s (__eo_to_smt_type T) v), ?_⟩
  intro s' T' hFree
  by_cases hKey :
      ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
        SmtModelKey) =
        { isVar := true, name := s, ty := __eo_to_smt_type T }
  · have hName : s' = s := by
      have h := congrArg SmtModelKey.name hKey
      simpa using h
    have hTypeEq :
        __eo_to_smt_type T' = __eo_to_smt_type T := by
      have h := congrArg SmtModelKey.ty hKey
      simpa using h
    subst s'
    have hTEq : T' = T :=
      eo_type_eq_of_smt_type_eq_of_type_wf hWF hTypeEq
    subst T'
    rcases hFree with hNotDiff | hBound
    · have hFindFalse :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons diff
                (Term.Var (Term.String s) T)) =
            Term.Boolean false :=
        eoSmtVarEnv_find_false_of_termMem hDiffEnv
          (termVarString_ne_stuck s T) hMem
      rw [hFindFalse] at hNotDiff
      cases hNotDiff
    · have hConcatEq :
          __eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil = y :=
        eo_list_concat_nil_right_eq hYEnv
      rw [hConcatEq] at hBound
      have hMemY :
          EoSmtVarEnvTermMem (Term.Var (Term.String s) T) y :=
        hYEnv.termMem_of_find_false (termVarString_ne_stuck s T) hBound
      exact False.elim (hNotY hMemY)
  · simpa [native_model_var_lookup, native_model_push, hKey]

private theorem model_agrees_for_free_check_push_of_watch_mem_nil
    (watch : Term) {watchVars : List SmtVarKey}
    (hWatchEnv : EoSmtVarEnv watch watchVars)
    (M : SmtModel) (s : native_String) (T : Term) (v : SmtValue)
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hMem :
      EoSmtVarEnvTermMem (Term.Var (Term.String s) T) watch) :
    model_agrees_for_free_check watch Term.__eo_List_nil
      (native_model_push M s (__eo_to_smt_type T) v) M := by
  refine
    ⟨model_agrees_on_globals_symm
      (model_agrees_on_globals_push M s (__eo_to_smt_type T) v), ?_⟩
  intro s' T' hFree
  by_cases hKey :
      ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
        SmtModelKey) =
        { isVar := true, name := s, ty := __eo_to_smt_type T }
  · have hName : s' = s := by
      have h := congrArg SmtModelKey.name hKey
      simpa using h
    have hTypeEq :
        __eo_to_smt_type T' = __eo_to_smt_type T := by
      have h := congrArg SmtModelKey.ty hKey
      simpa using h
    subst s'
    have hTEq : T' = T :=
      eo_type_eq_of_smt_type_eq_of_type_wf hWF hTypeEq
    subst T'
    rcases hFree with hNotWatch | hBound
    · have hFindFalse :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons watch
                (Term.Var (Term.String s) T)) =
            Term.Boolean false :=
        eoSmtVarEnv_find_false_of_termMem hWatchEnv
          (termVarString_ne_stuck s T) hMem
      rw [hFindFalse] at hNotWatch
      cases hNotWatch
    · simp [__eo_list_find, __eo_list_find_rec, __eo_is_neg,
        __eo_requires, __eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_ok, native_ite, native_teq, native_not, SmtEval.native_not,
        native_zlt, SmtEval.native_zlt] at hBound
  · simpa [native_model_var_lookup, native_model_push, hKey]

private theorem smtx_eval_eo_to_smt_exists_unused_of_rel :
    ∀ {qs : Term} {qVars : List SmtVarKey},
      EoSmtVarEnv qs qVars ->
        (watch bvs : Term) ->
        (M : SmtModel) ->
        model_total_typed M ->
        (body : SmtTerm) ->
        __smtx_typeof (__eo_to_smt_exists qs body) = SmtType.Bool ->
        (∀ M N,
          model_agrees_for_free_check watch bvs M N ->
            __smtx_model_eval M body = __smtx_model_eval N body) ->
        (∀ M' s T v,
          EoSmtVarEnvTermMem (Term.Var (Term.String s) T) qs ->
            model_agrees_for_free_check watch bvs
              (native_model_push M' s (__eo_to_smt_type T) v) M') ->
        __smtx_model_eval M (__eo_to_smt_exists qs body) =
          __smtx_model_eval M body
  | _, _, EoSmtVarEnv.nil, watch, bvs, M, _hM, body, _hTy,
      hBody, _hRelPush =>
      by
        exact hBody M M (model_agrees_for_free_check_refl watch bvs M)
  | _, _, EoSmtVarEnv.cons (s := s) (T := T) (env := tail) hTail,
      watch, bvs, M, hM, body, hTy, hBody, hRelPush =>
      by
        have hTailTy :
            __smtx_typeof (__eo_to_smt_exists tail body) =
              SmtType.Bool :=
          smtx_typeof_exists_tail_bool_of_cons_bool s T tail body hTy
        have hWF :
            __smtx_type_wf (__eo_to_smt_type T) = true :=
          smtx_type_wf_of_exists_cons_bool s T tail body hTy
        have hDropHead :
            __smtx_model_eval M
                (SmtTerm.exists s (__eo_to_smt_type T)
                  (__eo_to_smt_exists tail body)) =
              __smtx_model_eval M (__eo_to_smt_exists tail body) := by
          apply smtx_eval_exists_unused_of_body_invariant M hM
            s (__eo_to_smt_type T) (__eo_to_smt_exists tail body)
            hWF hTailTy
          intro v _hvTy _hvCan
          exact
            smtx_model_eval_eo_to_smt_exists_eq_of_rel
              (model_agrees_for_free_check watch bvs) body
              (fun M₁ N₁ s₁ T₁ v₁ hRel =>
                model_agrees_for_free_check_push_same watch bvs
                  M₁ N₁ s₁ T₁ v₁ hRel)
              hBody tail
              (native_model_push M s (__eo_to_smt_type T) v) M
              (hRelPush M s T v (Or.inl rfl))
        have hDropTail :
            __smtx_model_eval M (__eo_to_smt_exists tail body) =
              __smtx_model_eval M body :=
          smtx_eval_eo_to_smt_exists_unused_of_rel hTail watch bvs M hM
            body hTailTy hBody
            (by
              intro M' s' T' v hMem
              exact hRelPush M' s' T' v (Or.inr hMem))
        calc
          __smtx_model_eval M
              (__eo_to_smt_exists
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) tail)
                body)
              =
            __smtx_model_eval M
              (SmtTerm.exists s (__eo_to_smt_type T)
                (__eo_to_smt_exists tail body)) := by
              rfl
          _ = __smtx_model_eval M (__eo_to_smt_exists tail body) :=
              hDropHead
          _ = __smtx_model_eval M body := hDropTail

private theorem smtx_eval_eo_to_smt_exists_prefix_drop_suffix_of_rel :
    ∀ {pre : Term} {preVars : List SmtVarKey},
      EoSmtVarEnv pre preVars ->
        (suffix watch bvs : Term) ->
        ∀ {suffixVars : List SmtVarKey},
        EoSmtVarEnv suffix suffixVars ->
        (M : SmtModel) ->
        model_total_typed M ->
        (body : SmtTerm) ->
        __smtx_typeof
            (__eo_to_smt_exists pre
              (__eo_to_smt_exists suffix body)) =
          SmtType.Bool ->
        (∀ M N,
          model_agrees_for_free_check watch bvs M N ->
            __smtx_model_eval M body =
              __smtx_model_eval N body) ->
        (∀ M' s T v,
          EoSmtVarEnvTermMem (Term.Var (Term.String s) T) suffix ->
            model_agrees_for_free_check watch bvs
              (native_model_push M' s (__eo_to_smt_type T) v) M') ->
        __smtx_model_eval M
            (__eo_to_smt_exists pre
              (__eo_to_smt_exists suffix body)) =
          __smtx_model_eval M (__eo_to_smt_exists pre body)
  | _, _, EoSmtVarEnv.nil, suffix, watch, bvs, suffixVars, hSuffix,
      M, hM, body, hTy, hBody, hRelPush =>
      by
        have hSuffixTy :
            __smtx_typeof (__eo_to_smt_exists suffix body) =
              SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        simpa [__eo_to_smt_exists] using
          smtx_eval_eo_to_smt_exists_unused_of_rel hSuffix watch bvs
            M hM body hSuffixTy hBody hRelPush
  | _, _, EoSmtVarEnv.cons (s := s) (T := T) (env := tail) hTail,
      suffix, watch, bvs, suffixVars, hSuffix, M, hM, body, hTy,
      hBody, hRelPush =>
      by
        have hTailTy :
            __smtx_typeof
                (__eo_to_smt_exists tail
                  (__eo_to_smt_exists suffix body)) =
              SmtType.Bool :=
          smtx_typeof_exists_tail_bool_of_cons_bool s T tail
            (__eo_to_smt_exists suffix body) hTy
        have hWF :
            __smtx_type_wf (__eo_to_smt_type T) = true :=
          smtx_type_wf_of_exists_cons_bool s T tail
            (__eo_to_smt_exists suffix body) hTy
        change
          __smtx_model_eval M
              (SmtTerm.exists s (__eo_to_smt_type T)
                (__eo_to_smt_exists tail
                  (__eo_to_smt_exists suffix body))) =
            __smtx_model_eval M
              (SmtTerm.exists s (__eo_to_smt_type T)
                (__eo_to_smt_exists tail body))
        exact smtx_model_eval_exists_congr M s (__eo_to_smt_type T)
          (__eo_to_smt_exists tail (__eo_to_smt_exists suffix body))
          (__eo_to_smt_exists tail body)
          (by
            intro v hvTy hvCan
            have hvCanonical : __smtx_value_canonical v := by
              rw [value_canonical_bool_eq_true]
              exact hvCan
            exact
              smtx_eval_eo_to_smt_exists_prefix_drop_suffix_of_rel
                hTail suffix watch bvs hSuffix
                (native_model_push M s (__eo_to_smt_type T) v)
                (model_total_typed_push hM s (__eo_to_smt_type T) v
                  hWF hvTy hvCanonical)
                body hTailTy hBody hRelPush)

private theorem smtx_eval_qexists_concat_drop_suffix_of_rel
    (watch bvs : Term) (M : SmtModel) (hM : model_total_typed M)
    (y diff F : Term) {yVars diffVars : List SmtVarKey}
    (hYEnv : EoSmtVarEnv y yVars)
    (hDiffEnv : EoSmtVarEnv diff diffVars)
    (hy : y ≠ Term.__eo_List_nil)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (qexists (__eo_list_concat Term.__eo_List_cons y diff) F)) =
        SmtType.Bool)
    (hBody :
      ∀ M N,
        model_agrees_for_free_check watch bvs M N ->
          __smtx_model_eval M (__eo_to_smt F) =
            __smtx_model_eval N (__eo_to_smt F))
    (hRelPush :
      ∀ M' s T v,
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) diff ->
          model_agrees_for_free_check watch bvs
            (native_model_push M' s (__eo_to_smt_type T) v) M') :
    __smtx_model_eval M
        (__eo_to_smt
          (qexists (__eo_list_concat Term.__eo_List_cons y diff) F)) =
      __smtx_model_eval M (__eo_to_smt (qexists y F)) := by
  have hConcatNe :
      __eo_list_concat Term.__eo_List_cons y diff ≠
        Term.__eo_List_nil :=
    eo_list_concat_ne_nil_of_left_env_ne_nil hYEnv hDiffEnv hy
  have hConcatEq :=
    eo_to_smt_exists_concat_eq (__eo_to_smt F) hYEnv hDiffEnv
  have hExistsTy :
      __smtx_typeof
          (__eo_to_smt_exists y
            (__eo_to_smt_exists diff (__eo_to_smt F))) =
        SmtType.Bool := by
    have hTyConcat :
        __smtx_typeof
            (__eo_to_smt_exists
              (__eo_list_concat Term.__eo_List_cons y diff)
              (__eo_to_smt F)) =
          SmtType.Bool := by
      simpa [eo_to_smt_exists_eq
          (__eo_list_concat Term.__eo_List_cons y diff) F hConcatNe]
        using hTy
    simpa [hConcatEq] using hTyConcat
  rw [eo_to_smt_exists_eq
    (__eo_list_concat Term.__eo_List_cons y diff) F hConcatNe]
  rw [eo_to_smt_exists_eq y F hy]
  rw [hConcatEq]
  exact smtx_eval_eo_to_smt_exists_prefix_drop_suffix_of_rel
    hYEnv diff watch bvs hDiffEnv M hM (__eo_to_smt F)
    hExistsTy hBody hRelPush

private theorem smtx_eval_qforall_concat_drop_suffix_of_rel
    (watch bvs : Term) (M : SmtModel) (hM : model_total_typed M)
    (y diff F : Term) {yVars diffVars : List SmtVarKey}
    (hYEnv : EoSmtVarEnv y yVars)
    (hDiffEnv : EoSmtVarEnv diff diffVars)
    (hy : y ≠ Term.__eo_List_nil)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (qforall (__eo_list_concat Term.__eo_List_cons y diff) F)) =
        SmtType.Bool)
    (hBody :
      ∀ M N,
        model_agrees_for_free_check watch bvs M N ->
          __smtx_model_eval M (__eo_to_smt F) =
            __smtx_model_eval N (__eo_to_smt F))
    (hRelPush :
      ∀ M' s T v,
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) diff ->
          model_agrees_for_free_check watch bvs
            (native_model_push M' s (__eo_to_smt_type T) v) M') :
    __smtx_model_eval M
        (__eo_to_smt
          (qforall (__eo_list_concat Term.__eo_List_cons y diff) F)) =
      __smtx_model_eval M (__eo_to_smt (qforall y F)) := by
  have hConcatNe :
      __eo_list_concat Term.__eo_List_cons y diff ≠
        Term.__eo_List_nil :=
    eo_list_concat_ne_nil_of_left_env_ne_nil hYEnv hDiffEnv hy
  have hConcatEq :=
    eo_to_smt_exists_concat_eq (SmtTerm.not (__eo_to_smt F))
      hYEnv hDiffEnv
  have hNN :
      __smtx_typeof
          (__eo_to_smt
            (qforall (__eo_list_concat Term.__eo_List_cons y diff) F)) ≠
        SmtType.None := by
    rw [hTy]
    simp
  have hExistsTyConcat :
      __smtx_typeof
          (__eo_to_smt_exists
            (__eo_list_concat Term.__eo_List_cons y diff)
            (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool :=
    qforall_inner_exists_bool_of_non_none
      (__eo_list_concat Term.__eo_List_cons y diff) F hNN
  have hExistsTy :
      __smtx_typeof
          (__eo_to_smt_exists y
            (__eo_to_smt_exists diff (SmtTerm.not (__eo_to_smt F)))) =
        SmtType.Bool := by
    simpa [hConcatEq] using hExistsTyConcat
  have hNotBody :
      ∀ M N,
        model_agrees_for_free_check watch bvs M N ->
          __smtx_model_eval M (SmtTerm.not (__eo_to_smt F)) =
            __smtx_model_eval N (SmtTerm.not (__eo_to_smt F)) := by
    intro M' N' hRel
    simp [__smtx_model_eval, hBody M' N' hRel]
  have hDrop :
      __smtx_model_eval M
          (__eo_to_smt_exists y
            (__eo_to_smt_exists diff (SmtTerm.not (__eo_to_smt F)))) =
        __smtx_model_eval M
          (__eo_to_smt_exists y (SmtTerm.not (__eo_to_smt F))) :=
    smtx_eval_eo_to_smt_exists_prefix_drop_suffix_of_rel
      hYEnv diff watch bvs hDiffEnv M hM
      (SmtTerm.not (__eo_to_smt F)) hExistsTy hNotBody hRelPush
  rw [eo_to_smt_forall_eq
    (__eo_list_concat Term.__eo_List_cons y diff) F hConcatNe]
  rw [eo_to_smt_forall_eq y F hy]
  rw [hConcatEq]
  simp [__smtx_model_eval, hDrop]

private theorem smtx_eval_qterm_concat_drop_suffix_of_rel
    (watch bvs : Term) (M : SmtModel) (hM : model_total_typed M)
    (Q y diff F : Term) {yVars diffVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hYEnv : EoSmtVarEnv y yVars)
    (hDiffEnv : EoSmtVarEnv diff diffVars)
    (hy : y ≠ Term.__eo_List_nil)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (qterm Q (__eo_list_concat Term.__eo_List_cons y diff) F)) =
        SmtType.Bool)
    (hBody :
      ∀ M N,
        model_agrees_for_free_check watch bvs M N ->
          __smtx_model_eval M (__eo_to_smt F) =
            __smtx_model_eval N (__eo_to_smt F))
    (hRelPush :
      ∀ M' s T v,
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) diff ->
          model_agrees_for_free_check watch bvs
            (native_model_push M' s (__eo_to_smt_type T) v) M') :
    __smtx_model_eval M
        (__eo_to_smt
          (qterm Q (__eo_list_concat Term.__eo_List_cons y diff) F)) =
      __smtx_model_eval M (__eo_to_smt (qterm Q y F)) := by
  rcases hQ with hQ | hQ
  · subst Q
    exact smtx_eval_qforall_concat_drop_suffix_of_rel watch bvs M hM
      y diff F hYEnv hDiffEnv hy (by simpa [qforall] using hTy)
      hBody hRelPush
  · subst Q
    exact smtx_eval_qexists_concat_drop_suffix_of_rel watch bvs M hM
      y diff F hYEnv hDiffEnv hy (by simpa [qexists] using hTy)
      hBody hRelPush

private theorem smtx_eval_qterm_setof_perm_drop_suffix_of_rel
    (watch bvs : Term) (M : SmtModel) (hM : model_total_typed M)
    (Q x y diff F : Term)
    {xVars setVars yVars diffVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hXEnv : EoSmtVarEnv x xVars)
    (hSetEnv :
      EoSmtVarEnv (__eo_list_setof Term.__eo_List_cons x) setVars)
    (hYEnv : EoSmtVarEnv y yVars)
    (hDiffEnv : EoSmtVarEnv diff diffVars)
    (hPerm : setVars.Perm (yVars ++ diffVars))
    (hx : x ≠ Term.__eo_List_nil)
    (hy : y ≠ Term.__eo_List_nil)
    (hConcatTy :
      __smtx_typeof
          (__eo_to_smt
            (qterm Q (__eo_list_concat Term.__eo_List_cons y diff) F)) =
        SmtType.Bool)
    (hBody :
      ∀ M N,
        model_agrees_for_free_check watch bvs M N ->
          __smtx_model_eval M (__eo_to_smt F) =
            __smtx_model_eval N (__eo_to_smt F))
    (hRelPush :
      ∀ M' s T v,
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) diff ->
          model_agrees_for_free_check watch bvs
            (native_model_push M' s (__eo_to_smt_type T) v) M') :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M (__eo_to_smt (qterm Q y F)) := by
  have hToConcat :
      __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
        __smtx_model_eval M
          (__eo_to_smt
            (qterm Q (__eo_list_concat Term.__eo_List_cons y diff) F)) :=
    smtx_model_eval_qterm_setof_perm_concat M Q x y diff F hQ
      hXEnv hSetEnv hYEnv hDiffEnv hPerm hx hy
  have hDrop :
      __smtx_model_eval M
          (__eo_to_smt
            (qterm Q (__eo_list_concat Term.__eo_List_cons y diff) F)) =
        __smtx_model_eval M (__eo_to_smt (qterm Q y F)) :=
    smtx_eval_qterm_concat_drop_suffix_of_rel watch bvs M hM Q y diff F
      hQ hYEnv hDiffEnv hy hConcatTy hBody hRelPush
  exact hToConcat.trans hDrop

private theorem smtx_eval_qterm_setof_perm_drop_exact_diff_of_rel
    (M : SmtModel) (hM : model_total_typed M)
    (Q x y F : Term)
    {xVars setVars yVars diffVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hXEnv : EoSmtVarEnv x xVars)
    (hSetEnv :
      EoSmtVarEnv (__eo_list_setof Term.__eo_List_cons x) setVars)
    (hYEnv : EoSmtVarEnv y yVars)
    (hDiffEnv :
      EoSmtVarEnv
        (__eo_list_diff Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y)
        diffVars)
    (hPerm : setVars.Perm (yVars ++ diffVars))
    (hx : x ≠ Term.__eo_List_nil)
    (hy : y ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool)
    (hBody :
      ∀ M N,
        model_agrees_for_free_check
            (__eo_list_diff Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y)
            (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil)
            M N ->
          __smtx_model_eval M (__eo_to_smt F) =
            __smtx_model_eval N (__eo_to_smt F)) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M (__eo_to_smt (qterm Q y F)) := by
  let diff :=
    __eo_list_diff Term.__eo_List_cons
      (__eo_list_setof Term.__eo_List_cons x) y
  have hConcatEnv :
      EoSmtVarEnv (__eo_list_concat Term.__eo_List_cons y diff)
        (yVars ++ diffVars) :=
    EoSmtVarEnv.concat hYEnv (by simpa [diff] using hDiffEnv)
  have hConcatNe :
      __eo_list_concat Term.__eo_List_cons y diff ≠
        Term.__eo_List_nil :=
    eo_list_concat_ne_nil_of_left_env_ne_nil hYEnv
      (by simpa [diff] using hDiffEnv) hy
  have hConcatTy :
      __smtx_typeof
          (__eo_to_smt
            (qterm Q (__eo_list_concat Term.__eo_List_cons y diff) F)) =
        SmtType.Bool :=
    smtx_typeof_qterm_setof_perm_concat Q x y diff F hQ hXEnv hSetEnv
      hYEnv (by simpa [diff] using hDiffEnv) hPerm hx hy hTy
  refine
    smtx_eval_qterm_setof_perm_drop_suffix_of_rel
      diff
      (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil)
      M hM Q x y diff F hQ hXEnv hSetEnv hYEnv
      (by simpa [diff] using hDiffEnv) hPerm hx hy
      (by simpa [diff] using hConcatTy) hBody ?_
  intro M' s T v hMem
  have hMemConcat :
      EoSmtVarEnvTermMem (Term.Var (Term.String s) T)
        (__eo_list_concat Term.__eo_List_cons y diff) :=
    eoSmtVarEnvTermMem_concat_right hYEnv
      (by simpa [diff] using hDiffEnv) hMem
  have hWF :
      __smtx_type_wf (__eo_to_smt_type T) = true :=
    smtx_type_wf_of_qterm_binder_mem_bool Q
      (__eo_list_concat Term.__eo_List_cons y diff) F hQ
      hConcatEnv hConcatNe (by simpa [diff] using hConcatTy) hMemConcat
  have hNotY :
      ¬ EoSmtVarEnvTermMem (Term.Var (Term.String s) T) y :=
    eoSmtVarEnvTermMem_diff_setof_not_right hXEnv hYEnv
      (by simpa [diff] using hMem)
  exact model_agrees_for_free_check_push_of_diff_mem
    diff y (by simpa [diff] using hDiffEnv) hYEnv M' s T v hWF hMem
    hNotY

private theorem smtx_eval_qexists_unused_of_rel
    (watch bvs : Term) (M : SmtModel) (hM : model_total_typed M)
    (x F : Term) {xVars : List SmtVarKey}
    (hEnv : EoSmtVarEnv x xVars)
    (hTy : __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool)
    (hBody :
      ∀ M N,
        model_agrees_for_free_check watch bvs M N ->
          __smtx_model_eval M (__eo_to_smt F) =
            __smtx_model_eval N (__eo_to_smt F))
    (hRelPush :
      ∀ M' s T v,
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) x ->
          model_agrees_for_free_check watch bvs
            (native_model_push M' s (__eo_to_smt_type T) v) M') :
    __smtx_model_eval M (__eo_to_smt (qexists x F)) =
      __smtx_model_eval M (__eo_to_smt F) := by
  have hNN :
      __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None := by
    rw [hTy]
    simp
  have hx : x ≠ Term.__eo_List_nil :=
    qexists_non_nil_of_non_none x F hNN
  have hExistsTy :
      __smtx_typeof (__eo_to_smt_exists x (__eo_to_smt F)) =
        SmtType.Bool := by
    simpa [eo_to_smt_exists_eq x F hx] using hTy
  rw [eo_to_smt_exists_eq x F hx]
  exact smtx_eval_eo_to_smt_exists_unused_of_rel hEnv watch bvs M hM
    (__eo_to_smt F) hExistsTy hBody hRelPush

private theorem smtx_eval_qforall_unused_of_rel
    (watch bvs : Term) (M : SmtModel) (hM : model_total_typed M)
    (x F : Term) {xVars : List SmtVarKey}
    (hEnv : EoSmtVarEnv x xVars)
    (hTy : __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool)
    (hBodyTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (hBody :
      ∀ M N,
        model_agrees_for_free_check watch bvs M N ->
          __smtx_model_eval M (__eo_to_smt F) =
            __smtx_model_eval N (__eo_to_smt F))
    (hRelPush :
      ∀ M' s T v,
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) x ->
          model_agrees_for_free_check watch bvs
            (native_model_push M' s (__eo_to_smt_type T) v) M') :
    __smtx_model_eval M (__eo_to_smt (qforall x F)) =
      __smtx_model_eval M (__eo_to_smt F) := by
  have hNN :
      __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None := by
    rw [hTy]
    simp
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F hNN
  have hExistsTy :
      __smtx_typeof
          (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool :=
    qforall_inner_exists_bool_of_non_none x F hNN
  have hNotBody :
      ∀ M N,
        model_agrees_for_free_check watch bvs M N ->
          __smtx_model_eval M (SmtTerm.not (__eo_to_smt F)) =
            __smtx_model_eval N (SmtTerm.not (__eo_to_smt F)) := by
    intro M' N' hRel
    simp [__smtx_model_eval, hBody M' N' hRel]
  have hExistsDrop :
      __smtx_model_eval M
          (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        __smtx_model_eval M (SmtTerm.not (__eo_to_smt F)) :=
    smtx_eval_eo_to_smt_exists_unused_of_rel hEnv watch bvs M hM
      (SmtTerm.not (__eo_to_smt F)) hExistsTy hNotBody hRelPush
  rw [eo_to_smt_forall_eq x F hx]
  rw [__smtx_model_eval.eq_6, hExistsDrop]
  simpa [__smtx_model_eval] using
    smtx_eval_not_not_of_bool M hM (__eo_to_smt F) hBodyTy

private theorem smtx_eval_qterm_unused_of_rel
    (watch bvs : Term) (M : SmtModel) (hM : model_total_typed M)
    (Q x F : Term) {xVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hEnv : EoSmtVarEnv x xVars)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool)
    (hBodyTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (hBody :
      ∀ M N,
        model_agrees_for_free_check watch bvs M N ->
          __smtx_model_eval M (__eo_to_smt F) =
            __smtx_model_eval N (__eo_to_smt F))
    (hRelPush :
      ∀ M' s T v,
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) x ->
          model_agrees_for_free_check watch bvs
            (native_model_push M' s (__eo_to_smt_type T) v) M') :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M (__eo_to_smt F) := by
  rcases hQ with hQ | hQ
  · subst Q
    exact smtx_eval_qforall_unused_of_rel watch bvs M hM x F hEnv
      (by simpa [qforall] using hTy) hBodyTy hBody hRelPush
  · subst Q
    exact smtx_eval_qexists_unused_of_rel watch bvs M hM x F hEnv
      (by simpa [qexists] using hTy) hBody hRelPush

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

private theorem quant_unused_free_body_env_shape_of_no_free
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    (∃ xVars unusedVars,
      EoSmtVarEnv x xVars ∧
      EoSmtVarEnv (__eo_list_setof Term.__eo_List_cons x) unusedVars ∧
      G = F ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x ∧
      __contains_atomic_term_list_free_rec F
          (__eo_list_setof Term.__eo_List_cons x) Term.__eo_List_nil =
        Term.Boolean false) ∨
    ∃ y xVars setVars yVars unusedVars,
      EoSmtVarEnv x xVars ∧
      EoSmtVarEnv (__eo_list_setof Term.__eo_List_cons x) setVars ∧
      EoSmtVarEnv y yVars ∧
      EoSmtVarEnv
        (__eo_list_diff Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y)
        unusedVars ∧
      setVars.Perm (yVars ++ unusedVars) ∧
      G = qterm Q y F ∧
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
  rcases quantUnusedFormula_lhs_binder_env_of_quant Q x F G hQ hBool with
    ⟨xVars, hXEnv⟩
  rcases eoSmtVarEnv_setof_exists hXEnv with ⟨setVars, hSetEnv⟩
  rcases quant_unused_free_body_shape_of_no_free Q x F G hQ hNoFree
      hBool with
    hFallback | hQuant
  · rcases hFallback with ⟨hG, hGet, hNoFreeF⟩
    exact Or.inl
      ⟨xVars, setVars, hXEnv, hSetEnv, hG, hGet, hNoFreeF⟩
  · rcases hQuant with
      ⟨y, yVars, hG, hYEnv, hIncl, hGet, hNoFreeF⟩
    rcases minclude_env_diff_perm_append hSetEnv hYEnv hIncl with
      ⟨diffVars, hDiffEnv, hPerm⟩
    exact Or.inr
      ⟨y, xVars, setVars, yVars, diffVars, hXEnv, hSetEnv, hYEnv,
        hDiffEnv, hPerm, hG, hIncl, hGet, hNoFreeF⟩

private theorem qterm_binder_non_nil_of_bool
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool) :
    x ≠ Term.__eo_List_nil := by
  have hNN :
      __smtx_typeof (__eo_to_smt (qterm Q x F)) ≠ SmtType.None := by
    rw [hTy]
    simp
  rcases hQ with hQ | hQ
  · subst Q
    exact qforall_non_nil_of_non_none x F (by
      simpa [qforall] using hNN)
  · subst Q
    exact qexists_non_nil_of_non_none x F (by
      simpa [qexists] using hNN)

private def smtKeyEraseAll
    (key : SmtVarKey) (vars : List SmtVarKey) : List SmtVarKey :=
  vars.filter (fun key' => decide (key' ≠ key))

private theorem smtKeyEraseAll_mem_of_ne
    {key key' : SmtVarKey} {vars : List SmtVarKey}
    (hMem : key' ∈ vars) (hNe : key' ≠ key) :
    key' ∈ smtKeyEraseAll key vars := by
  simpa [smtKeyEraseAll, hMem, hNe]

private theorem smtKeyEraseAll_mem
    {key key' : SmtVarKey} {vars : List SmtVarKey}
    (hMem : key' ∈ smtKeyEraseAll key vars) :
    key' ∈ vars ∧ key' ≠ key := by
  simpa [smtKeyEraseAll] using hMem

private def smtTermFreeVars : SmtTerm -> List SmtVarKey
  | SmtTerm.None => []
  | SmtTerm.Boolean _ => []
  | SmtTerm.Numeral _ => []
  | SmtTerm.Rational _ => []
  | SmtTerm.String _ => []
  | SmtTerm.Binary _ _ => []
  | SmtTerm.Apply f x => smtTermFreeVars f ++ smtTermFreeVars x
  | SmtTerm.Var s T => [(s, T)]
  | SmtTerm.ite c t e =>
      smtTermFreeVars c ++ smtTermFreeVars t ++ smtTermFreeVars e
  | SmtTerm.eq x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.exists s T body =>
      smtKeyEraseAll (s, T) (smtTermFreeVars body)
  | SmtTerm.forall s T body =>
      smtKeyEraseAll (s, T) (smtTermFreeVars body)
  | SmtTerm.choice_nth s T body _ =>
      smtKeyEraseAll (s, T) (smtTermFreeVars body)
  | SmtTerm.map_diff x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.DtCons _ _ _ => []
  | SmtTerm.DtSel _ _ _ _ => []
  | SmtTerm.DtTester _ _ _ => []
  | SmtTerm.UConst _ _ => []
  | SmtTerm.not x => smtTermFreeVars x
  | SmtTerm.or x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.and x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.imp x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.xor x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm._at_purify x => smtTermFreeVars x
  | SmtTerm.plus x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.neg x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.mult x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.lt x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.leq x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.gt x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.geq x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.to_real x => smtTermFreeVars x
  | SmtTerm.to_int x => smtTermFreeVars x
  | SmtTerm.is_int x => smtTermFreeVars x
  | SmtTerm.abs x => smtTermFreeVars x
  | SmtTerm.uneg x => smtTermFreeVars x
  | SmtTerm.div x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.mod x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.multmult x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.divisible x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.int_pow2 x => smtTermFreeVars x
  | SmtTerm.int_log2 x => smtTermFreeVars x
  | SmtTerm.div_total x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.mod_total x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.multmult_total x y =>
      smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.select x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.store x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.concat x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.extract x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.repeat x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvnot x => smtTermFreeVars x
  | SmtTerm.bvand x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvor x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvnand x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvnor x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvxor x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvxnor x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvcomp x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvneg x => smtTermFreeVars x
  | SmtTerm.bvadd x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvmul x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvudiv x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvurem x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvsub x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvsdiv x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvsrem x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvsmod x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvult x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvule x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvugt x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvuge x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvslt x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvsle x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvsgt x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvsge x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvshl x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvlshr x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvashr x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.zero_extend x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.sign_extend x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.rotate_left x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.rotate_right x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvuaddo x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvnego x => smtTermFreeVars x
  | SmtTerm.bvsaddo x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvumulo x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvsmulo x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvusubo x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvssubo x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.bvsdivo x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.seq_empty _ => []
  | SmtTerm.str_len x => smtTermFreeVars x
  | SmtTerm.str_concat x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.str_substr x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.str_contains x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.str_replace x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.str_indexof x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.str_at x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.str_prefixof x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.str_suffixof x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.str_rev x => smtTermFreeVars x
  | SmtTerm.str_update x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.str_to_lower x => smtTermFreeVars x
  | SmtTerm.str_to_upper x => smtTermFreeVars x
  | SmtTerm.str_to_code x => smtTermFreeVars x
  | SmtTerm.str_from_code x => smtTermFreeVars x
  | SmtTerm.str_is_digit x => smtTermFreeVars x
  | SmtTerm.str_to_int x => smtTermFreeVars x
  | SmtTerm.str_from_int x => smtTermFreeVars x
  | SmtTerm.str_lt x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.str_leq x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.str_replace_all x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.str_replace_re x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.str_replace_re_all x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.str_indexof_re x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.str_indexof_re_split x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.re_allchar => []
  | SmtTerm.re_none => []
  | SmtTerm.re_all => []
  | SmtTerm.str_to_re x => smtTermFreeVars x
  | SmtTerm.re_mult x => smtTermFreeVars x
  | SmtTerm.re_plus x => smtTermFreeVars x
  | SmtTerm.re_exp x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.re_opt x => smtTermFreeVars x
  | SmtTerm.re_comp x => smtTermFreeVars x
  | SmtTerm.re_range x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.re_concat x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.re_inter x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.re_union x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.re_diff x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.re_loop x y z =>
      smtTermFreeVars x ++ smtTermFreeVars y ++ smtTermFreeVars z
  | SmtTerm.str_in_re x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.seq_unit x => smtTermFreeVars x
  | SmtTerm.seq_nth x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.set_empty _ => []
  | SmtTerm.set_singleton x => smtTermFreeVars x
  | SmtTerm.set_union x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.set_inter x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.set_minus x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.set_member x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.set_subset x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.qdiv x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.qdiv_total x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.int_to_bv x y => smtTermFreeVars x ++ smtTermFreeVars y
  | SmtTerm.ubv_to_int x => smtTermFreeVars x
  | SmtTerm.sbv_to_int x => smtTermFreeVars x

private theorem smtTermClosedIn_binder_freeVars
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hBody : SmtTermClosedIn (smtTermFreeVars body) body) :
    SmtTermClosedIn
      ((s, T) :: smtKeyEraseAll (s, T) (smtTermFreeVars body)) body := by
  exact SmtTermClosedIn.mono
    (vars := smtTermFreeVars body)
    (vars' := (s, T) :: smtKeyEraseAll (s, T)
      (smtTermFreeVars body))
    (by
      intro s' T' hMem
      by_cases hEq : (s', T') = (s, T)
      · cases hEq
        exact List.Mem.head _
      · exact List.Mem.tail _ (smtKeyEraseAll_mem_of_ne hMem hEq))
    hBody

private theorem smtTermClosedIn_freeVars
    (t : SmtTerm) :
    SmtTermClosedIn (smtTermFreeVars t) t := by
  let rec go (t : SmtTerm) :
      SmtTermClosedIn (smtTermFreeVars t) t := by
    cases t <;> simp [smtTermFreeVars, SmtTermClosedIn]
    case «exists» s T body =>
      exact smtTermClosedIn_binder_freeVars s T body (go body)
    case «forall» s T body =>
      exact smtTermClosedIn_binder_freeVars s T body (go body)
    case choice_nth s T body n =>
      exact smtTermClosedIn_binder_freeVars s T body (go body)
    all_goals
      first
      | exact go _
      | constructor
        · exact (
            SmtTermClosedIn.mono
              (by intro s T hMem; simp [hMem])
              (go _))
        · constructor
          · exact (
              SmtTermClosedIn.mono
                (by intro s T hMem; simp [hMem])
                (go _))
          · exact (
              SmtTermClosedIn.mono
                (by intro s T hMem; simp [hMem])
                (go _))
      | constructor
        · exact (
            SmtTermClosedIn.mono
              (by intro s T hMem; simp [hMem])
              (go _))
        · exact (
            SmtTermClosedIn.mono
              (by intro s T hMem; simp [hMem])
                (go _))
  exact go t

private theorem smtTermFreeVars_mem_of_closedIn
    {vars : List SmtVarKey} {t : SmtTerm} {key : SmtVarKey}
    (hClosed : SmtTermClosedIn vars t)
    (hMem : key ∈ smtTermFreeVars t) :
    key ∈ vars := by
  let rec go (t : SmtTerm) {vars : List SmtVarKey} {key : SmtVarKey}
      (hClosed : SmtTermClosedIn vars t)
      (hMem : key ∈ smtTermFreeVars t) :
      key ∈ vars := by
    cases t <;> simp [smtTermFreeVars, SmtTermClosedIn] at hClosed hMem
    case Var s T =>
      cases hMem
      exact hClosed
    case «exists» s T body =>
      rcases smtKeyEraseAll_mem hMem with ⟨hBodyMem, hNe⟩
      have hBodyVars := go body hClosed hBodyMem
      cases hBodyVars with
      | head => exact False.elim (hNe rfl)
      | tail _ hTail => exact hTail
    case «forall» s T body =>
      rcases smtKeyEraseAll_mem hMem with ⟨hBodyMem, hNe⟩
      have hBodyVars := go body hClosed hBodyMem
      cases hBodyVars with
      | head => exact False.elim (hNe rfl)
      | tail _ hTail => exact hTail
    case choice_nth s T body n =>
      rcases smtKeyEraseAll_mem hMem with ⟨hBodyMem, hNe⟩
      have hBodyVars := go body hClosed hBodyMem
      cases hBodyVars with
      | head => exact False.elim (hNe rfl)
      | tail _ hTail => exact hTail
    all_goals
      first
      | exact go _ hClosed hMem
      | rcases hClosed with ⟨hClosed₁, hClosed₂, hClosed₃⟩
        rcases hMem with hMem₁ | hMem₂ | hMem₃
        · exact go _ hClosed₁ hMem₁
        · exact go _ hClosed₂ hMem₂
        · exact go _ hClosed₃ hMem₃
      | rcases hClosed with ⟨hClosed₁, hClosed₂⟩
        rcases hMem with hMem₁ | hMem₂
        · exact go _ hClosed₁ hMem₁
        · exact go _ hClosed₂ hMem₂
  exact go t hClosed hMem

private theorem smtTermFreeVars_eo_to_smt_exists_subset_body :
    ∀ (vs : Term) (body : SmtTerm) {key : SmtVarKey},
      key ∈ smtTermFreeVars (__eo_to_smt_exists vs body) ->
        key ∈ smtTermFreeVars body
  | Term.__eo_List_nil, body, key, hMem =>
      by
        simpa [__eo_to_smt_exists] using hMem
  | Term.Apply f x, body, key, hMem =>
      by
        cases f <;>
          try
            (change key ∈ smtTermFreeVars SmtTerm.None at hMem
             simp [smtTermFreeVars] at hMem)
        case Apply g y =>
          cases g <;>
            try
              (change key ∈ smtTermFreeVars SmtTerm.None at hMem
               simp [smtTermFreeVars] at hMem)
          case __eo_List_cons =>
            cases y <;>
              try
                (change key ∈ smtTermFreeVars SmtTerm.None at hMem
                 simp [smtTermFreeVars] at hMem)
            case Var name T =>
              cases name <;>
                try
                  (change key ∈ smtTermFreeVars SmtTerm.None at hMem
                   simp [smtTermFreeVars] at hMem)
              case String s =>
                change
                  key ∈ smtTermFreeVars
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists x body)) at hMem
                rcases smtKeyEraseAll_mem hMem with ⟨hTailMem, _hNe⟩
                exact
                  smtTermFreeVars_eo_to_smt_exists_subset_body
                    x body hTailMem
  | Term.UOp _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.UOp1 _ _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.UOp2 _ _ _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.UOp3 _ _ _ _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.__eo_List, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.__eo_List_cons, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Bool, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Boolean _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Numeral _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Rational _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.String _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Binary _ _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Type, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Stuck, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.FunType, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Var _ _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.DatatypeType _ _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.DatatypeTypeRef _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.DtcAppType _ _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.DtCons _ _ _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.DtSel _ _ _ _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.USort _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.UConst _ _, body, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem

private theorem smtTermFreeVars_eo_to_smt_qterm_subset_body
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    {key : SmtVarKey}
    (hMem : key ∈ smtTermFreeVars (__eo_to_smt (qterm Q x F))) :
    key ∈ smtTermFreeVars (__eo_to_smt F) := by
  rcases hQ with hQ | hQ
  · subst Q
    by_cases hx : x = Term.__eo_List_nil
    · subst x
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
    · change
        key ∈ smtTermFreeVars (__eo_to_smt (qforall x F)) at hMem
      rw [eo_to_smt_forall_eq x F hx] at hMem
      change
        key ∈ smtTermFreeVars
          (SmtTerm.not
            (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F)))) at hMem
      have hInner :
          key ∈ smtTermFreeVars (SmtTerm.not (__eo_to_smt F)) :=
        smtTermFreeVars_eo_to_smt_exists_subset_body
          x (SmtTerm.not (__eo_to_smt F)) hMem
      simpa [smtTermFreeVars] using hInner
  · subst Q
    by_cases hx : x = Term.__eo_List_nil
    · subst x
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
    · change
        key ∈ smtTermFreeVars (__eo_to_smt (qexists x F)) at hMem
      rw [eo_to_smt_exists_eq x F hx] at hMem
      exact smtTermFreeVars_eo_to_smt_exists_subset_body
        x (__eo_to_smt F) hMem

private theorem smtTermFreeVars_eo_to_smt_distinct_pairs_subset :
    ∀ (s : SmtTerm) (xs : Term) {key : SmtVarKey},
      key ∈ smtTermFreeVars (__eo_to_smt_distinct_pairs s xs) ->
        key ∈ smtTermFreeVars s ∨
          key ∈ smtTermFreeVars (__eo_to_smt xs)
  | s, Term.Apply f xs, key, hMem =>
      by
        cases f <;>
          try
            (change key ∈ smtTermFreeVars SmtTerm.None at hMem
             simp [smtTermFreeVars] at hMem)
        case UOp op =>
          cases op <;>
            simp [__eo_to_smt_distinct_pairs, smtTermFreeVars] at hMem
        case Apply g x =>
          cases g <;>
            try
              (change key ∈ smtTermFreeVars SmtTerm.None at hMem
               simp [smtTermFreeVars] at hMem)
          case UOp op =>
            cases op <;>
              try
                (change key ∈ smtTermFreeVars SmtTerm.None at hMem
                 simp [smtTermFreeVars] at hMem)
            case _at__at_TypedList_cons =>
              change
                key ∈ smtTermFreeVars
                  (SmtTerm.and
                    (SmtTerm.not (SmtTerm.eq s (__eo_to_smt x)))
                    (__eo_to_smt_distinct_pairs s xs)) at hMem
              simp [smtTermFreeVars] at hMem
              rcases hMem with hMem | hMem | hMem
              · exact Or.inl hMem
              · exact Or.inr (by
                  change key ∈
                    smtTermFreeVars
                      (SmtTerm.Apply
                        (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
                        (__eo_to_smt xs))
                  simp [smtTermFreeVars, hMem])
              · rcases
                  smtTermFreeVars_eo_to_smt_distinct_pairs_subset
                    s xs hMem with
                  hS | hXs
                · exact Or.inl hS
                · exact Or.inr (by
                    change key ∈
                      smtTermFreeVars
                        (SmtTerm.Apply
                          (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
                          (__eo_to_smt xs))
                    simp [smtTermFreeVars, hXs])
  | s, Term.UOp _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.UOp1 _ _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.UOp2 _ _ _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.UOp3 _ _ _ _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.__eo_List, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.__eo_List_cons, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.__eo_List_nil, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.Bool, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.Boolean _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.Numeral _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.Rational _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.String _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.Binary _ _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.Type, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.Stuck, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.FunType, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.Var _ _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.DatatypeType _ _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.DatatypeTypeRef _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.DtcAppType _ _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.DtCons _ _ _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.DtSel _ _ _ _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.USort _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | s, Term.UConst _ _, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem

private theorem smtTermFreeVars_eo_to_smt_distinct_subset
    (xs : Term) {key : SmtVarKey}
    (hMem : key ∈ smtTermFreeVars (__eo_to_smt_distinct xs)) :
    key ∈ smtTermFreeVars (__eo_to_smt xs) := by
  cases xs <;>
    try
      (change key ∈ smtTermFreeVars SmtTerm.None at hMem
       simp [smtTermFreeVars] at hMem)
  case Apply f tail =>
    cases f <;>
      try
        (change key ∈ smtTermFreeVars SmtTerm.None at hMem
         simp [smtTermFreeVars] at hMem)
    case UOp op =>
      cases op <;>
        simp [__eo_to_smt_distinct, smtTermFreeVars] at hMem
    case Apply g x =>
      cases g <;>
        try
          (change key ∈ smtTermFreeVars SmtTerm.None at hMem
           simp [smtTermFreeVars] at hMem)
      case UOp op =>
        cases op <;>
          try
            (change key ∈ smtTermFreeVars SmtTerm.None at hMem
             simp [smtTermFreeVars] at hMem)
        case _at__at_TypedList_cons =>
          change
            key ∈ smtTermFreeVars
              (SmtTerm.and
                (__eo_to_smt_distinct_pairs (__eo_to_smt x) tail)
                (__eo_to_smt_distinct tail)) at hMem
          simp [smtTermFreeVars] at hMem
          rcases hMem with hMem | hMem
          · rcases
              smtTermFreeVars_eo_to_smt_distinct_pairs_subset
                (__eo_to_smt x) tail hMem with
              hX | hTail
            · change key ∈
                smtTermFreeVars
                  (SmtTerm.Apply
                    (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
                    (__eo_to_smt tail))
              simp [smtTermFreeVars, hX]
            · change key ∈
                smtTermFreeVars
                  (SmtTerm.Apply
                    (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
                    (__eo_to_smt tail))
              simp [smtTermFreeVars, hTail]
          · have hTail :
                key ∈ smtTermFreeVars (__eo_to_smt tail) :=
              smtTermFreeVars_eo_to_smt_distinct_subset tail hMem
            change key ∈
              smtTermFreeVars
                (SmtTerm.Apply
                  (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
                  (__eo_to_smt tail))
            simp [smtTermFreeVars, hTail]

private theorem smtTermFreeVars_eo_to_smt_apply_uop_subset_arg
    (op : UserOp) (a : Term) {key : SmtVarKey}
    (hMem :
      key ∈ smtTermFreeVars (__eo_to_smt (Term.Apply (Term.UOp op) a))) :
    key ∈ smtTermFreeVars (__eo_to_smt a) := by
  cases op <;>
    try
      (simpa [smtTermFreeVars] using hMem)
  case distinct =>
    change key ∈
      smtTermFreeVars
        (native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type a) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct a)) at hMem
    cases hElem :
        native_Teq (__eo_to_smt_typed_list_elem_type a) SmtType.None <;>
      simp [native_ite, hElem, smtTermFreeVars] at hMem
    exact smtTermFreeVars_eo_to_smt_distinct_subset a hMem
  case int_ispow2 =>
    change key ∈
      smtTermFreeVars
        (let t := __eo_to_smt a
        SmtTerm.and (SmtTerm.geq t (SmtTerm.Numeral 0))
          (SmtTerm.eq t (SmtTerm.int_pow2 (SmtTerm.int_log2 t)))) at hMem
    simpa [smtTermFreeVars] using hMem
  case _at_int_div_by_zero =>
    change key ∈
      smtTermFreeVars
        (SmtTerm.div (__eo_to_smt a) (SmtTerm.Numeral 0)) at hMem
    simpa [smtTermFreeVars] using hMem
  case _at_mod_by_zero =>
    change key ∈
      smtTermFreeVars
        (SmtTerm.mod (__eo_to_smt a) (SmtTerm.Numeral 0)) at hMem
    simpa [smtTermFreeVars] using hMem
  case _at_bvsize =>
    change key ∈
      smtTermFreeVars
        (native_ite
          (native_zleq 0
            (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt a))))
          (SmtTerm._at_purify
            (SmtTerm.Numeral
              (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt a)))))
          SmtTerm.None) at hMem
    cases hSize :
        native_zleq 0
          (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt a))) <;>
      simp [native_ite, hSize, smtTermFreeVars] at hMem
  case bvredand =>
    change key ∈
      smtTermFreeVars
        (let t := __eo_to_smt a
        SmtTerm.bvcomp t
          (SmtTerm.bvnot
            (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof t)) 0))) at hMem
    simpa [smtTermFreeVars] using hMem
  case bvredor =>
    change key ∈
      smtTermFreeVars
        (let t := __eo_to_smt a
        SmtTerm.bvnot
          (SmtTerm.bvcomp t
            (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof t)) 0))) at hMem
    simpa [smtTermFreeVars] using hMem
  case _at_strings_stoi_non_digit =>
    change key ∈
      smtTermFreeVars
        (SmtTerm.str_indexof_re (__eo_to_smt a)
          (SmtTerm.re_comp
            (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
              (SmtTerm.String (native_string_lit "9"))))
          (SmtTerm.Numeral 0)) at hMem
    simpa [smtTermFreeVars] using hMem
  case set_choose =>
    change key ∈
      smtTermFreeVars
        (let t := __eo_to_smt a
        SmtTerm.map_diff t
          (SmtTerm.set_empty
            (__eo_to_smt_set_elem_type (__smtx_typeof t)))) at hMem
    simpa [smtTermFreeVars] using hMem
  case set_is_empty =>
    change key ∈
      smtTermFreeVars
        (let t := __eo_to_smt a
        SmtTerm.eq t (SmtTerm.set_empty (__smtx_typeof t))) at hMem
    simpa [smtTermFreeVars] using hMem
  case set_is_singleton =>
    change key ∈
      smtTermFreeVars
        (let t := __eo_to_smt a
        SmtTerm.eq t
          (SmtTerm.set_singleton
            (SmtTerm.map_diff t
              (SmtTerm.set_empty
                (__eo_to_smt_set_elem_type (__smtx_typeof t)))))) at hMem
    simpa [smtTermFreeVars] using hMem
  case _at_div_by_zero =>
    change key ∈
      smtTermFreeVars
        (SmtTerm.qdiv (__eo_to_smt a)
          (SmtTerm.Rational (native_mk_rational 0 1))) at hMem
    simpa [smtTermFreeVars] using hMem

private theorem smtTermFreeVars_eo_to_smt__at_bv_empty
    (x y : SmtTerm) {key : SmtVarKey}
    (hMem : key ∈ smtTermFreeVars (__eo_to_smt__at_bv x y)) :
    False := by
  cases x <;> simp [__eo_to_smt__at_bv, smtTermFreeVars] at hMem
  case Numeral n =>
    cases y <;>
      simp [smtTermFreeVars, native_ite] at hMem
    case Numeral m =>
      by_cases hLe : native_zleq 0 m = true
      · simp [hLe, smtTermFreeVars] at hMem
      · have hLeFalse : native_zleq 0 m = false := by
          cases h : native_zleq 0 m <;> simp [h] at hLe ⊢
        simp [hLeFalse, smtTermFreeVars] at hMem

private theorem smtTermFreeVars_eo_to_smt_seq_empty_empty
    (T : SmtType) {key : SmtVarKey}
    (hMem : key ∈ smtTermFreeVars (__eo_to_smt_seq_empty T)) :
    False := by
  cases T <;> simp [__eo_to_smt_seq_empty, smtTermFreeVars] at hMem

private theorem smtTermFreeVars_eo_to_smt_set_empty_empty
    (T : SmtType) {key : SmtVarKey}
    (hMem : key ∈ smtTermFreeVars (__eo_to_smt_set_empty T)) :
    False := by
  cases T <;> simp [__eo_to_smt_set_empty, smtTermFreeVars] at hMem

private theorem smtTermFreeVars_eo_to_smt_witness_string_length_empty
    (x y z : Term) {key : SmtVarKey}
    (hMem :
      key ∈
        smtTermFreeVars
          (__eo_to_smt
            (Term.UOp3 UserOp3._at_witness_string_length x y z))) :
    False := by
  change key ∈
    smtTermFreeVars
      (native_ite (__eo_to_smt_nat_is_valid y)
        (native_ite (__eo_to_smt_nat_is_valid z)
          (SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type x)
            (SmtTerm.eq
              (SmtTerm.str_len
                (SmtTerm.Var (native_string_lit "@x")
                  (__eo_to_smt_type x)))
              (__eo_to_smt y))
            native_nat_zero)
          SmtTerm.None)
        SmtTerm.None) at hMem
  cases y <;>
    simp [__eo_to_smt_nat_is_valid, native_ite, smtTermFreeVars] at hMem
  case Numeral n =>
    by_cases hY : native_zleq 0 n = true
    · rw [hY] at hMem
      simp at hMem
      let zValid : native_Bool := __eo_to_smt_nat_is_valid z
      change key ∈
        smtTermFreeVars
          (if zValid = true then
            SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type x)
              ((SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type x)).str_len.eq
                (__eo_to_smt (Term.Numeral n))) native_nat_zero
          else SmtTerm.None) at hMem
      by_cases hZ : zValid = true
      · rw [hZ] at hMem
        simp [smtTermFreeVars] at hMem
        rcases smtKeyEraseAll_mem hMem with ⟨hRaw, hNe⟩
        simp at hRaw
        rcases hRaw with hRaw | hRaw
        · exact hNe hRaw
        · change key ∈ smtTermFreeVars (SmtTerm.Numeral n) at hRaw
          simp [smtTermFreeVars] at hRaw
      · rw [if_neg hZ] at hMem
        simp [smtTermFreeVars] at hMem
    · have hYFalse : native_zleq 0 n = false := by
        cases h : native_zleq 0 n <;> simp [h] at hY ⊢
      rw [hYFalse] at hMem
      simp [smtTermFreeVars] at hMem

private theorem smtx_typeof_eo_to_smt_list_cons_none
    (head tail : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt head))
          (__eo_to_smt tail)) =
      SmtType.None
  simp [__smtx_typeof, __smtx_typeof_apply]

private theorem smtx_typeof_smt_or_left_none_ne_bool
    {x y : SmtTerm}
    (hX : __smtx_typeof x = SmtType.None) :
    __smtx_typeof (SmtTerm.or x y) ≠ SmtType.Bool := by
  intro hBool
  simp [__smtx_typeof, hX, native_ite, native_Teq] at hBool

private theorem smtx_typeof_smt_and_left_none_ne_bool
    {x y : SmtTerm}
    (hX : __smtx_typeof x = SmtType.None) :
    __smtx_typeof (SmtTerm.and x y) ≠ SmtType.Bool := by
  intro hBool
  simp [__smtx_typeof, hX, native_ite, native_Teq] at hBool

private theorem smtx_typeof_smt_imp_left_none_ne_bool
    {x y : SmtTerm}
    (hX : __smtx_typeof x = SmtType.None) :
    __smtx_typeof (SmtTerm.imp x y) ≠ SmtType.Bool := by
  intro hBool
  simp [__smtx_typeof, hX, native_ite, native_Teq] at hBool

private theorem smtx_typeof_smt_xor_left_none_ne_bool
    {x y : SmtTerm}
    (hX : __smtx_typeof x = SmtType.None) :
    __smtx_typeof (SmtTerm.xor x y) ≠ SmtType.Bool := by
  intro hBool
  simp [__smtx_typeof, hX, native_ite, native_Teq] at hBool

private theorem smtx_typeof_smt_eq_left_none_ne_bool
    {x y : SmtTerm}
    (hX : __smtx_typeof x = SmtType.None) :
    __smtx_typeof (SmtTerm.eq x y) ≠ SmtType.Bool := by
  intro hBool
  simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard,
    hX, native_ite, native_Teq] at hBool

private theorem smtx_typeof_qor_list_arg_ne_bool
    (head tail y : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.or)
              (Term.Apply (Term.Apply Term.__eo_List_cons head) tail))
            y)) ≠ SmtType.Bool := by
  rw [eo_to_smt_or_eq]
  exact smtx_typeof_smt_or_left_none_ne_bool
    (smtx_typeof_eo_to_smt_list_cons_none head tail)

private theorem smtx_typeof_qand_list_arg_ne_bool
    (head tail y : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply Term.__eo_List_cons head) tail))
            y)) ≠ SmtType.Bool := by
  rw [eo_to_smt_and_eq]
  exact smtx_typeof_smt_and_left_none_ne_bool
    (smtx_typeof_eo_to_smt_list_cons_none head tail)

private theorem smtx_typeof_qimp_list_arg_ne_bool
    (head tail y : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.imp)
              (Term.Apply (Term.Apply Term.__eo_List_cons head) tail))
            y)) ≠ SmtType.Bool := by
  rw [eo_to_smt_imp_eq]
  exact smtx_typeof_smt_imp_left_none_ne_bool
    (smtx_typeof_eo_to_smt_list_cons_none head tail)

private theorem smtx_typeof_qxor_list_arg_ne_bool
    (head tail y : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.xor)
              (Term.Apply (Term.Apply Term.__eo_List_cons head) tail))
            y)) ≠ SmtType.Bool := by
  rw [eo_to_smt_xor_eq]
  exact smtx_typeof_smt_xor_left_none_ne_bool
    (smtx_typeof_eo_to_smt_list_cons_none head tail)

private theorem smtx_typeof_qeq_list_arg_ne_bool
    (head tail y : Term) :
    __smtx_typeof
        (__eo_to_smt
          (qeq (Term.Apply (Term.Apply Term.__eo_List_cons head) tail) y)) ≠
      SmtType.Bool := by
  rw [eo_to_smt_eq_eq]
  exact smtx_typeof_smt_eq_left_none_ne_bool
    (smtx_typeof_eo_to_smt_list_cons_none head tail)

private theorem smtTermFreeVars_eo_to_smt_quantifiers_skolemize_subset
    (t : SmtTerm) (n : native_Nat) {key : SmtVarKey}
    (hMem :
      key ∈ smtTermFreeVars (__eo_to_smt_quantifiers_skolemize t n)) :
    key ∈ smtTermFreeVars t := by
  cases t <;>
    simp [__eo_to_smt_quantifiers_skolemize, smtTermFreeVars] at hMem ⊢
  case «exists» s T body =>
    exact hMem

private theorem smtTermFreeVars_eo_to_smt_re_unfold_pos_component_subset :
    ∀ (s r : SmtTerm) (n : native_Nat) {key : SmtVarKey},
      key ∈ smtTermFreeVars
          (__eo_to_smt_re_unfold_pos_component s r n) ->
        key ∈ smtTermFreeVars s ∨ key ∈ smtTermFreeVars r
  | s, r, native_nat_zero, key, hMem =>
      by
        cases r <;>
          simp [__eo_to_smt_re_unfold_pos_component, smtTermFreeVars]
            at hMem ⊢
        exact hMem
  | s, r, native_nat_succ n, key, hMem =>
      by
        cases r <;>
          try
            (simp [__eo_to_smt_re_unfold_pos_component, smtTermFreeVars]
              at hMem)
        case re_concat r1 r2 =>
          let split := SmtTerm.str_indexof_re_split s r1 r2
          let suffix :=
            SmtTerm.str_substr s split
              (SmtTerm.neg (SmtTerm.str_len s) split)
          change key ∈
            smtTermFreeVars
              (__eo_to_smt_re_unfold_pos_component suffix r2 n) at hMem
          rcases
              smtTermFreeVars_eo_to_smt_re_unfold_pos_component_subset
                suffix r2 n hMem with
            hSuffix | hR2
          · simp [suffix, split, smtTermFreeVars] at hSuffix ⊢
            rcases hSuffix with hS | hRest
            · exact Or.inl hS
            rcases hRest with hR1 | hRest
            · exact Or.inr (Or.inl hR1)
            rcases hRest with hR2' | hRest
            · exact Or.inr (Or.inr hR2')
            rcases hRest with hS | hRest
            · exact Or.inl hS
            rcases hRest with hR1 | hR2'
            · exact Or.inr (Or.inl hR1)
            · exact Or.inr (Or.inr hR2')
          · simp [smtTermFreeVars, hR2]

private theorem smtTermFreeVars_eo_to_smt_re_unfold_pos_component_raw_subset
    (x y z : Term) {key : SmtVarKey}
    (hMem :
      key ∈
        smtTermFreeVars
          (__eo_to_smt
            (Term.UOp3 UserOp3._at_re_unfold_pos_component x y z))) :
    key ∈ smtTermFreeVars (__eo_to_smt x) ∨
      key ∈ smtTermFreeVars (__eo_to_smt y) := by
  let zValid : native_Bool := __eo_to_smt_nat_is_valid z
  change key ∈
    smtTermFreeVars
      (if zValid = true then
        (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x)
          (__eo_to_smt y) (__eo_to_smt_nat z))
      else SmtTerm.None) at hMem
  by_cases hZ : zValid = true
  · rw [if_pos hZ] at hMem
    exact
      smtTermFreeVars_eo_to_smt_re_unfold_pos_component_subset
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt_nat z) hMem
  · rw [if_neg hZ] at hMem
    simp [smtTermFreeVars] at hMem

private theorem smtTermFreeVars_eo_to_smt_array_deq_diff_subset
    (a : SmtTerm) (aT : SmtType) (b : SmtTerm) (bT : SmtType)
    {key : SmtVarKey}
    (hMem :
      key ∈ smtTermFreeVars (__eo_to_smt_array_deq_diff a aT b bT)) :
    key ∈ smtTermFreeVars a ∨ key ∈ smtTermFreeVars b := by
  cases aT <;> cases bT <;>
    simp [__eo_to_smt_array_deq_diff, smtTermFreeVars] at hMem ⊢
  case Map.Map =>
    exact hMem

private theorem smtTermFreeVars_eo_to_smt_sets_deq_diff_subset
    (a : SmtTerm) (aT : SmtType) (b : SmtTerm) (bT : SmtType)
    {key : SmtVarKey}
    (hMem :
      key ∈ smtTermFreeVars (__eo_to_smt_sets_deq_diff a aT b bT)) :
    key ∈ smtTermFreeVars a ∨ key ∈ smtTermFreeVars b := by
  cases aT <;> cases bT <;>
    simp [__eo_to_smt_sets_deq_diff, smtTermFreeVars] at hMem ⊢
  case Set.Set =>
    exact hMem

private theorem smtTermFreeVars_eo_to_smt_set_insert_subset :
    ∀ (xs : Term) (base : SmtTerm) {key : SmtVarKey},
      key ∈ smtTermFreeVars (__eo_to_smt_set_insert xs base) ->
        key ∈ smtTermFreeVars (__eo_to_smt xs) ∨
          key ∈ smtTermFreeVars base
  | Term.Apply f tail, base, key, hMem =>
      by
        cases f <;>
          try
            (change key ∈ smtTermFreeVars SmtTerm.None at hMem
             simp [smtTermFreeVars] at hMem)
        case UOp op =>
          cases op <;>
            try
              (change key ∈ smtTermFreeVars SmtTerm.None at hMem
               simp [smtTermFreeVars] at hMem)
          case _at__at_TypedList_nil =>
            change
              key ∈ smtTermFreeVars
                (native_ite
                  (native_Teq (__smtx_typeof base)
                    (SmtType.Set (__eo_to_smt_type tail)))
                  base SmtTerm.None) at hMem
            cases hTy :
                native_Teq (__smtx_typeof base)
                  (SmtType.Set (__eo_to_smt_type tail)) <;>
              simp [native_ite, hTy, smtTermFreeVars] at hMem
            exact Or.inr hMem
        case Apply g x =>
          cases g <;>
            try
              (change key ∈ smtTermFreeVars SmtTerm.None at hMem
               simp [smtTermFreeVars] at hMem)
          case UOp op =>
            cases op <;>
              try
                (change key ∈ smtTermFreeVars SmtTerm.None at hMem
                 simp [smtTermFreeVars] at hMem)
            case _at__at_TypedList_cons =>
              change
                key ∈ smtTermFreeVars
                  (SmtTerm.set_union
                    (SmtTerm.set_singleton (__eo_to_smt x))
                    (__eo_to_smt_set_insert tail base)) at hMem
              simp [smtTermFreeVars] at hMem
              rcases hMem with hMem | hMem
              · left
                change key ∈
                  smtTermFreeVars
                    (SmtTerm.Apply
                      (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
                      (__eo_to_smt tail))
                simp [smtTermFreeVars, hMem]
              · rcases
                  smtTermFreeVars_eo_to_smt_set_insert_subset
                    tail base hMem with
                hTail | hBase
                · left
                  change key ∈
                    smtTermFreeVars
                      (SmtTerm.Apply
                        (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
                        (__eo_to_smt tail))
                  simp [smtTermFreeVars, hTail]
                · exact Or.inr hBase
  | Term.UOp _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.UOp1 _ _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.UOp2 _ _ _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.UOp3 _ _ _ _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.__eo_List, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.__eo_List_cons, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.__eo_List_nil, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Bool, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Boolean _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Numeral _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Rational _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.String _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Binary _ _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Type, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Stuck, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.FunType, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.Var _ _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.DatatypeType _ _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.DatatypeTypeRef _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.DtcAppType _ _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.DtCons _ _ _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.DtSel _ _ _ _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.USort _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
  | Term.UConst _ _, base, key, hMem => by
      change key ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem

private theorem smtTermFreeVars_eo_to_smt_tuple_select_subset
    (T : SmtType) (n t : SmtTerm) {key : SmtVarKey}
    (hMem :
      key ∈ smtTermFreeVars (__eo_to_smt_tuple_select T n t)) :
    key ∈ smtTermFreeVars n ∨ key ∈ smtTermFreeVars t := by
  cases T <;> cases n <;>
    simp [__eo_to_smt_tuple_select, smtTermFreeVars] at hMem ⊢
  case Datatype.Numeral s d i =>
    cases hOk :
        native_and (native_streq s (native_string_lit "@Tuple"))
          (native_zleq 0 i) <;>
      simp [native_ite, hOk, smtTermFreeVars] at hMem
    exact hMem

private theorem smtTermFreeVars_eo_to_smt_tuple_prepend_rec_subset :
    ∀ (d : SmtDatatype) (tail : SmtTerm) (n : native_Nat)
      (acc : SmtTerm) {key : SmtVarKey},
      key ∈ smtTermFreeVars (__eo_to_smt_tuple_prepend_rec d tail n acc) ->
        key ∈ smtTermFreeVars tail ∨ key ∈ smtTermFreeVars acc
  | d, tail, native_nat_zero, acc, key, hMem =>
      by
        exact Or.inr hMem
  | d, tail, native_nat_succ n, acc, key, hMem =>
      by
        change key ∈ smtTermFreeVars
          (SmtTerm.Apply
            (__eo_to_smt_tuple_prepend_rec d tail n acc)
            (SmtTerm.Apply
              (SmtTerm.DtSel (native_string_lit "@Tuple") d
                native_nat_zero n)
              tail)) at hMem
        simp [smtTermFreeVars] at hMem
        rcases hMem with hMem | hMem
        · exact
            smtTermFreeVars_eo_to_smt_tuple_prepend_rec_subset
              d tail n acc hMem
        · exact Or.inl hMem

private theorem smtTermFreeVars_eo_to_smt_tuple_prepend_of_type_subset
    (T : SmtType) (h : SmtTerm) (hT : SmtType) (tail : SmtTerm)
    {key : SmtVarKey}
    (hMem :
      key ∈
        smtTermFreeVars
          (__eo_to_smt_tuple_prepend_of_type T h hT tail)) :
    key ∈ smtTermFreeVars h ∨ key ∈ smtTermFreeVars tail := by
  cases T <;>
    try
      (change key ∈ smtTermFreeVars SmtTerm.None at hMem
       simp [smtTermFreeVars] at hMem)
  case Datatype s d =>
    cases d <;>
      try
        (change key ∈ smtTermFreeVars SmtTerm.None at hMem
         simp [smtTermFreeVars] at hMem)
    case sum c rest =>
      cases rest <;>
        try
          (change key ∈ smtTermFreeVars SmtTerm.None at hMem
           simp [smtTermFreeVars] at hMem)
      case null =>
        change key ∈
          smtTermFreeVars
            (native_ite
              (native_and (native_streq s (native_string_lit "@Tuple"))
                (__smtx_type_wf
                  (SmtType.Datatype (native_string_lit "@Tuple")
                    (SmtDatatype.sum (SmtDatatypeCons.cons hT c)
                      SmtDatatype.null))))
              (__eo_to_smt_tuple_prepend_rec
                (SmtDatatype.sum c SmtDatatype.null) tail
                (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
                  native_nat_zero)
                (SmtTerm.Apply
                  (SmtTerm.DtCons (native_string_lit "@Tuple")
                    (SmtDatatype.sum (SmtDatatypeCons.cons hT c)
                      SmtDatatype.null)
                    native_nat_zero)
                  h))
              SmtTerm.None) at hMem
        cases hOk :
            native_and (native_streq s (native_string_lit "@Tuple"))
              (__smtx_type_wf
                (SmtType.Datatype (native_string_lit "@Tuple")
                  (SmtDatatype.sum (SmtDatatypeCons.cons hT c)
                    SmtDatatype.null))) <;>
          simp [native_ite, hOk, smtTermFreeVars] at hMem
        rcases
          smtTermFreeVars_eo_to_smt_tuple_prepend_rec_subset
            (SmtDatatype.sum c SmtDatatype.null) tail
            (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
              native_nat_zero)
            (SmtTerm.Apply
              (SmtTerm.DtCons (native_string_lit "@Tuple")
                (SmtDatatype.sum (SmtDatatypeCons.cons hT c)
                  SmtDatatype.null)
                native_nat_zero)
              h)
            hMem with
        hTail | hHead
        · exact Or.inr hTail
        · exact Or.inl hHead

private theorem smtTermFreeVars_eo_to_smt_tuple_prepend_subset
    (h tail : SmtTerm) {key : SmtVarKey}
    (hMem :
      key ∈
        smtTermFreeVars
          (__eo_to_smt_tuple_prepend h (__smtx_typeof h) tail)) :
    key ∈ smtTermFreeVars h ∨ key ∈ smtTermFreeVars tail := by
  exact
    smtTermFreeVars_eo_to_smt_tuple_prepend_of_type_subset
      (__smtx_typeof tail) h (__smtx_typeof h) tail hMem

private theorem smtExistsOfBinders_freeVars_body_and_not_binder :
    ∀ (binders : List SmtVarKey) (body : SmtTerm) {key : SmtVarKey},
      key ∈ smtTermFreeVars (smtExistsOfBinders binders body) ->
        key ∈ smtTermFreeVars body ∧ key ∉ binders
  | [], body, key, hMem =>
      by
        simp [smtExistsOfBinders] at hMem
        exact ⟨hMem, by simp⟩
  | b :: bs, body, key, hMem =>
      by
        rcases b with ⟨s, T⟩
        change
          key ∈ smtTermFreeVars
            (SmtTerm.exists s T (smtExistsOfBinders bs body)) at hMem
        rcases smtKeyEraseAll_mem hMem with ⟨hTailMem, hNe⟩
        rcases
            smtExistsOfBinders_freeVars_body_and_not_binder
              bs body hTailMem with
          ⟨hBodyMem, hNotTail⟩
        refine ⟨hBodyMem, ?_⟩
        intro hBinder
        cases hBinder with
        | head =>
            exact hNe rfl
        | tail _ hTail =>
            exact hNotTail hTail

private theorem smtTermFreeVars_eo_to_smt_exists_body_and_not_env
    {env : Term} {vars : List SmtVarKey} {body : SmtTerm}
    {key : SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hMem : key ∈ smtTermFreeVars (__eo_to_smt_exists env body)) :
    key ∈ smtTermFreeVars body ∧ key ∉ vars := by
  rw [eo_to_smt_exists_of_env body hEnv] at hMem
  exact smtExistsOfBinders_freeVars_body_and_not_binder vars body hMem

private theorem eoSmtVarEnv_key_mem_of_termMem
    {env : Term} {vars : List SmtVarKey}
    {s : native_String} {T : Term}
    (hEnv : EoSmtVarEnv env vars)
    (hMem : EoSmtVarEnvTermMem (Term.Var (Term.String s) T) env) :
    (s, __eo_to_smt_type T) ∈ vars :=
  EoSmtVarEnv.mem_of_closed_var hEnv
    (hEnv.eo_is_closed_rec_var_of_termMem hMem)

private theorem eoSmtVarEnv_termMem_of_key_mem
    {env : Term} {vars : List SmtVarKey}
    {s : native_String} {U : SmtType}
    (hEnv : EoSmtVarEnv env vars)
    (hMem : (s, U) ∈ vars) :
    ∃ T,
      U = __eo_to_smt_type T ∧
        EoSmtVarEnvTermMem (Term.Var (Term.String s) T) env := by
  induction hEnv with
  | nil =>
      cases hMem
  | cons hTail ih =>
      rename_i s' T' tail tailVars
      cases hMem with
      | head =>
          exact ⟨T', rfl, Or.inl rfl⟩
      | tail _ hTailMem =>
          rcases ih hTailMem with ⟨T, hU, hTermMem⟩
          exact ⟨T, hU, Or.inr hTermMem⟩

private theorem smtTermFreeVars_allowed_of_closedIn_env
    {env : Term} {vars : List SmtVarKey} {F xs : Term}
    (hEnv : EoSmtVarEnv env vars)
    (hClosed : SmtTermClosedIn vars (__eo_to_smt F)) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt F) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons env
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  have hKey : (s, U) ∈ vars :=
    smtTermFreeVars_mem_of_closedIn hClosed hMem
  rcases eoSmtVarEnv_termMem_of_key_mem hEnv hKey with
    ⟨T, hU, hTermMem⟩
  refine ⟨T, hU, Or.inr ?_⟩
  exact eoSmtVarEnv_find_false_of_termMem hEnv
    (termVarString_ne_stuck s T) hTermMem

private theorem smtTermFreeVars_allowed_of_eo_closed_env
    (F xs env : Term) {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hClosed :
      __eo_is_closed_rec F env = Term.Boolean true) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt F) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons env
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  exact smtTermFreeVars_allowed_of_closedIn_env hEnv
    (smtTermClosedIn_of_eo_is_closed_rec_perm
      (hEnv := EoSmtVarEnvPerm.of_exact hEnv) hClosed)

private theorem eoSmtVarEnvTermMem_concat_rec_of_env
    {left right : Term} {leftVars rightVars : List SmtVarKey}
    {z : Term}
    (hLeft : EoSmtVarEnv left leftVars)
    (hRight : EoSmtVarEnv right rightVars)
    (hMem : EoSmtVarEnvTermMem z (__eo_list_concat_rec left right)) :
    EoSmtVarEnvTermMem z left ∨ EoSmtVarEnvTermMem z right := by
  induction hLeft with
  | nil =>
      right
      have hRightNe := eoSmtVarEnv_ne_stuck hRight
      simpa [__eo_list_concat_rec, hRightNe] using hMem
  | cons hTail ih =>
      rename_i s T tail tailVars
      have hTailConcat :
          EoSmtVarEnv (__eo_list_concat_rec tail right)
            (tailVars ++ rightVars) :=
        EoSmtVarEnv.concat_rec hTail hRight
      have hTailConcatNe := eoSmtVarEnv_ne_stuck hTailConcat
      have hRightNe := eoSmtVarEnv_ne_stuck hRight
      simp [__eo_list_concat_rec, __eo_mk_apply] at hMem
      rcases hMem with hHead | hTailMem
      · left
        exact Or.inl hHead
      · rcases ih hTailMem with hLeftMem | hRightMem
        · left
          exact Or.inr hLeftMem
        · right
          exact hRightMem

private theorem eoSmtVarEnvTermMem_concat_of_env
    {left right : Term} {leftVars rightVars : List SmtVarKey}
    {z : Term}
    (hLeft : EoSmtVarEnv left leftVars)
    (hRight : EoSmtVarEnv right rightVars)
    (hMem :
      EoSmtVarEnvTermMem z
        (__eo_list_concat Term.__eo_List_cons left right)) :
    EoSmtVarEnvTermMem z left ∨ EoSmtVarEnvTermMem z right := by
  have hRec :
      EoSmtVarEnvTermMem z (__eo_list_concat_rec left right) := by
    simpa [__eo_list_concat, hLeft.is_list, hRight.is_list,
      __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] using hMem
  exact eoSmtVarEnvTermMem_concat_rec_of_env hLeft hRight hRec

private theorem eoSmtVarEnv_find_concat_right_of_not_left
    {left right : Term} {leftVars rightVars : List SmtVarKey}
    (hLeft : EoSmtVarEnv left leftVars)
    (hRight : EoSmtVarEnv right rightVars)
    (s : native_String) (T : Term)
    (hNotLeft : (s, __eo_to_smt_type T) ∉ leftVars)
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons
            (__eo_list_concat Term.__eo_List_cons left right)
            (Term.Var (Term.String s) T)) =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons right
          (Term.Var (Term.String s) T)) =
      Term.Boolean false := by
  have hConcatEnv :
      EoSmtVarEnv (__eo_list_concat Term.__eo_List_cons left right)
        (leftVars ++ rightVars) :=
    EoSmtVarEnv.concat hLeft hRight
  have hMemConcat :
      EoSmtVarEnvTermMem (Term.Var (Term.String s) T)
        (__eo_list_concat Term.__eo_List_cons left right) :=
    hConcatEnv.termMem_of_find_false
      (termVarString_ne_stuck s T) hFind
  rcases eoSmtVarEnvTermMem_concat_of_env hLeft hRight hMemConcat with
    hMemLeft | hMemRight
  · have hKeyLeft :
        (s, __eo_to_smt_type T) ∈ leftVars :=
      eoSmtVarEnv_key_mem_of_termMem hLeft hMemLeft
    exact False.elim (hNotLeft hKeyLeft)
  · exact eoSmtVarEnv_find_false_of_termMem hRight
      (termVarString_ne_stuck s T) hMemRight

private theorem smtTermFreeVars_eo_to_smt_exists_allowed_drop_binders
    {vs bvs : Term} {vsVars bvsVars : List SmtVarKey}
    {body : SmtTerm} {xs : Term} {s : native_String} {U : SmtType}
    (hVs : EoSmtVarEnv vs vsVars)
    (hBvs : EoSmtVarEnv bvs bvsVars)
    (hMem :
      (s, U) ∈ smtTermFreeVars (__eo_to_smt_exists vs body))
    (hAllowed :
      ∃ T,
        U = __eo_to_smt_type T ∧
          (__eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) T)) =
            Term.Boolean true ∨
            __eo_is_neg
              (__eo_list_find Term.__eo_List_cons
                (__eo_list_concat Term.__eo_List_cons vs bvs)
                (Term.Var (Term.String s) T)) =
            Term.Boolean false)) :
    ∃ T,
      U = __eo_to_smt_type T ∧
        (__eo_is_neg
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T)) =
          Term.Boolean true ∨
          __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) T)) =
          Term.Boolean false) := by
  have hNotBinder := (smtTermFreeVars_eo_to_smt_exists_body_and_not_env
    hVs hMem).2
  rcases hAllowed with ⟨T, hU, hAllowed⟩
  refine ⟨T, hU, ?_⟩
  rcases hAllowed with hNotXs | hBound
  · exact Or.inl hNotXs
  · have hNotLeft : (s, __eo_to_smt_type T) ∉ vsVars := by
      simpa [hU] using hNotBinder
    exact Or.inr
      (eoSmtVarEnv_find_concat_right_of_not_left hVs hBvs
        s T hNotLeft hBound)

private theorem smtTermFreeVars_eo_to_smt_allowed_of_contains_atomic_var_false
    (name T xs bvs : Term)
    (hNoFree :
      __contains_atomic_term_list_free_rec (Term.Var name T) xs bvs =
        Term.Boolean false) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt (Term.Var name T)) ->
        ∃ T',
          U = __eo_to_smt_type T' ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T')) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T')) =
              Term.Boolean false) := by
  intro s U hMem
  cases name
  case String s' =>
    change
      (s, U) ∈ smtTermFreeVars
        (SmtTerm.Var s' (__eo_to_smt_type T)) at hMem
    simp [smtTermFreeVars] at hMem
    rcases hMem with ⟨hS, hU⟩
    subst s
    subst U
    exact ⟨T, rfl, contains_atomic_var_false_cases
      (Term.String s') T xs bvs hNoFree⟩
  all_goals
    change (s, U) ∈ smtTermFreeVars SmtTerm.None at hMem
    simp [smtTermFreeVars] at hMem

private theorem smtTermFreeVars_eo_to_smt_allowed_of_closed_nil
    (F xs bvs : Term)
    (hClosed : SmtTermClosedIn [] (__eo_to_smt F)) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt F) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  have hNoMem : (s, U) ∈ ([] : List SmtVarKey) :=
    smtTermFreeVars_mem_of_closedIn hClosed hMem
  cases hNoMem

private theorem smtTermFreeVars_eo_to_smt_allowed_of_eo_closed_nil
    (F xs bvs : Term)
    (hClosed :
      __eo_is_closed_rec F Term.__eo_List_nil = Term.Boolean true) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt F) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  exact smtTermFreeVars_eo_to_smt_allowed_of_closed_nil F xs bvs
    (smtTermClosedIn_of_eo_is_closed_rec_perm
      (hEnv := EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil) hClosed)

private theorem smtTermFreeVars_allowed_of_append
    {x y : SmtTerm} {xs bvs : Term}
    (hXAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars x ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hYAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars y ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars x ++ smtTermFreeVars y ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  rcases List.mem_append.1 hMem with hMem | hMem
  · exact hXAllowed s U hMem
  · exact hYAllowed s U hMem

private theorem smtTermFreeVars_allowed_of_subset
    {x y : SmtTerm} {xs bvs : Term}
    (hSubset :
      ∀ key : SmtVarKey, key ∈ smtTermFreeVars x ->
        key ∈ smtTermFreeVars y)
    (hAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars y ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars x ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  exact hAllowed s U (hSubset (s, U) hMem)

private theorem smtTermFreeVars_allowed_re_unfold_pos_component_of_args_allowed
    (x y z xs bvs : Term)
    (hXAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt x) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hYAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt y) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈
          smtTermFreeVars
            (__eo_to_smt
              (Term.UOp3 UserOp3._at_re_unfold_pos_component x y z)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  rcases
      smtTermFreeVars_eo_to_smt_re_unfold_pos_component_raw_subset
        x y z hMem with
    hX | hY
  · exact hXAllowed s U hX
  · exact hYAllowed s U hY

private theorem smtTermFreeVars_allowed_witness_string_length
    (x y z xs bvs : Term) :
    ∀ s U,
      (s, U) ∈
          smtTermFreeVars
            (__eo_to_smt
              (Term.UOp3 UserOp3._at_witness_string_length x y z)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  exact False.elim
    (smtTermFreeVars_eo_to_smt_witness_string_length_empty
      x y z hMem)

private theorem smtTermFreeVars_allowed_of_append3
    {x y z : SmtTerm} {xs bvs : Term}
    (hXAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars x ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hYAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars y ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hZAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars z ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars x ++ smtTermFreeVars y ++
          smtTermFreeVars z ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  rcases List.mem_append.1 hMem with hMem | hMem
  · rcases List.mem_append.1 hMem with hMem | hMem
    · exact hXAllowed s U hMem
    · exact hYAllowed s U hMem
  · exact hZAllowed s U hMem

private theorem smtTermFreeVars_allowed_apply_not_of_arg_allowed
    (x xs bvs : Term)
    (hArgAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt x) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈
          smtTermFreeVars (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  change (s, U) ∈
    smtTermFreeVars (SmtTerm.not (__eo_to_smt x)) at hMem
  exact hArgAllowed s U hMem

private theorem smtTermFreeVars_allowed_apply_uop_of_arg_allowed
    (op : UserOp) (x xs bvs : Term)
    (hArgAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt x) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈
          smtTermFreeVars (__eo_to_smt (Term.Apply (Term.UOp op) x)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  exact smtTermFreeVars_allowed_of_subset
    (fun key hMem =>
      smtTermFreeVars_eo_to_smt_apply_uop_subset_arg op x hMem)
    hArgAllowed

private theorem smtTermFreeVars_allowed_qeq_of_args_allowed
    (x y xs bvs : Term)
    (hXAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt x) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hYAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt y) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt (qeq x y)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  change (s, U) ∈
    smtTermFreeVars (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) at hMem
  simp [smtTermFreeVars] at hMem
  rcases hMem with hMem | hMem
  · exact hXAllowed s U hMem
  · exact hYAllowed s U hMem

private theorem smtTermFreeVars_allowed_qor_of_args_allowed
    (x y xs bvs : Term)
    (hXAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt x) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hYAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt y) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈
          smtTermFreeVars
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  change (s, U) ∈
    smtTermFreeVars (__eo_to_smt x) ++
      smtTermFreeVars (__eo_to_smt y) at hMem
  exact smtTermFreeVars_allowed_of_append hXAllowed hYAllowed s U hMem

private theorem smtTermFreeVars_allowed_qand_of_args_allowed
    (x y xs bvs : Term)
    (hXAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt x) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hYAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt y) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈
          smtTermFreeVars
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  change (s, U) ∈
    smtTermFreeVars (__eo_to_smt x) ++
      smtTermFreeVars (__eo_to_smt y) at hMem
  exact smtTermFreeVars_allowed_of_append hXAllowed hYAllowed s U hMem

private theorem smtTermFreeVars_allowed_qimp_of_args_allowed
    (x y xs bvs : Term)
    (hXAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt x) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hYAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt y) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈
          smtTermFreeVars
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  change (s, U) ∈
    smtTermFreeVars (__eo_to_smt x) ++
      smtTermFreeVars (__eo_to_smt y) at hMem
  exact smtTermFreeVars_allowed_of_append hXAllowed hYAllowed s U hMem

private theorem smtTermFreeVars_allowed_qxor_of_args_allowed
    (x y xs bvs : Term)
    (hXAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt x) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hYAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt y) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈
          smtTermFreeVars
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  change (s, U) ∈
    smtTermFreeVars (__eo_to_smt x) ++
      smtTermFreeVars (__eo_to_smt y) at hMem
  exact smtTermFreeVars_allowed_of_append hXAllowed hYAllowed s U hMem

private theorem smtTermFreeVars_allowed_qite_of_args_allowed
    (c t e xs bvs : Term)
    (hCAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt c) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hTAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt t) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false))
    (hEAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt e) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈
          smtTermFreeVars
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  change (s, U) ∈
    smtTermFreeVars (__eo_to_smt c) ++
      smtTermFreeVars (__eo_to_smt t) ++
        smtTermFreeVars (__eo_to_smt e) at hMem
  exact
    smtTermFreeVars_allowed_of_append3
      hCAllowed hTAllowed hEAllowed s U hMem

private theorem smtTermFreeVars_eo_to_smt_allowed_uop1_bool
    (op : UserOp1) (x xs bvs : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.UOp1 op x)) = SmtType.Bool) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt (Term.UOp1 op x)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  cases op
  case seq_empty =>
    exact False.elim
      (smtTermFreeVars_eo_to_smt_seq_empty_empty
        (__eo_to_smt_type x) hMem)
  case set_empty =>
    exact False.elim
      (smtTermFreeVars_eo_to_smt_set_empty_empty
        (__eo_to_smt_type x) hMem)
  all_goals
    change (s, U) ∈ smtTermFreeVars SmtTerm.None at hMem
    simp [smtTermFreeVars] at hMem

private theorem contains_atomic_qterm_body_false_of_binder_env
    (Q y F xs bvs : Term) {yVars bvsVars : List SmtVarKey}
    (hYEnv : EoSmtVarEnv y yVars)
    (hBvsEnv : EoSmtVarEnv bvs bvsVars)
    (h :
      __contains_atomic_term_list_free_rec (qterm Q y F) xs bvs =
        Term.Boolean false) :
    __contains_atomic_term_list_free_rec F xs
        (__eo_list_concat Term.__eo_List_cons y bvs) =
      Term.Boolean false := by
  cases hYEnv with
  | nil =>
      have hBody :
          __contains_atomic_term_list_free_rec F xs bvs =
            Term.Boolean false := by
        cases xs <;> cases bvs <;>
          simp [qterm, __contains_atomic_term_list_free_rec] at h ⊢
        all_goals exact (eo_ite_true_eq_false _ _ h).2
      simpa [EoSmtVarEnv.concat_nil_left_eq hBvsEnv] using hBody
  | cons hTail =>
      rename_i s T tail tailVars
      simpa using
        contains_atomic_qterm_cons_body_false Q
          (Term.Var (Term.String s) T) tail F xs bvs h

private axiom smtTermFreeVars_eo_to_smt_allowed_of_contains_atomic_free_false
    (F xs bvs : Term)
    (hTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (hNoFree :
      __contains_atomic_term_list_free_rec F xs bvs =
        Term.Boolean false) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt F) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false)

private theorem smtTermFreeVars_eo_to_smt_allowed_of_contains_atomic_free_false_env
    (F xs bvs : Term) {bvsVars : List SmtVarKey}
    (_hBvsEnv : EoSmtVarEnv bvs bvsVars)
    (hTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (hNoFree :
      __contains_atomic_term_list_free_rec F xs bvs =
        Term.Boolean false) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt F) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  exact smtTermFreeVars_eo_to_smt_allowed_of_contains_atomic_free_false
    F xs bvs hTy hNoFree

private theorem smtTermFreeVars_eo_to_smt_allowed_of_qterm_body_allowed
    (Q y F xs bvs : Term) {yVars bvsVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hYEnv : EoSmtVarEnv y yVars)
    (hBvsEnv : EoSmtVarEnv bvs bvsVars)
    (hBodyAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt F) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons
                    (__eo_list_concat Term.__eo_List_cons y bvs)
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt (qterm Q y F)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  intro s U hMem
  have hBodyMem :
      (s, U) ∈ smtTermFreeVars (__eo_to_smt F) :=
    smtTermFreeVars_eo_to_smt_qterm_subset_body Q y F hQ hMem
  have hAllowedBody :
      ∃ T,
        U = __eo_to_smt_type T ∧
          (__eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) T)) =
            Term.Boolean true ∨
            __eo_is_neg
              (__eo_list_find Term.__eo_List_cons
                (__eo_list_concat Term.__eo_List_cons y bvs)
                (Term.Var (Term.String s) T)) =
            Term.Boolean false) :=
    hBodyAllowed s U hBodyMem
  rcases hQ with hQ | hQ
  · subst Q
    by_cases hy : y = Term.__eo_List_nil
    · subst y
      change (s, U) ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
    · change
        (s, U) ∈ smtTermFreeVars (__eo_to_smt (qforall y F)) at hMem
      rw [eo_to_smt_forall_eq y F hy] at hMem
      change
        (s, U) ∈ smtTermFreeVars
          (SmtTerm.not
            (__eo_to_smt_exists y (SmtTerm.not (__eo_to_smt F)))) at hMem
      exact
        smtTermFreeVars_eo_to_smt_exists_allowed_drop_binders
          (vs := y) (bvs := bvs) (body := SmtTerm.not (__eo_to_smt F))
          hYEnv hBvsEnv hMem hAllowedBody
  · subst Q
    by_cases hy : y = Term.__eo_List_nil
    · subst y
      change (s, U) ∈ smtTermFreeVars SmtTerm.None at hMem
      simp [smtTermFreeVars] at hMem
    · change
        (s, U) ∈ smtTermFreeVars (__eo_to_smt (qexists y F)) at hMem
      rw [eo_to_smt_exists_eq y F hy] at hMem
      exact
        smtTermFreeVars_eo_to_smt_exists_allowed_drop_binders
          (vs := y) (bvs := bvs) (body := __eo_to_smt F)
          hYEnv hBvsEnv hMem hAllowedBody

private theorem smtTermFreeVars_eo_to_smt_allowed_of_contains_atomic_qterm_false
    (Q y F xs bvs : Term) {yVars bvsVars : List SmtVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hYEnv : EoSmtVarEnv y yVars)
    (hBvsEnv : EoSmtVarEnv bvs bvsVars)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q y F)) = SmtType.Bool)
    (hNoFree :
      __contains_atomic_term_list_free_rec (qterm Q y F) xs bvs =
        Term.Boolean false) :
    ∀ s U,
      (s, U) ∈ smtTermFreeVars (__eo_to_smt (qterm Q y F)) ->
        ∃ T,
          U = __eo_to_smt_type T ∧
            (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true ∨
              __eo_is_neg
              (__eo_list_find Term.__eo_List_cons bvs
                (Term.Var (Term.String s) T)) =
              Term.Boolean false) := by
  have hBodyTy :
      __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
    smtx_typeof_qterm_body_bool_of_top_bool Q y F hQ hTy
  have hBodyNoFree :
      __contains_atomic_term_list_free_rec F xs
          (__eo_list_concat Term.__eo_List_cons y bvs) =
        Term.Boolean false :=
    contains_atomic_qterm_body_false_of_binder_env Q y F xs bvs
      hYEnv hBvsEnv hNoFree
  exact
    smtTermFreeVars_eo_to_smt_allowed_of_qterm_body_allowed
      Q y F xs bvs hQ hYEnv hBvsEnv
      (smtTermFreeVars_eo_to_smt_allowed_of_contains_atomic_free_false_env
        F xs (__eo_list_concat Term.__eo_List_cons y bvs)
        (EoSmtVarEnv.concat hYEnv hBvsEnv)
        hBodyTy hBodyNoFree)

private theorem smtx_model_eval_eq_of_freeVars_allowed
    (F xs bvs : Term) (M N : SmtModel)
    (hAgree : model_agrees_for_free_check xs bvs M N)
    (hAllowed :
      ∀ s U,
        (s, U) ∈ smtTermFreeVars (__eo_to_smt F) ->
          ∃ T,
            U = __eo_to_smt_type T ∧
              (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true ∨
                __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons bvs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false)) :
    __smtx_model_eval M (__eo_to_smt F) =
      __smtx_model_eval N (__eo_to_smt F) := by
  have hEnvAgree :
      model_agrees_on_env (smtTermFreeVars (__eo_to_smt F)) M N := by
    refine ⟨hAgree.1, ?_⟩
    intro s U hMem
    rcases hAllowed s U hMem with ⟨T, hU, hAllowed⟩
    subst U
    exact hAgree.2 s T hAllowed
  exact smt_model_eval_eq_of_closedIn (__eo_to_smt F)
    (smtTermFreeVars (__eo_to_smt F)) M N
    (smtTermClosedIn_freeVars (__eo_to_smt F)) hEnvAgree

private theorem smtx_model_eval_eq_of_eo_closed_env
    (F xs env : Term) {vars : List SmtVarKey} (M N : SmtModel)
    (hEnv : EoSmtVarEnv env vars)
    (hClosed :
      __eo_is_closed_rec F env = Term.Boolean true)
    (hAgree : model_agrees_for_free_check xs env M N) :
    __smtx_model_eval M (__eo_to_smt F) =
      __smtx_model_eval N (__eo_to_smt F) := by
  exact smtx_model_eval_eq_of_freeVars_allowed F xs env M N hAgree
    (smtTermFreeVars_allowed_of_eo_closed_env F xs env hEnv hClosed)

private theorem smtx_model_eval_eq_of_contains_atomic_free_false
    (F xs bvs : Term) {bvsVars : List SmtVarKey} (M N : SmtModel)
    (hBvsEnv : EoSmtVarEnv bvs bvsVars)
    (hTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (hAgree : model_agrees_for_free_check xs bvs M N)
    (hNoFree :
      __contains_atomic_term_list_free_rec F xs bvs =
        Term.Boolean false) :
    __smtx_model_eval M (__eo_to_smt F) =
      __smtx_model_eval N (__eo_to_smt F) := by
  exact smtx_model_eval_eq_of_freeVars_allowed F xs bvs M N hAgree
    (smtTermFreeVars_eo_to_smt_allowed_of_contains_atomic_free_false_env
      F xs bvs hBvsEnv hTy hNoFree)

private theorem smtx_model_eval_quant_unused_formula
    (M : SmtModel) (hM : model_total_typed M)
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M (__eo_to_smt G) := by
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool :=
    quantUnusedFormula_lhs_bool_of_quant Q x F G hQ hBool
  have hBodyTy :
      __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
    quantUnusedFormula_body_bool_of_quant Q x F G hQ hBool
  have hx : x ≠ Term.__eo_List_nil :=
    qterm_binder_non_nil_of_bool Q x F hQ hLhsTy
  rcases quant_unused_free_body_env_shape_of_no_free
      Q x F G hQ hNoFree hBool with
    hFallback | hQuant
  · rcases hFallback with
      ⟨xVars, setVars, hXEnv, hSetEnv, hG, _hGet, hNoFreeF⟩
    subst G
    have hBody :
        ∀ M' N',
          model_agrees_for_free_check
              (__eo_list_setof Term.__eo_List_cons x)
              Term.__eo_List_nil M' N' ->
            __smtx_model_eval M' (__eo_to_smt F) =
              __smtx_model_eval N' (__eo_to_smt F) := by
      intro M' N' hAgree
      exact smtx_model_eval_eq_of_contains_atomic_free_false F
        (__eo_list_setof Term.__eo_List_cons x) Term.__eo_List_nil
        M' N' EoSmtVarEnv.nil hBodyTy hAgree hNoFreeF
    exact smtx_eval_qterm_unused_of_rel
      (__eo_list_setof Term.__eo_List_cons x) Term.__eo_List_nil
      M hM Q x F hQ hXEnv hLhsTy hBodyTy hBody
      (by
        intro M' s T v hMem
        have hWF :
            __smtx_type_wf (__eo_to_smt_type T) = true :=
          smtx_type_wf_of_qterm_binder_mem_bool Q x F hQ hXEnv hx
            hLhsTy hMem
        have hWatchMem :
            EoSmtVarEnvTermMem (Term.Var (Term.String s) T)
              (__eo_list_setof Term.__eo_List_cons x) :=
          eoSmtVarEnvTermMem_setof_of_mem hXEnv hMem
        exact model_agrees_for_free_check_push_of_watch_mem_nil
          (__eo_list_setof Term.__eo_List_cons x) hSetEnv
          M' s T v hWF hWatchMem)
  · rcases hQuant with
      ⟨y, xVars, setVars, yVars, diffVars, hXEnv, hSetEnv, hYEnv,
        hDiffEnv, hPerm, hG, _hIncl, _hGet, hNoFreeF⟩
    subst G
    have hRhsTy :
        __smtx_typeof (__eo_to_smt (qterm Q y F)) = SmtType.Bool :=
      quantUnusedFormula_rhs_bool_of_quant Q x F (qterm Q y F) hQ hBool
    have hy : y ≠ Term.__eo_List_nil :=
      qterm_binder_non_nil_of_bool Q y F hQ hRhsTy
    have hBody :
        ∀ M' N',
          model_agrees_for_free_check
              (__eo_list_diff Term.__eo_List_cons
                (__eo_list_setof Term.__eo_List_cons x) y)
              (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil)
              M' N' ->
            __smtx_model_eval M' (__eo_to_smt F) =
              __smtx_model_eval N' (__eo_to_smt F) := by
      intro M' N' hAgree
      exact smtx_model_eval_eq_of_contains_atomic_free_false F
        (__eo_list_diff Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y)
        (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil)
        M' N' (EoSmtVarEnv.concat hYEnv EoSmtVarEnv.nil)
        hBodyTy hAgree hNoFreeF
    exact smtx_eval_qterm_setof_perm_drop_exact_diff_of_rel
      M hM Q x y F hQ hXEnv hSetEnv hYEnv hDiffEnv hPerm
      hx hy hLhsTy hBody

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
