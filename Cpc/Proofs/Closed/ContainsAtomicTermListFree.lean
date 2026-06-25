import Cpc.Proofs.Closed.IsClosedRec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

abbrev EoVarKey : Type := native_String × Term

def EoVarKey.toSmt (key : EoVarKey) : SmtVarKey :=
  (key.1, __eo_to_smt_type key.2)

/--
An EO variable environment that remembers the original EO type syntax.

`EoSmtVarEnv` is the right relation for SMT closedness, but it stores only the
translated SMT type.  The free-variable checker searches for exact EO variables,
so this relation keeps the EO type term around for the membership facts.
-/
inductive EoVarEnv : Term -> List EoVarKey -> Prop where
  | nil :
      EoVarEnv Term.__eo_List_nil []
  | cons {s : native_String} {T env : Term} {vars : List EoVarKey} :
      EoVarEnv env vars ->
        EoVarEnv
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) env)
          ((s, T) :: vars)

namespace EoVarEnv

theorem to_smt :
    ∀ {env : Term} {vars : List EoVarKey},
      EoVarEnv env vars ->
        EoSmtVarEnv env (vars.map EoVarKey.toSmt)
  | _, _, nil =>
      by
        exact EoSmtVarEnv.nil
  | _, _, cons hTail =>
      by
        simpa [EoVarKey.toSmt] using EoSmtVarEnv.cons (to_smt hTail)

theorem of_smt :
    ∀ {env : Term} {vars : List SmtVarKey},
      EoSmtVarEnv env vars ->
        ∃ eoVars,
          EoVarEnv env eoVars ∧ vars = eoVars.map EoVarKey.toSmt
  | _, _, EoSmtVarEnv.nil =>
      by
        exact ⟨[], EoVarEnv.nil, rfl⟩
  | _, _, EoSmtVarEnv.cons hTail =>
      by
        rename_i s T env vars
        rcases of_smt hTail with ⟨eoVars, hEo, hVars⟩
        exact
          ⟨(s, T) :: eoVars,
            EoVarEnv.cons (s := s) (T := T) hEo,
            by simp [EoVarKey.toSmt, hVars]⟩

theorem is_list
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  __eo_is_list Term.__eo_List_cons env = Term.Boolean true :=
by
  simpa using hEnv.to_smt.is_list

theorem cons_mk_apply
    {s : native_String} {T env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  EoVarEnv
    (__eo_mk_apply
      (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
      env)
    ((s, T) :: vars) :=
by
  cases hEnv with
  | nil =>
      simpa [__eo_mk_apply] using
        EoVarEnv.cons (s := s) (T := T) EoVarEnv.nil
  | cons hTail =>
      simpa [__eo_mk_apply] using
        EoVarEnv.cons (s := s) (T := T)
          (EoVarEnv.cons hTail)

theorem ne_stuck
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  env ≠ Term.Stuck :=
by
  cases hEnv <;> intro h <;> cases h

theorem vars_eq_of_same_env
    {env : Term} {vars vars' : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    (hEnv' : EoVarEnv env vars') :
  vars = vars' :=
by
  induction hEnv generalizing vars' with
  | nil =>
      cases hEnv'
      rfl
  | cons hTail ih =>
      cases hEnv' with
      | cons hTail' =>
          simp [ih hTail']

private theorem eo_prepend_if_true_eq
    {f x res : Term}
    (hF : f ≠ Term.Stuck)
    (hX : x ≠ Term.Stuck)
    (hRes : res ≠ Term.Stuck) :
  __eo_prepend_if (Term.Boolean true) f x res =
    Term.Apply (Term.Apply f x) res :=
by
  cases f <;> cases x <;> cases res <;>
    simp [__eo_prepend_if] at hF hX hRes ⊢

private theorem eo_prepend_if_false_eq
    {f x res : Term}
    (hF : f ≠ Term.Stuck)
    (hX : x ≠ Term.Stuck)
    (hRes : res ≠ Term.Stuck) :
  __eo_prepend_if (Term.Boolean false) f x res = res :=
by
  cases f <;> cases x <;> cases res <;>
    simp [__eo_prepend_if] at hF hX hRes ⊢

private theorem eo_eq_true_of_eq
    {x y : Term}
    (hEq : x = y)
    (hX : x ≠ Term.Stuck) :
  __eo_eq x y = Term.Boolean true :=
by
  subst y
  cases x <;> simp [__eo_eq, native_teq] at hX ⊢

private theorem eo_eq_false_of_ne
    {x y : Term}
    (hX : x ≠ Term.Stuck)
    (hY : y ≠ Term.Stuck)
    (hNe : x ≠ y) :
  __eo_eq x y = Term.Boolean false :=
by
  have hNeSymm : y ≠ x := by
    intro h
    exact hNe h.symm
  cases x <;> cases y <;>
    simp [__eo_eq, native_teq, hNe, hNeSymm] at hX hY ⊢
  all_goals
    exact False.elim (hNe rfl)

theorem erase_rec_var :
    ∀ {env : Term} {vars : List EoVarKey}
      (s : native_String) (T : Term),
      EoVarEnv env vars ->
        ∃ vars',
          EoVarEnv
            (__eo_list_erase_rec env (Term.Var (Term.String s) T))
            vars'
  | _, _, _, _, nil =>
      by
        exact ⟨[], by simpa [__eo_list_erase_rec] using EoVarEnv.nil⟩
  | _, _, s, T, cons (s := s') (T := T') (env := envTail) hTail =>
      by
        by_cases hEq :
            Term.Var (Term.String s') T' =
              Term.Var (Term.String s) T
        · exact
            ⟨_, by
              simpa [__eo_list_erase_rec, __eo_eq, native_teq, hEq,
                __eo_ite, native_ite] using hTail⟩
        · have hEqSymm :
              Term.Var (Term.String s) T ≠
                Term.Var (Term.String s') T' := by
            intro h
            exact hEq h.symm
          rcases erase_rec_var s T hTail with ⟨tailVars, hTailErase⟩
          exact
            ⟨(s', T') :: tailVars,
              by
                simpa [__eo_list_erase_rec, __eo_eq, native_teq, hEq,
                  hEqSymm, __eo_ite, native_ite] using
                  cons_mk_apply (s := s') (T := T') hTailErase⟩

theorem erase_all_rec_var :
    ∀ {env : Term} {vars : List EoVarKey}
      (s : native_String) (T : Term),
      EoVarEnv env vars ->
        ∃ vars',
          EoVarEnv
            (__eo_list_erase_all_rec env (Term.Var (Term.String s) T))
            vars'
  | _, _, _, _, nil =>
      by
        exact
          ⟨[], by simpa [__eo_list_erase_all_rec] using EoVarEnv.nil⟩
  | _, _, s, T, cons (s := s') (T := T') (env := envTail) hTail =>
      by
        by_cases hEq :
            Term.Var (Term.String s) T =
              Term.Var (Term.String s') T'
        · cases hEq
          rcases erase_all_rec_var s T hTail with
            ⟨tailVars, hTailErase⟩
          have hTailEraseNe := hTailErase.ne_stuck
          have hPrep :
              __eo_prepend_if (Term.Boolean false) Term.__eo_List_cons
                  (Term.Var (Term.String s) T)
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String s) T)) =
                __eo_list_erase_all_rec envTail
                  (Term.Var (Term.String s) T) :=
            eo_prepend_if_false_eq
              (by intro h; cases h) (by intro h; cases h) hTailEraseNe
          exact
            ⟨tailVars,
              by
                simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
                  __eo_not, native_not, __eo_prepend_if, hPrep] using
                  hTailErase⟩
        · have hEqSymm :
              Term.Var (Term.String s') T' ≠
                Term.Var (Term.String s) T := by
            intro h
            exact hEq h.symm
          rcases erase_all_rec_var s T hTail with
            ⟨tailVars, hTailErase⟩
          have hTailEraseNe := hTailErase.ne_stuck
          have hPrep :
              __eo_prepend_if (Term.Boolean true) Term.__eo_List_cons
                  (Term.Var (Term.String s') T')
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String s) T)) =
                Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s') T'))
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String s) T)) :=
            eo_prepend_if_true_eq
              (by intro h; cases h) (by intro h; cases h) hTailEraseNe
          exact
            ⟨(s', T') :: tailVars,
              by
                simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
                  hEq, hEqSymm, __eo_not, native_not, __eo_prepend_if,
                  hPrep] using
                  EoVarEnv.cons (s := s') (T := T') hTailErase⟩

theorem erase_all_rec_var_mem_of_mem_ne :
    ∀ {env : Term} {vars : List EoVarKey}
      {sErase : native_String} {TErase : Term}
      {s : native_String} {T : Term},
      EoVarEnv env vars ->
        (s, T) ∈ vars ->
          (s, T) ≠ (sErase, TErase) ->
            ∃ vars',
              EoVarEnv
                (__eo_list_erase_all_rec env
                  (Term.Var (Term.String sErase) TErase))
                vars' ∧
              (s, T) ∈ vars'
  | _, _, _, _, _, _, nil, hMem, _ =>
      by
        cases hMem
  | _, _, sErase, TErase, s, T,
      cons (s := sHead) (T := THead) (env := envTail) hTail,
      hMem, hNe =>
      by
        by_cases hEq :
            Term.Var (Term.String sErase) TErase =
              Term.Var (Term.String sHead) THead
        · cases hEq
          cases hMem with
          | head =>
              exfalso
              exact hNe rfl
          | tail _ hTailMem =>
              rcases
                erase_all_rec_var_mem_of_mem_ne hTail hTailMem hNe with
                ⟨tailVars, hTailErase, hTailMemOut⟩
              have hTailEraseNe := hTailErase.ne_stuck
              have hPrep :
                  __eo_prepend_if (Term.Boolean false) Term.__eo_List_cons
                      (Term.Var (Term.String sErase) TErase)
                      (__eo_list_erase_all_rec envTail
                        (Term.Var (Term.String sErase) TErase)) =
                    __eo_list_erase_all_rec envTail
                      (Term.Var (Term.String sErase) TErase) :=
                eo_prepend_if_false_eq
                  (by intro h; cases h) (by intro h; cases h) hTailEraseNe
              exact
                ⟨tailVars,
                  by
                    simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
                      __eo_not, native_not, __eo_prepend_if, hPrep] using
                      hTailErase,
                  hTailMemOut⟩
        · have hEqSymm :
              Term.Var (Term.String sHead) THead ≠
                Term.Var (Term.String sErase) TErase := by
            intro h
            exact hEq h.symm
          rcases erase_all_rec_var sErase TErase hTail with
            ⟨tailVars, hTailErase⟩
          have hTailEraseNe := hTailErase.ne_stuck
          have hPrep :
              __eo_prepend_if (Term.Boolean true) Term.__eo_List_cons
                  (Term.Var (Term.String sHead) THead)
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String sErase) TErase)) =
                Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String sHead) THead))
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String sErase) TErase)) :=
            eo_prepend_if_true_eq
              (by intro h; cases h) (by intro h; cases h) hTailEraseNe
          cases hMem with
          | head =>
              exact
                ⟨(s, T) :: tailVars,
                  by
                    simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
                      hEq, hEqSymm, __eo_not, native_not, __eo_prepend_if,
                      hPrep] using
                      EoVarEnv.cons (s := s) (T := T) hTailErase,
                  List.Mem.head _⟩
          | tail _ hTailMem =>
              by_cases hKey :
                  (s, T) = (sErase, TErase)
              · exact False.elim (hNe hKey)
              · rcases
                  erase_all_rec_var_mem_of_mem_ne hTail hTailMem hKey with
                ⟨memVars, hMemErase, hMemOut⟩
                have hVarsEq :
                    tailVars = memVars :=
                  EoVarEnv.vars_eq_of_same_env hTailErase hMemErase
                subst tailVars
                exact
                  ⟨(sHead, THead) :: memVars,
                    by
                      simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
                        hEq, hEqSymm, __eo_not, native_not, __eo_prepend_if,
                        hPrep] using
                        EoVarEnv.cons (s := sHead) (T := THead) hMemErase,
                    List.Mem.tail _ hMemOut⟩

theorem setof_rec :
    ∀ {env : Term} {vars : List EoVarKey},
      EoVarEnv env vars ->
        ∃ vars',
          EoVarEnv (__eo_list_setof_rec env) vars'
  | _, _, nil =>
      by
        exact ⟨[], by simpa [__eo_list_setof_rec] using EoVarEnv.nil⟩
  | _, _, cons (s := s) (T := T) hTail =>
      by
        rcases setof_rec hTail with ⟨setVars, hSet⟩
        rcases
          erase_all_rec_var s T hSet with
          ⟨eraseVars, hErase⟩
        exact
          ⟨(s, T) :: eraseVars,
            by
              simpa [__eo_list_setof_rec] using
                cons_mk_apply (s := s) (T := T) hErase⟩

theorem setof_rec_mem_of_mem :
    ∀ {env : Term} {vars : List EoVarKey}
      {s : native_String} {T : Term},
      EoVarEnv env vars ->
        (s, T) ∈ vars ->
          ∃ vars',
            EoVarEnv (__eo_list_setof_rec env) vars' ∧
            (s, T) ∈ vars'
  | _, _, _, _, nil, hMem =>
      by
        cases hMem
  | _, _, s, T, cons (s := sHead) (T := THead) hTail, hMem =>
      by
        rcases setof_rec hTail with ⟨setVars, hSet⟩
        rcases
          erase_all_rec_var sHead THead hSet with
          ⟨eraseVars, hErase⟩
        cases hMem with
        | head =>
            exact
              ⟨(s, T) :: eraseVars,
                by
                  simpa [__eo_list_setof_rec] using
                    cons_mk_apply (s := s) (T := T) hErase,
                List.Mem.head _⟩
        | tail _ hTailMem =>
            by_cases hKey :
                (s, T) = (sHead, THead)
            · cases hKey
              exact
                ⟨(s, T) :: eraseVars,
                  by
                    simpa [__eo_list_setof_rec] using
                      cons_mk_apply (s := s) (T := T) hErase,
                  List.Mem.head _⟩
            · rcases setof_rec_mem_of_mem hTail hTailMem with
                ⟨memSetVars, hMemSet, hMemSetVars⟩
              have hSetEq :
                  setVars = memSetVars :=
                EoVarEnv.vars_eq_of_same_env hSet hMemSet
              subst setVars
              rcases
                erase_all_rec_var_mem_of_mem_ne hMemSet hMemSetVars
                  (by
                    intro hEq
                    exact hKey hEq) with
                ⟨memEraseVars, hMemErase, hMemEraseVars⟩
              have hEraseEq :
                  eraseVars = memEraseVars :=
                EoVarEnv.vars_eq_of_same_env hErase hMemErase
              subst eraseVars
              exact
                ⟨(sHead, THead) :: memEraseVars,
                  by
                    simpa [__eo_list_setof_rec] using
                      cons_mk_apply (s := sHead) (T := THead) hMemErase,
                  List.Mem.tail _ hMemEraseVars⟩

theorem setof
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  ∃ vars',
    EoVarEnv (__eo_list_setof Term.__eo_List_cons env) vars' :=
by
  have hList := hEnv.is_list
  rcases setof_rec hEnv with ⟨setVars, hSet⟩
  exact
    ⟨setVars,
      by
        simpa [__eo_list_setof, __eo_requires, hList, native_ite,
          native_teq] using hSet⟩

theorem setof_mem_of_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    {s : native_String} {T : Term}
    (hMem : (s, T) ∈ vars) :
  ∃ vars',
    EoVarEnv (__eo_list_setof Term.__eo_List_cons env) vars' ∧
    (s, T) ∈ vars' :=
by
  have hList := hEnv.is_list
  rcases setof_rec_mem_of_mem hEnv hMem with
    ⟨setVars, hSet, hSetMem⟩
  exact
    ⟨setVars,
      by
        simpa [__eo_list_setof, __eo_requires, hList, native_ite,
          native_teq] using hSet,
      hSetMem⟩

theorem diff_rec :
    ∀ {a b : Term} {aVars bVars : List EoVarKey},
      EoVarEnv a aVars ->
        EoVarEnv b bVars ->
          ∃ vars',
            EoVarEnv (__eo_list_diff_rec a b) vars'
  | _, _, _, _, nil, hB =>
      by
        cases hB <;>
          exact ⟨[], by simpa [__eo_list_diff_rec] using EoVarEnv.nil⟩
  | _, b, _, _, cons (s := s) (T := T) (env := aTail) hTail, hB =>
      by
        let erased := __eo_list_erase_rec b (Term.Var (Term.String s) T)
        rcases
          erase_rec_var s T hB with
          ⟨erasedVars, hErased⟩
        have hErased' : EoVarEnv erased erasedVars := by
          simpa [erased] using hErased
        rcases diff_rec hTail hErased' with ⟨diffVars, hDiff⟩
        have hBNe := hB.ne_stuck
        have hErasedNe := hErased'.ne_stuck
        have hDiffNe := hDiff.ne_stuck
        by_cases hEq : erased = b
        · have hEqSymm : b = erased := hEq.symm
          exact
            ⟨(s, T) :: diffVars,
              by
                have hCond : __eo_eq erased b = Term.Boolean true :=
                  eo_eq_true_of_eq hEq hErasedNe
                have hPrep :
                    __eo_prepend_if (Term.Boolean true) Term.__eo_List_cons
                        (Term.Var (Term.String s) T)
                        (__eo_list_diff_rec aTail erased) =
                      Term.Apply
                        (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T))
                        (__eo_list_diff_rec aTail erased) :=
                  eo_prepend_if_true_eq
                    (by intro h; cases h) (by intro h; cases h) hDiffNe
                have hUnfold :
                    __eo_list_diff_rec
                        (Term.Apply
                          (Term.Apply Term.__eo_List_cons
                            (Term.Var (Term.String s) T))
                          aTail)
                        b =
                      __eo_prepend_if (__eo_eq erased b)
                        Term.__eo_List_cons
                        (Term.Var (Term.String s) T)
                        (__eo_list_diff_rec aTail erased) := by
                  cases hB <;> simp [__eo_list_diff_rec, erased]
                rw [hUnfold, hCond, hPrep]
                exact EoVarEnv.cons (s := s) (T := T) hDiff⟩
        · exact
            ⟨diffVars,
              by
                have hEqSymm : b ≠ erased := by
                  intro h
                  exact hEq h.symm
                have hCond : __eo_eq erased b = Term.Boolean false :=
                  eo_eq_false_of_ne hErasedNe hBNe hEq
                have hPrep :
                    __eo_prepend_if (Term.Boolean false) Term.__eo_List_cons
                        (Term.Var (Term.String s) T)
                        (__eo_list_diff_rec aTail erased) =
                      __eo_list_diff_rec aTail erased :=
                  eo_prepend_if_false_eq
                    (by intro h; cases h) (by intro h; cases h) hDiffNe
                have hUnfold :
                    __eo_list_diff_rec
                        (Term.Apply
                          (Term.Apply Term.__eo_List_cons
                            (Term.Var (Term.String s) T))
                          aTail)
                        b =
                      __eo_prepend_if (__eo_eq erased b)
                        Term.__eo_List_cons
                        (Term.Var (Term.String s) T)
                        (__eo_list_diff_rec aTail erased) := by
                  cases hB <;> simp [__eo_list_diff_rec, erased]
                rw [hUnfold, hCond, hPrep]
                exact hDiff⟩

theorem diff
    {a b : Term} {aVars bVars : List EoVarKey}
    (hA : EoVarEnv a aVars)
    (hB : EoVarEnv b bVars) :
  ∃ vars',
    EoVarEnv (__eo_list_diff Term.__eo_List_cons a b) vars' :=
by
  have hAList := hA.is_list
  have hBList := hB.is_list
  rcases diff_rec hA hB with ⟨diffVars, hDiff⟩
  exact
    ⟨diffVars,
      by
        simpa [__eo_list_diff, __eo_requires, hAList, hBList,
          native_ite, native_teq] using hDiff⟩

theorem concat_rec :
    ∀ {vs env : Term} {binderVars vars : List EoVarKey},
      EoVarEnv vs binderVars ->
        EoVarEnv env vars ->
          EoVarEnv
            (__eo_list_concat_rec vs env)
            (binderVars ++ vars)
  | _, _, _, _, nil, hEnv =>
      by
        cases hEnv with
        | nil =>
            simpa [__eo_list_concat_rec] using EoVarEnv.nil
        | cons hTail =>
            rename_i s' T' env' vars'
            simpa [__eo_list_concat_rec] using
              EoVarEnv.cons (s := s') (T := T') hTail
  | _, _, _, _, cons (s := s) (T := T) hTail, hEnv =>
      by
        cases hEnv with
        | nil =>
            have hTailConcat := concat_rec hTail EoVarEnv.nil
            simpa [__eo_list_concat_rec, List.cons_append]
              using cons_mk_apply (s := s) (T := T) hTailConcat
        | cons hEnvTail =>
            rename_i s' T' env' vars'
            have hTailConcat :=
              concat_rec hTail
                (EoVarEnv.cons (s := s') (T := T') hEnvTail)
            simpa [__eo_list_concat_rec, List.cons_append]
              using cons_mk_apply (s := s) (T := T) hTailConcat

theorem concat :
    ∀ {vs env : Term} {binderVars vars : List EoVarKey},
      EoVarEnv vs binderVars ->
        EoVarEnv env vars ->
          EoVarEnv
            (__eo_list_concat Term.__eo_List_cons vs env)
            (binderVars ++ vars)
  | _, _, _, _, hVs, hEnv =>
      by
        have hVsList := hVs.is_list
        have hEnvList := hEnv.is_list
        simpa [__eo_list_concat, __eo_requires, hVsList, hEnvList,
          native_ite, native_teq]
          using concat_rec hVs hEnv

theorem find_rec_neg_false_of_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  ∀ {s : native_String} {T : Term} {n : native_Int},
    (s, T) ∈ vars ->
      0 ≤ n ->
        __eo_is_neg
            (__eo_list_find_rec env (Term.Var (Term.String s) T)
              (Term.Numeral n)) =
          Term.Boolean false :=
by
  induction hEnv with
  | nil =>
      intro s T n hMem hNonneg
      cases hMem
  | cons hTail ih =>
      rename_i s' T' env' vars'
      intro s T n hMem hNonneg
      by_cases hVarEq :
          Term.Var (Term.String s') T' =
            Term.Var (Term.String s) T
      · have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq.symm]
        have hNotLt : native_zlt n 0 = false := by
          simp [native_zlt, Int.not_lt_of_ge hNonneg]
        simp [__eo_list_find_rec, hFindEq, __eo_ite, __eo_is_neg,
          native_ite, native_teq, hNotLt]
      · have hVarEqSymm :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s') T' := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hTailMem : (s, T) ∈ vars' := by
          cases hMem with
          | head =>
              exfalso
              exact hVarEq rfl
          | tail _ hTailMem =>
              exact hTailMem
        have hSuccNonneg : 0 ≤ native_zplus n 1 := by
          simpa [native_zplus] using
            Int.add_nonneg hNonneg (by decide : (0 : Int) ≤ 1)
        simpa [__eo_list_find_rec, hFindEq, __eo_ite, __eo_add,
          native_ite, native_teq]
          using ih hTailMem hSuccNonneg

theorem find_rec_neg_true_of_not_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  ∀ {s : native_String} {T : Term} {n : native_Int},
    (s, T) ∉ vars ->
      0 ≤ n ->
        __eo_is_neg
            (__eo_list_find_rec env (Term.Var (Term.String s) T)
              (Term.Numeral n)) =
          Term.Boolean true :=
by
  induction hEnv with
  | nil =>
      intro s T n hNotMem hNonneg
      simp [__eo_list_find_rec, __eo_is_neg, native_zlt]
  | cons hTail ih =>
      rename_i s' T' env' vars'
      intro s T n hNotMem hNonneg
      by_cases hVarEq :
          Term.Var (Term.String s') T' =
            Term.Var (Term.String s) T
      · exfalso
        injection hVarEq with hName hTy
        injection hName with hs
        cases hs
        cases hTy
        exact hNotMem (List.Mem.head _)
      · have hVarEqSymm :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s') T' := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hTailNotMem : (s, T) ∉ vars' := by
          intro hMem
          exact hNotMem (List.Mem.tail _ hMem)
        have hSuccNonneg : 0 ≤ native_zplus n 1 := by
          simpa [native_zplus] using
            Int.add_nonneg hNonneg (by decide : (0 : Int) ≤ 1)
        simpa [__eo_list_find_rec, hFindEq, __eo_ite, __eo_add,
          native_ite, native_teq]
          using ih hTailNotMem hSuccNonneg

theorem find_neg_false_of_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    {s : native_String} {T : Term}
    (hMem : (s, T) ∈ vars) :
  __eo_is_neg
      (__eo_list_find Term.__eo_List_cons env
        (Term.Var (Term.String s) T)) =
    Term.Boolean false :=
by
  have hList := hEnv.is_list
  simpa [__eo_list_find, __eo_requires, hList, native_ite, native_teq]
    using
      hEnv.find_rec_neg_false_of_mem hMem
        (show (0 : native_Int) ≤ (0 : native_Int) by
          exact Int.le_refl 0)

theorem find_neg_true_of_not_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    {s : native_String} {T : Term}
    (hNotMem : (s, T) ∉ vars) :
  __eo_is_neg
      (__eo_list_find Term.__eo_List_cons env
        (Term.Var (Term.String s) T)) =
    Term.Boolean true :=
by
  have hList := hEnv.is_list
  simpa [__eo_list_find, __eo_requires, hList, native_ite, native_teq]
    using
      hEnv.find_rec_neg_true_of_not_mem hNotMem
        (show (0 : native_Int) ≤ (0 : native_Int) by
          exact Int.le_refl 0)

end EoVarEnv

def EoVarEnvEquiv (xs ys : List EoVarKey) : Prop :=
  ∀ key, key ∈ xs ↔ key ∈ ys

theorem EoVarEnvEquiv.refl (xs : List EoVarKey) :
  EoVarEnvEquiv xs xs :=
by
  intro key
  rfl

theorem EoVarEnvEquiv.reverse (xs : List EoVarKey) :
  EoVarEnvEquiv xs xs.reverse :=
by
  intro key
  simp

theorem EoVarEnvEquiv.append
    {xs xs' ys ys' : List EoVarKey}
    (hxs : EoVarEnvEquiv xs xs')
    (hys : EoVarEnvEquiv ys ys') :
  EoVarEnvEquiv (xs ++ ys) (xs' ++ ys') :=
by
  intro key
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append.2 (Or.inl ((hxs key).1 h))
    · exact List.mem_append.2 (Or.inr ((hys key).1 h))
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append.2 (Or.inl ((hxs key).2 h))
    · exact List.mem_append.2 (Or.inr ((hys key).2 h))

def EoVarEnvPerm (env : Term) (vars : List EoVarKey) : Prop :=
  ∃ exactVars, EoVarEnv env exactVars ∧ EoVarEnvEquiv exactVars vars

theorem EoVarEnvPerm.of_exact
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  EoVarEnvPerm env vars :=
by
  exact ⟨vars, hEnv, EoVarEnvEquiv.refl vars⟩

theorem EoVarEnvPerm.mem_of_exact_env_mem
    {env : Term} {exactVars vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars)
    (hExact : EoVarEnv env exactVars)
    {key : EoVarKey}
    (hMem : key ∈ exactVars) :
  key ∈ vars :=
by
  rcases hEnv with ⟨envVars, hEnvVars, hEquiv⟩
  have hEq : exactVars = envVars :=
    EoVarEnv.vars_eq_of_same_env hExact hEnvVars
  subst exactVars
  exact (hEquiv key).1 hMem

theorem EoVarEnvPerm.ne_stuck
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars) :
  env ≠ Term.Stuck :=
by
  rcases hEnv with ⟨_, hExact, _⟩
  exact hExact.ne_stuck

theorem EoVarEnvPerm.mem_of_find_neg_false
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars)
    {s : native_String} {T : Term}
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons env
            (Term.Var (Term.String s) T)) =
        Term.Boolean false) :
  (s, T) ∈ vars :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  by_cases hMem : (s, T) ∈ exactVars
  · exact (hEquiv (s, T)).1 hMem
  · have hFindTrue := hExact.find_neg_true_of_not_mem hMem
    rw [hFindTrue] at hFind
    cases hFind

theorem EoVarEnvPerm.not_mem_of_find_neg_true
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars)
    {s : native_String} {T : Term}
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons env
            (Term.Var (Term.String s) T)) =
        Term.Boolean true) :
  (s, T) ∉ vars :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  intro hMem
  have hExactMem : (s, T) ∈ exactVars := (hEquiv (s, T)).2 hMem
  have hFindFalse := hExact.find_neg_false_of_mem hExactMem
  rw [hFind] at hFindFalse
  cases hFindFalse

theorem EoVarKey.mem_of_toSmt_mem_map_of_type_wf
    {vars : List EoVarKey} {s : native_String} {T : Term}
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hMem : (s, __eo_to_smt_type T) ∈ vars.map EoVarKey.toSmt) :
  (s, T) ∈ vars :=
by
  rcases List.mem_map.1 hMem with ⟨key, hKeyMem, hKeyEq⟩
  rcases key with ⟨s', T'⟩
  simp [EoVarKey.toSmt] at hKeyEq
  rcases hKeyEq with ⟨hName, hType⟩
  subst s'
  by_cases hReg : T = Term.UOp UserOp.RegLan
  · subst T
    have hT' :
        T' = Term.UOp UserOp.RegLan :=
      TranslationProofs.eo_to_smt_type_eq_reglan hType
    subst T'
    exact hKeyMem
  · have hValid : TranslationProofs.eo_type_valid T :=
      TranslationProofs.eo_type_valid_of_smt_wf T hWf
    have hValidRec : TranslationProofs.eo_type_valid_rec [] T := by
      cases T with
      | UOp op =>
          cases op
          case RegLan =>
            exact False.elim (hReg rfl)
          all_goals
            exact hValid
      | _ =>
          simpa [TranslationProofs.eo_type_valid] using hValid
    have hT : T = T' :=
      TranslationProofs.eo_to_smt_type_eq_of_valid
        (T := T) (U := T') hValidRec hType.symm
    subst T'
    exact hKeyMem

theorem EoVarEnvPerm.toSmt_not_mem_of_find_neg_true
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars)
    {s : native_String} {T : Term}
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons env
            (Term.Var (Term.String s) T)) =
        Term.Boolean true) :
  (s, __eo_to_smt_type T) ∉ vars.map EoVarKey.toSmt :=
by
  have hNotMem : (s, T) ∉ vars :=
    EoVarEnvPerm.not_mem_of_find_neg_true hEnv hFind
  intro hMem
  exact hNotMem
    (EoVarKey.mem_of_toSmt_mem_map_of_type_wf hWf hMem)

theorem smtx_type_wf_of_var_has_smt_translation
    {s : native_String} {T : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Var (Term.String s) T)) :
  __smtx_type_wf (__eo_to_smt_type T) = true :=
by
  have hGuardNN :
      __smtx_typeof_guard_wf
          (__eo_to_smt_type T) (__eo_to_smt_type T) ≠
        SmtType.None := by
    have hNN :
        __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) ≠
          SmtType.None := by
      simpa [eoHasSmtTranslation] using hTrans
    simpa [__smtx_typeof] using hNN
  exact
    smtx_typeof_guard_wf_wf_of_non_none
      (__eo_to_smt_type T) (__eo_to_smt_type T) hGuardNN

theorem EoVarEnvPerm.concat_rev
    {vs env : Term} {binderVars vars : List EoVarKey}
    (hVs : EoVarEnv vs binderVars)
    (hEnv : EoVarEnvPerm env vars) :
  EoVarEnvPerm
    (__eo_list_concat Term.__eo_List_cons vs env)
    (binderVars.reverse ++ vars) :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  refine ⟨binderVars ++ exactVars, EoVarEnv.concat hVs hExact, ?_⟩
  exact EoVarEnvEquiv.append
    (EoVarEnvEquiv.reverse binderVars)
    hEquiv

theorem eo_var_env_of_uop_list_branch_has_smt_translation
    {op : UserOp} {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars,
    EoVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  rcases
    eo_smt_var_env_of_uop_list_branch_has_smt_translation hTrans with
    ⟨smtVars, hSmtEnv⟩
  rcases EoVarEnv.of_smt hSmtEnv with
    ⟨eoVars, hEoEnv, _hVars⟩
  exact ⟨eoVars, hEoEnv⟩

theorem eo_var_env_of_list_branch_has_smt_translation
    {q v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars,
    EoVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  rcases
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst q
    exact eo_var_env_of_uop_list_branch_has_smt_translation hTrans
  · subst q
    exact eo_var_env_of_uop_list_branch_has_smt_translation hTrans

theorem eo_var_env_of_forall_has_smt_translation
    {xs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)) :
  ∃ vars, EoVarEnv xs vars :=
by
  by_cases hCons :
      ∃ v vs,
        xs = Term.Apply (Term.Apply Term.__eo_List_cons v) vs
  · rcases hCons with ⟨v, vs, rfl⟩
    exact eo_var_env_of_uop_list_branch_has_smt_translation hTrans
  · exact
      false_of_forall_non_list_has_smt_translation
        (by
          intro v vs hEq
          exact hCons ⟨v, vs, hEq⟩)
        hTrans

theorem eo_var_env_of_exists_has_smt_translation
    {xs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)) :
  ∃ vars, EoVarEnv xs vars :=
by
  by_cases hCons :
      ∃ v vs,
        xs = Term.Apply (Term.Apply Term.__eo_List_cons v) vs
  · rcases hCons with ⟨v, vs, rfl⟩
    exact eo_var_env_of_uop_list_branch_has_smt_translation hTrans
  · exact
      false_of_exists_non_list_has_smt_translation
        (by
          intro v vs hEq
          exact hCons ⟨v, vs, hEq⟩)
        hTrans

theorem eo_var_env_of_quant_has_smt_translation
    {Q xs body : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply Q xs) body)) :
  ∃ vars, EoVarEnv xs vars :=
by
  rcases hQ with hForall | hExists
  · subst Q
    exact eo_var_env_of_forall_has_smt_translation hTrans
  · subst Q
    exact eo_var_env_of_exists_has_smt_translation hTrans

/--
Models agree everywhere except possibly on the variables in `except` that are
not currently shadowed by `bound`.

This is the semantic relation matched to
`__contains_atomic_term_list_free_rec t except bound = false`: free variables in
`except` are the only variables on which the two models may differ, while
variables in `bound` are considered locally bound and therefore must agree after
the evaluator pushes matching witnesses on both sides.
-/
structure model_agrees_except_on_env
    (except bound : List SmtVarKey) (M N : SmtModel) : Prop where
  globals : model_agrees_on_globals M N
  vars_eq :
    ∀ s T, (s, T) ∈ bound ∨ (s, T) ∉ except ->
      native_model_var_lookup M s T = native_model_var_lookup N s T

theorem model_agrees_except_on_env_refl
    (except bound : List SmtVarKey) (M : SmtModel) :
  model_agrees_except_on_env except bound M M :=
by
  exact ⟨model_agrees_on_globals_refl M, by intro s T _; rfl⟩

theorem model_agrees_except_on_env_symm
    {except bound : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_env except bound M N) :
  model_agrees_except_on_env except bound N M :=
by
  refine ⟨?_, ?_⟩
  · exact ⟨by intro s T; exact (hAgree.globals.1 s T).symm,
      by intro fid T U; exact (hAgree.globals.2 fid T U).symm⟩
  · intro s T hKey
    exact (hAgree.vars_eq s T hKey).symm

theorem model_agrees_except_on_env_push_same
    {except bound : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType} {v : SmtValue}
    (hAgree : model_agrees_except_on_env except bound M N) :
  model_agrees_except_on_env except ((s, T) :: bound)
    (native_model_push M s T v) (native_model_push N s T v) :=
by
  refine ⟨model_agrees_on_globals_push₂ hAgree.globals, ?_⟩
  intro s' T' hKeyAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := T' } : SmtModelKey) =
        { isVar := true, name := s, ty := T }
  · cases hKey
    simp [native_model_var_lookup, native_model_push]
  · have hAllowedTail : (s', T') ∈ bound ∨ (s', T') ∉ except := by
      rcases hKeyAllowed with hBound | hNotExcept
      · cases hBound with
        | head =>
            exfalso
            exact hKey rfl
        | tail _ hTail =>
            exact Or.inl hTail
      · exact Or.inr hNotExcept
    simpa [native_model_var_lookup, native_model_push, hKey]
      using hAgree.vars_eq s' T' hAllowedTail

theorem model_agrees_except_on_env_shrink_bound
    {except bound bound' : List SmtVarKey} {M N : SmtModel}
    (hSub : ∀ key, key ∈ bound' -> key ∈ bound)
    (hAgree : model_agrees_except_on_env except bound M N) :
  model_agrees_except_on_env except bound' M N :=
by
  refine ⟨hAgree.globals, ?_⟩
  intro s T hAllowed
  apply hAgree.vars_eq
  rcases hAllowed with hBound' | hNotExcept
  · exact Or.inl (hSub (s, T) hBound')
  · exact Or.inr hNotExcept

theorem model_agrees_except_on_env_push_left_of_mem_except
    {except bound : List SmtVarKey} {M : SmtModel}
    {s : native_String} {T : SmtType} {v : SmtValue}
    (hMem : (s, T) ∈ except)
    (hNotBound : (s, T) ∉ bound) :
  model_agrees_except_on_env except bound
    (native_model_push M s T v) M :=
by
  refine ⟨model_agrees_on_globals_push M s T v, ?_⟩
  intro s' T' hAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := T' } : SmtModelKey) =
        { isVar := true, name := s, ty := T }
  · cases hKey
    exfalso
    rcases hAllowed with hBound | hNotExcept
    · exact hNotBound hBound
    · exact hNotExcept hMem
  · simp [native_model_var_lookup, native_model_push, hKey]

theorem model_agrees_except_on_env_push_left
    {except bound : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType} {v : SmtValue}
    (hAgree : model_agrees_except_on_env except bound N M)
    (hMem : (s, T) ∈ except)
    (hNotBound : (s, T) ∉ bound) :
  model_agrees_except_on_env except bound
    (native_model_push N s T v) M :=
by
  refine
    ⟨model_agrees_on_globals_trans
      (model_agrees_on_globals_push N s T v) hAgree.globals, ?_⟩
  intro s' T' hAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := T' } : SmtModelKey) =
        { isVar := true, name := s, ty := T }
  · cases hKey
    exfalso
    rcases hAllowed with hBound | hNotExcept
    · exact hNotBound hBound
    · exact hNotExcept hMem
  · simpa [native_model_var_lookup, native_model_push, hKey]
      using hAgree.vars_eq s' T' hAllowed

/--
Exact-EO-variable version of `model_agrees_except_on_env`.

The checker's free-variable test compares whole EO variables, including the EO
type syntax.  This relation preserves that exactness while still comparing SMT
model lookups at the translated type.
-/
structure model_agrees_except_on_eo_env
    (except bound : List EoVarKey) (M N : SmtModel) : Prop where
  globals : model_agrees_on_globals M N
  vars_eq :
    ∀ s T, (s, T) ∈ bound ∨ (s, T) ∉ except ->
      native_model_var_lookup M s (__eo_to_smt_type T) =
        native_model_var_lookup N s (__eo_to_smt_type T)

theorem model_agrees_except_on_eo_env_refl
    (except bound : List EoVarKey) (M : SmtModel) :
  model_agrees_except_on_eo_env except bound M M :=
by
  exact ⟨model_agrees_on_globals_refl M, by intro s T _; rfl⟩

theorem model_agrees_except_on_eo_env_symm
    {except bound : List EoVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_eo_env except bound M N) :
  model_agrees_except_on_eo_env except bound N M :=
by
  refine ⟨?_, ?_⟩
  · exact ⟨by intro s T; exact (hAgree.globals.1 s T).symm,
      by intro fid T U; exact (hAgree.globals.2 fid T U).symm⟩
  · intro s T hKey
    exact (hAgree.vars_eq s T hKey).symm

theorem model_agrees_except_on_eo_env_push_same
    {except bound : List EoVarKey} {M N : SmtModel}
    {s : native_String} {T : Term} {v : SmtValue}
    (hAgree : model_agrees_except_on_eo_env except bound M N) :
  model_agrees_except_on_eo_env except ((s, T) :: bound)
    (native_model_push M s (__eo_to_smt_type T) v)
    (native_model_push N s (__eo_to_smt_type T) v) :=
by
  refine ⟨model_agrees_on_globals_push₂ hAgree.globals, ?_⟩
  intro s' T' hKeyAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
          SmtModelKey) =
        { isVar := true, name := s, ty := __eo_to_smt_type T }
  · simp [native_model_var_lookup, native_model_push, hKey]
  · have hAllowedTail : (s', T') ∈ bound ∨ (s', T') ∉ except := by
      rcases hKeyAllowed with hBound | hNotExcept
      · cases hBound with
        | head =>
            exfalso
            exact hKey rfl
        | tail _ hTail =>
            exact Or.inl hTail
      · exact Or.inr hNotExcept
    simpa [native_model_var_lookup, native_model_push, hKey]
      using hAgree.vars_eq s' T' hAllowedTail

private theorem eo_ite_false_eq_false_cases
    {c e : Term}
    (h : __eo_ite c (Term.Boolean false) e = Term.Boolean false) :
  c = Term.Boolean true ∨ e = Term.Boolean false :=
by
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b
    · right
      simpa [__eo_ite, native_ite, native_teq] using h
    · left
      rfl

private theorem eo_ite_true_eq_false_cases
    {c e : Term}
    (h : __eo_ite c (Term.Boolean true) e = Term.Boolean false) :
  c = Term.Boolean false ∧ e = Term.Boolean false :=
by
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b
    · constructor
      · rfl
      · simpa [__eo_ite, native_ite, native_teq] using h
    · cases h

/--
The variable case of `__contains_atomic_term_list_free_rec`.

For a variable, returning `false` means exactly the checker's local condition:
either the variable is absent from the exception list, or it is present in the
current bound-variable stack.
-/
theorem contains_atomic_term_list_free_rec_var_false_cases
    {name T except bound : Term}
    (hNoFree :
      __contains_atomic_term_list_free_rec (Term.Var name T) except bound =
        Term.Boolean false) :
  __eo_is_neg
      (__eo_list_find Term.__eo_List_cons except (Term.Var name T)) =
      Term.Boolean true ∨
    __eo_is_neg
      (__eo_list_find Term.__eo_List_cons bound (Term.Var name T)) =
      Term.Boolean false :=
by
  cases except <;> cases bound <;>
    simp [__contains_atomic_term_list_free_rec] at hNoFree ⊢
  all_goals
    exact eo_ite_false_eq_false_cases hNoFree

theorem native_model_var_lookup_eq_of_contains_atomic_term_list_free_rec_var_false
    {s : native_String} {T except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N) :
  native_model_var_lookup M s (__eo_to_smt_type T) =
    native_model_var_lookup N s (__eo_to_smt_type T) :=
by
  rcases contains_atomic_term_list_free_rec_var_false_cases hNoFree with
    hNotExcept | hBoundVar
  · have hNotMem :
        (s, T) ∉ exceptVars :=
      EoVarEnvPerm.not_mem_of_find_neg_true hExcept hNotExcept
    exact hAgree.vars_eq s T (Or.inr hNotMem)
  · have hMem :
        (s, T) ∈ boundVars :=
      EoVarEnvPerm.mem_of_find_neg_false hBound hBoundVar
    exact hAgree.vars_eq s T (Or.inl hMem)

theorem smt_model_eval_var_eq_of_contains_atomic_term_list_free_rec_false
    {s : native_String} {T except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N) :
  __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
    __smtx_model_eval N (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def]
  exact
    native_model_var_lookup_eq_of_contains_atomic_term_list_free_rec_var_false
      hExcept hBound hNoFree hAgree

theorem native_model_var_lookup_eq_of_contains_atomic_term_list_free_rec_var_false_mapped
    {s : native_String} {T except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N) :
  native_model_var_lookup M s (__eo_to_smt_type T) =
    native_model_var_lookup N s (__eo_to_smt_type T) :=
by
  rcases contains_atomic_term_list_free_rec_var_false_cases hNoFree with
    hNotExcept | hBoundVar
  · have hNotMem :
        (s, __eo_to_smt_type T) ∉ exceptVars.map EoVarKey.toSmt :=
      EoVarEnvPerm.toSmt_not_mem_of_find_neg_true
        hExcept hWf hNotExcept
    exact hAgree.vars_eq s (__eo_to_smt_type T) (Or.inr hNotMem)
  · have hMem :
        (s, T) ∈ boundVars :=
      EoVarEnvPerm.mem_of_find_neg_false hBound hBoundVar
    have hSmtMem :
        (s, __eo_to_smt_type T) ∈ boundVars.map EoVarKey.toSmt :=
      List.mem_map.2 ⟨(s, T), hMem, by simp [EoVarKey.toSmt]⟩
    exact hAgree.vars_eq s (__eo_to_smt_type T) (Or.inl hSmtMem)

theorem smt_model_eval_var_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {s : native_String} {T except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N) :
  __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
    __smtx_model_eval N (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def]
  exact
    native_model_var_lookup_eq_of_contains_atomic_term_list_free_rec_var_false_mapped
      hExcept hBound hWf hNoFree hAgree

/--
The quantifier-shaped/list-binder branch only asks the body about free
variables, with the binder list appended to the bound-variable stack.
-/
theorem contains_atomic_term_list_free_rec_list_branch_false_body
    {q x ys body except bound : Term}
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
            body)
          except bound =
        Term.Boolean false)
    :
  __contains_atomic_term_list_free_rec body except
      (__eo_list_concat Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) ys) bound) =
    Term.Boolean false :=
by
  cases except <;> cases bound <;>
    simp [__contains_atomic_term_list_free_rec] at hNoFree ⊢
  all_goals
    exact hNoFree

/--
The ordinary application branch checks both the head and the argument.

The side condition excludes the generated list-binder branch, which has higher
priority in `__contains_atomic_term_list_free_rec`.
-/
theorem contains_atomic_term_list_free_rec_apply_false_cases
    {f a except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNotList :
      ∀ q x ys,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply f a) except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec f except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec a except bound =
      Term.Boolean false :=
by
  rcases hExcept with ⟨exactExcept, hExactExcept, _hExceptEquiv⟩
  rcases hBound with ⟨exactBound, hExactBound, _hBoundEquiv⟩
  cases hExactExcept <;> cases hExactBound <;> cases f <;>
    simp only [__contains_atomic_term_list_free_rec] at hNoFree ⊢ <;>
    try exact eo_ite_true_eq_false_cases hNoFree
  all_goals
    rename_i q y
    cases y <;>
      simp only [__contains_atomic_term_list_free_rec] at hNoFree ⊢ <;>
      try exact eo_ite_true_eq_false_cases hNoFree
  all_goals
    rename_i g ys
    cases g <;>
      simp only [__contains_atomic_term_list_free_rec] at hNoFree ⊢ <;>
      try exact eo_ite_true_eq_false_cases hNoFree
  all_goals
    rename_i x
    exfalso
    exact hNotList _ x _ rfl

/--
Evaluator congruence for the generic SMT application emitted by the fallback
`__eo_to_smt` application clause.
-/
theorem smt_model_eval_eo_to_smt_apply_generic_eq_of_eval_eq
    {f a : Term} {M N : SmtModel}
    (hTranslate :
      __eo_to_smt (Term.Apply f a) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hAgree : model_agrees_on_globals M N)
    (hFunc :
      __smtx_model_eval M (__eo_to_smt f) =
        __smtx_model_eval N (__eo_to_smt f))
    (hArg :
      __smtx_model_eval M (__eo_to_smt a) =
        __smtx_model_eval N (__eo_to_smt a)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply f a)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply f a)) :=
by
  rw [hTranslate]
  exact
    smtx_model_eval_apply_eq_of_env
      (model_agrees_on_env_nil_of_globals hAgree) hFunc hArg

/--
One-step semantic theorem for the ordinary generic application branch.

The translation/type hypotheses are the usual generic-application side
conditions: the EO translator emitted `SmtTerm.Apply`, and that SMT application
has the standard `typeof_apply` type.  They let us recover SMT translations for
both recursive subterms from the translation of the whole application.
-/
theorem smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false
    {f a except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNotList :
      ∀ q x ys,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
    (hTranslate :
      __eo_to_smt (Term.Apply f a) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hTy :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)))
    (hTrans : eoHasSmtTranslation (Term.Apply f a))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply f a) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hFuncEval :
      eoHasSmtTranslation f ->
        EoVarEnvPerm bound boundVars ->
          __contains_atomic_term_list_free_rec f except bound =
            Term.Boolean false ->
            ∀ {M' N' : SmtModel},
              model_agrees_except_on_eo_env exceptVars boundVars M' N' ->
                __smtx_model_eval M' (__eo_to_smt f) =
                  __smtx_model_eval N' (__eo_to_smt f))
    (hArgEval :
      eoHasSmtTranslation a ->
        EoVarEnvPerm bound boundVars ->
          __contains_atomic_term_list_free_rec a except bound =
            Term.Boolean false ->
            ∀ {M' N' : SmtModel},
              model_agrees_except_on_eo_env exceptVars boundVars M' N' ->
                __smtx_model_eval M' (__eo_to_smt a) =
                  __smtx_model_eval N' (__eo_to_smt a)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply f a)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply f a)) :=
by
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hFuncTrans, hArgTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound hNotList hNoFree with
    ⟨hFuncNoFree, hArgNoFree⟩
  exact
    smt_model_eval_eo_to_smt_apply_generic_eq_of_eval_eq
      hTranslate hAgree.globals
      (hFuncEval hFuncTrans hBound hFuncNoFree hAgree)
      (hArgEval hArgTrans hBound hArgNoFree hAgree)

theorem smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {f a except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNotList :
      ∀ q x ys,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
    (hTranslate :
      __eo_to_smt (Term.Apply f a) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hTy :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)))
    (hTrans : eoHasSmtTranslation (Term.Apply f a))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply f a) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hFuncEval :
      eoHasSmtTranslation f ->
        EoVarEnvPerm bound boundVars ->
          __contains_atomic_term_list_free_rec f except bound =
            Term.Boolean false ->
            ∀ {M' N' : SmtModel},
              model_agrees_except_on_env
                (exceptVars.map EoVarKey.toSmt)
                (boundVars.map EoVarKey.toSmt) M' N' ->
                __smtx_model_eval M' (__eo_to_smt f) =
                  __smtx_model_eval N' (__eo_to_smt f))
    (hArgEval :
      eoHasSmtTranslation a ->
        EoVarEnvPerm bound boundVars ->
          __contains_atomic_term_list_free_rec a except bound =
            Term.Boolean false ->
            ∀ {M' N' : SmtModel},
              model_agrees_except_on_env
                (exceptVars.map EoVarKey.toSmt)
                (boundVars.map EoVarKey.toSmt) M' N' ->
                __smtx_model_eval M' (__eo_to_smt a) =
                  __smtx_model_eval N' (__eo_to_smt a)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply f a)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply f a)) :=
by
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hFuncTrans, hArgTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound hNotList hNoFree with
    ⟨hFuncNoFree, hArgNoFree⟩
  exact
    smt_model_eval_eo_to_smt_apply_generic_eq_of_eval_eq
      hTranslate hAgree.globals
      (hFuncEval hFuncTrans hBound hFuncNoFree hAgree)
      (hArgEval hArgTrans hBound hArgNoFree hAgree)

theorem smtx_model_eval_ite_eq_of_eval_eq
    {M N : SmtModel} {c x y : SmtTerm}
    (hc :
      __smtx_model_eval M c = __smtx_model_eval N c)
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.ite c x y) =
    __smtx_model_eval N (SmtTerm.ite c x y) :=
by
  simp [__smtx_model_eval, hc, hx, hy]

theorem contains_atomic_term_list_free_rec_apply_uop_false_arg
    {op : UserOp} {x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp op) x) except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec x except bound =
    Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by intro q v vs hEq; cases hEq)
      hNoFree with
    ⟨_hHeadNoFree, hArgNoFree⟩
  exact hArgNoFree

theorem contains_atomic_term_list_free_rec_apply_apply_uop_false_args
    {op : UserOp} {x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hXNotList :
      ∀ v vs,
        x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp op) x) y) except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec x except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec y except bound =
      Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by
        intro q v vs hEq
        cases hEq
        exact hXNotList v vs rfl)
      hNoFree with
    ⟨hHeadNoFree, hYNoFree⟩
  have hXNoFree :
      __contains_atomic_term_list_free_rec x except bound =
        Term.Boolean false :=
    contains_atomic_term_list_free_rec_apply_uop_false_arg
      hExcept hBound hHeadNoFree
  exact ⟨hXNoFree, hYNoFree⟩

theorem contains_atomic_term_list_free_rec_apply_apply_apply_uop_false_args
    {op : UserOp} {c x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hCNotList :
      ∀ v vs,
        c ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hXNotList :
      ∀ v vs,
        x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)
          except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec c except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec x except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec y except bound =
      Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by
        intro q v vs hEq
        cases hEq
        exact hXNotList v vs rfl)
      hNoFree with
    ⟨hHeadNoFree, hYNoFree⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound hCNotList hHeadNoFree with
    ⟨hCNoFree, hXNoFree⟩
  exact ⟨hCNoFree, hXNoFree, hYNoFree⟩

theorem smt_model_eval_apply_not_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.not) x))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp UserOp.not) x) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) :=
by
  have hXNoFree :
      __contains_atomic_term_list_free_rec x except bound =
        Term.Boolean false :=
    contains_atomic_term_list_free_rec_apply_uop_false_arg
      hExcept hBound hNoFree
  have hXTrans :
      eoHasSmtTranslation x :=
    not_arg_has_smt_translation_of_has_smt_translation hTrans
  change
    __smtx_model_eval M (SmtTerm.not (__eo_to_smt x)) =
      __smtx_model_eval N (SmtTerm.not (__eo_to_smt x))
  exact
    smtx_model_eval_not_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)

theorem smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp} {x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) x))
    (hArgTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) x) ->
        eoHasSmtTranslation x)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp op) x) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hEval :
      __smtx_model_eval M (__eo_to_smt x) =
        __smtx_model_eval N (__eo_to_smt x) ->
      __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
        __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) x)))
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) x)) :=
by
  have hXNoFree :
      __contains_atomic_term_list_free_rec x except bound =
        Term.Boolean false :=
    contains_atomic_term_list_free_rec_apply_uop_false_arg
      hExcept hBound hNoFree
  exact
    hEval
      (ih hXLt hExcept hBound (hArgTrans hTrans) hXNoFree hAgree)

theorem smt_model_eval_apply_apply_and_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) :=
by
  rcases and_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        (by decide) (by decide) hTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_and_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_or_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) :=
by
  rcases or_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        (by decide) (by decide) hTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_or_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_imp_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) :=
by
  rcases imp_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        (by decide) (by decide) hTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_imp_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_xor_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) :=
by
  rcases xor_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        (by decide) (by decide) hTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.xor (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.xor (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_xor_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_eq_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :=
by
  rcases eq_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        (by decide) (by decide) hTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_eq_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_uop_binary_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp} {x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hArgsTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp op) x) y) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hEval :
      __smtx_model_eval M (__eo_to_smt x) =
        __smtx_model_eval N (__eo_to_smt x) ->
      __smtx_model_eval M (__eo_to_smt y) =
        __smtx_model_eval N (__eo_to_smt y) ->
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) =
        __smtx_model_eval N
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)))
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) :=
by
  rcases hArgsTrans hTrans with ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (term_not_eo_list_cons_of_has_smt_translation hXTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  exact
    hEval
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_apply_ite_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {c x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hCLt : sizeOf c < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)) :=
by
  rcases ite_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hCTrans, hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_apply_uop_false_args
      hExcept hBound
      (term_not_eo_list_cons_of_has_smt_translation hCTrans)
      (term_not_eo_list_cons_of_has_smt_translation hXTrans)
      hNoFree with
    ⟨hCNoFree, hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_ite_eq_of_eval_eq
      (ih hCLt hExcept hBound hCTrans hCNoFree hAgree)
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp} {c x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hCLt : sizeOf c < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y))
    (hArgsTrans :
      eoHasSmtTranslation
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y) ->
        eoHasSmtTranslation c ∧
          eoHasSmtTranslation x ∧
          eoHasSmtTranslation y)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hEval :
      __smtx_model_eval M (__eo_to_smt c) =
        __smtx_model_eval N (__eo_to_smt c) ->
      __smtx_model_eval M (__eo_to_smt x) =
        __smtx_model_eval N (__eo_to_smt x) ->
      __smtx_model_eval M (__eo_to_smt y) =
        __smtx_model_eval N (__eo_to_smt y) ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)) =
        __smtx_model_eval N
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)))
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)) :=
by
  rcases hArgsTrans hTrans with ⟨hCTrans, hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_apply_uop_false_args
      hExcept hBound
      (term_not_eo_list_cons_of_has_smt_translation hCTrans)
      (term_not_eo_list_cons_of_has_smt_translation hXTrans)
      hNoFree with
    ⟨hCNoFree, hXNoFree, hYNoFree⟩
  exact
    hEval
      (ih hCLt hExcept hBound hCTrans hCNoFree hAgree)
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

/--
Evaluator congruence for the SMT existential chain produced from an exact EO
binder list.

The body hypothesis is stated at the final bound stack
`binderVars.reverse ++ boundVars`, because SMT evaluation pushes the binders in
front of the current model one at a time.
-/
theorem smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq
    {vs : Term} {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hAgree : model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_eo_env exceptVars
          (binderVars.reverse ++ boundVars) M' N' ->
          __smtx_model_eval M' body =
            __smtx_model_eval N' body) :
  __smtx_model_eval M (__eo_to_smt_exists vs body) =
    __smtx_model_eval N (__eo_to_smt_exists vs body) :=
by
  induction hEnv generalizing boundVars M N body with
  | nil =>
      exact hBody (by simpa using hAgree)
  | cons hTail ih =>
      rename_i s T vs tailVars
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists vs body)) =
          __smtx_model_eval N
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists vs body))
      exact
        smtx_model_eval_exists_eq_of_body_eval_eq
          (fun v =>
            ih
              (boundVars := (s, T) :: boundVars)
              (M := native_model_push M s (__eo_to_smt_type T) v)
              (N := native_model_push N s (__eo_to_smt_type T) v)
              (body := body)
              (model_agrees_except_on_eo_env_push_same hAgree)
              (by
                intro M' N' hAgreeTail
                apply hBody
                simpa [List.reverse_cons, List.append_assoc]
                  using hAgreeTail))

/--
Evaluator congruence for the SMT encoding of EO `forall`.

EO forall translates through `not (exists ... (not body))`, so this is just the
existential-chain congruence with two `not` congruence steps.
-/
theorem smt_model_eval_eo_to_smt_forall_encoding_eq_of_body_eval_eq
    {vs : Term} {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hAgree : model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_eo_env exceptVars
          (binderVars.reverse ++ boundVars) M' N' ->
          __smtx_model_eval M' body =
            __smtx_model_eval N' body) :
  __smtx_model_eval M
      (SmtTerm.not (__eo_to_smt_exists vs (SmtTerm.not body))) =
    __smtx_model_eval N
      (SmtTerm.not (__eo_to_smt_exists vs (SmtTerm.not body))) :=
by
  exact
    smtx_model_eval_not_eq_of_eval_eq
      (smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq
        hEnv hAgree
      (by
        intro M' N' hAgree'
        exact smtx_model_eval_not_eq_of_eval_eq (hBody hAgree')))

theorem smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_mapped
    {vs : Term} {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_env
          (exceptVars.map EoVarKey.toSmt)
          ((binderVars.reverse ++ boundVars).map EoVarKey.toSmt)
          M' N' ->
          __smtx_model_eval M' body =
            __smtx_model_eval N' body) :
  __smtx_model_eval M (__eo_to_smt_exists vs body) =
    __smtx_model_eval N (__eo_to_smt_exists vs body) :=
by
  induction hEnv generalizing boundVars M N body with
  | nil =>
      exact hBody (by simpa using hAgree)
  | cons hTail ih =>
      rename_i s T vs tailVars
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists vs body)) =
          __smtx_model_eval N
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists vs body))
      exact
        smtx_model_eval_exists_eq_of_body_eval_eq
          (fun v =>
            ih
              (boundVars := (s, T) :: boundVars)
              (M := native_model_push M s (__eo_to_smt_type T) v)
              (N := native_model_push N s (__eo_to_smt_type T) v)
              (body := body)
              (by
                simpa [EoVarKey.toSmt] using
                  model_agrees_except_on_env_push_same hAgree)
              (by
                intro M' N' hAgreeTail
                apply hBody
                simpa [List.reverse_cons, List.append_assoc,
                  List.map_append, EoVarKey.toSmt] using hAgreeTail))

theorem smt_model_eval_eo_to_smt_forall_encoding_eq_of_body_eval_eq_mapped
    {vs : Term} {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_env
          (exceptVars.map EoVarKey.toSmt)
          ((binderVars.reverse ++ boundVars).map EoVarKey.toSmt)
          M' N' ->
          __smtx_model_eval M' body =
            __smtx_model_eval N' body) :
  __smtx_model_eval M
      (SmtTerm.not (__eo_to_smt_exists vs (SmtTerm.not body))) =
    __smtx_model_eval N
      (SmtTerm.not (__eo_to_smt_exists vs (SmtTerm.not body))) :=
by
  exact
    smtx_model_eval_not_eq_of_eval_eq
      (smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_mapped
        hEnv hAgree
        (by
          intro M' N' hAgree'
          exact smtx_model_eval_not_eq_of_eval_eq (hBody hAgree')))

/--
Evaluator congruence for the nonempty quantifier-shaped EO branch.

The free-variable checker treats any `Apply (Apply q nonempty-list) body` as a
binder branch; the translation proof tells us that the head is actually
`forall` or `exists`.
-/
theorem smt_model_eval_uop_list_branch_eq_of_body_eval_eq
    {op : UserOp} {v vs body : Term}
    {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hEnv :
      EoVarEnv
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) binderVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hAgree : model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_eo_env exceptVars
          (binderVars.reverse ++ boundVars) M' N' ->
          __smtx_model_eval M' (__eo_to_smt body) =
            __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst op
    change
      __smtx_model_eval M
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body)))) =
        __smtx_model_eval N
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body))))
    exact
      smt_model_eval_eo_to_smt_forall_encoding_eq_of_body_eval_eq
        hEnv hAgree hBody
  · subst op
    change
      __smtx_model_eval M
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (__eo_to_smt body)) =
        __smtx_model_eval N
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (__eo_to_smt body))
    exact
      smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq
        hEnv hAgree hBody

theorem smt_model_eval_uop_list_branch_eq_of_body_eval_eq_mapped
    {op : UserOp} {v vs body : Term}
    {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hEnv :
      EoVarEnv
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) binderVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_env
          (exceptVars.map EoVarKey.toSmt)
          ((binderVars.reverse ++ boundVars).map EoVarKey.toSmt)
          M' N' ->
          __smtx_model_eval M' (__eo_to_smt body) =
            __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst op
    change
      __smtx_model_eval M
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body)))) =
        __smtx_model_eval N
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body))))
    exact
      smt_model_eval_eo_to_smt_forall_encoding_eq_of_body_eval_eq_mapped
        hEnv hAgree hBody
  · subst op
    change
      __smtx_model_eval M
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (__eo_to_smt body)) =
        __smtx_model_eval N
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (__eo_to_smt body))
    exact
      smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_mapped
        hEnv hAgree hBody

private theorem eo_requires_true_false_eq_false
    {c : Term}
    (h :
      __eo_requires c (Term.Boolean true) (Term.Boolean false) =
        Term.Boolean false) :
  c = Term.Boolean true :=
by
  cases c <;> simp [__eo_requires, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b <;> simp at h ⊢

/--
Fallback case for `__contains_atomic_term_list_free_rec`.

For non-recursive terms, the checker returns `false` by first proving that the
term is closed at the empty environment.  Under SMT translation, closed EO terms
evaluate the same in any two models that agree on globals.
-/
theorem smt_model_eval_eq_of_contains_atomic_term_list_free_rec_fallback
    {t except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hTrans : eoHasSmtTranslation t)
    (hNoFree :
      __eo_requires (__is_closed_rec t Term.__eo_List_nil)
          (Term.Boolean true) (Term.Boolean false) =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N) :
  __smtx_model_eval M (__eo_to_smt t) =
    __smtx_model_eval N (__eo_to_smt t) :=
by
  have hClosedRec :
      __is_closed_rec t Term.__eo_List_nil = Term.Boolean true :=
    eo_requires_true_false_eq_false hNoFree
  have hClosed :
      __eo_is_closed t = Term.Boolean true := by
    simpa [is_closed_rec_eq_eo_is_closed_of_has_smt_translation hTrans]
      using hClosedRec
  exact smt_model_eval_eq_of_eo_closed t hClosed M N hAgree.globals

theorem smt_model_eval_eq_of_contains_atomic_term_list_free_rec_fallback_mapped
    {t except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hTrans : eoHasSmtTranslation t)
    (hNoFree :
      __eo_requires (__is_closed_rec t Term.__eo_List_nil)
          (Term.Boolean true) (Term.Boolean false) =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N) :
  __smtx_model_eval M (__eo_to_smt t) =
    __smtx_model_eval N (__eo_to_smt t) :=
by
  have hClosedRec :
      __is_closed_rec t Term.__eo_List_nil = Term.Boolean true :=
    eo_requires_true_false_eq_false hNoFree
  have hClosed :
      __eo_is_closed t = Term.Boolean true := by
    simpa [is_closed_rec_eq_eo_is_closed_of_has_smt_translation hTrans]
      using hClosedRec
  exact smt_model_eval_eq_of_eo_closed t hClosed M N hAgree.globals

theorem contains_atomic_term_list_free_rec_fallback_eq_of_shape
    {t except bound : Term}
    (hExcept : except ≠ Term.Stuck)
    (hBound : bound ≠ Term.Stuck)
    (hNotStuck : t ≠ Term.Stuck)
    (hNotApply : ∀ f a, t ≠ Term.Apply f a)
    (hNotVar : ∀ name T, t ≠ Term.Var name T)
    (hNoFree :
      __contains_atomic_term_list_free_rec t except bound =
        Term.Boolean false) :
  __eo_requires (__is_closed_rec t Term.__eo_List_nil)
      (Term.Boolean true) (Term.Boolean false) =
    Term.Boolean false :=
by
  cases t
  case Stuck =>
    exact False.elim (hNotStuck rfl)
  case Apply f a =>
    exact False.elim (hNotApply f a rfl)
  case Var name T =>
    exact False.elim (hNotVar name T rfl)
  all_goals
    cases except <;> cases bound <;>
      simp [__contains_atomic_term_list_free_rec] at hNoFree ⊢
  all_goals
    exact hNoFree

theorem smt_model_eval_eq_of_contains_atomic_term_list_free_rec_non_apply_false_mapped
    {t except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans : eoHasSmtTranslation t)
    (hNotApply : ∀ f a, t ≠ Term.Apply f a)
    (hNoFree :
      __contains_atomic_term_list_free_rec t except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N) :
  __smtx_model_eval M (__eo_to_smt t) =
    __smtx_model_eval N (__eo_to_smt t) :=
by
  cases t
  case Stuck =>
      simp [__contains_atomic_term_list_free_rec] at hNoFree
  case Apply f a =>
      exact False.elim (hNotApply f a rfl)
  case Var name T =>
      cases name
      case String s =>
          exact
            smt_model_eval_var_eq_of_contains_atomic_term_list_free_rec_false_mapped
              hExcept hBound
              (smtx_type_wf_of_var_has_smt_translation hTrans)
              hNoFree hAgree
      all_goals
        exfalso
        unfold eoHasSmtTranslation at hTrans
        change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
        exact hTrans TranslationProofs.smtx_typeof_none
  all_goals
    have hReq :=
      contains_atomic_term_list_free_rec_fallback_eq_of_shape
        (EoVarEnvPerm.ne_stuck hExcept)
        (EoVarEnvPerm.ne_stuck hBound)
        (by intro h; cases h)
        hNotApply
        (by intro name T h; cases h)
        hNoFree
    exact
      smt_model_eval_eq_of_contains_atomic_term_list_free_rec_fallback_mapped
        (except := except) (bound := bound) hTrans hReq hAgree

/--
The obligations needed by the recursive semantic proof in the quantifier-shaped
`UOp` branch.

When the branch has an SMT translation and the free-variable check returns
`false`, the body is translation-safe, the binder list is an exact EO variable
environment, the bound stack extends by that binder list, and the body inherits
the `false` free-variable check under the extended bound stack.
-/
theorem body_obligations_of_contains_atomic_term_list_free_rec_uop_list_branch
    {op : UserOp} {v vs body except bound : Term}
    {boundVars : List EoVarKey}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false) :
  eoHasSmtTranslation body ∧
    ∃ binderVars,
      EoVarEnv
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) binderVars ∧
      EoVarEnvPerm
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
        (binderVars.reverse ++ boundVars) ∧
      __contains_atomic_term_list_free_rec body except
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
        Term.Boolean false :=
by
  have hBodyTrans :
      eoHasSmtTranslation body :=
    body_has_smt_translation_of_uop_list_branch_has_smt_translation
      hTrans
  rcases eo_var_env_of_uop_list_branch_has_smt_translation hTrans with
    ⟨binderVars, hBinderEnv⟩
  exact
    ⟨hBodyTrans,
      ⟨binderVars, hBinderEnv,
        EoVarEnvPerm.concat_rev hBinderEnv hBound,
        contains_atomic_term_list_free_rec_list_branch_false_body
          hNoFree⟩⟩

theorem body_has_smt_translation_of_list_branch_has_smt_translation
    {q v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  eoHasSmtTranslation body :=
by
  rcases
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst q
    exact
      body_has_smt_translation_of_uop_list_branch_has_smt_translation
        hTrans
  · subst q
    exact
      body_has_smt_translation_of_uop_list_branch_has_smt_translation
        hTrans

/--
Raw generated-list-branch obligations.

This is the same package as the `UOp`-specific theorem above, but it matches
the actual first clause of `__contains_atomic_term_list_free_rec`, whose head is
an arbitrary term `q`.  SMT translation forces `q` to be a real quantifier.
-/
theorem body_obligations_of_contains_atomic_term_list_free_rec_list_branch
    {q v vs body except bound : Term}
    {boundVars : List EoVarKey}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false) :
  eoHasSmtTranslation body ∧
    ∃ binderVars,
      EoVarEnv
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) binderVars ∧
      EoVarEnvPerm
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
        (binderVars.reverse ++ boundVars) ∧
      __contains_atomic_term_list_free_rec body except
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
        Term.Boolean false :=
by
  have hBodyTrans :
      eoHasSmtTranslation body :=
    body_has_smt_translation_of_list_branch_has_smt_translation hTrans
  rcases eo_var_env_of_list_branch_has_smt_translation hTrans with
    ⟨binderVars, hBinderEnv⟩
  exact
    ⟨hBodyTrans,
      ⟨binderVars, hBinderEnv,
        EoVarEnvPerm.concat_rev hBinderEnv hBound,
        contains_atomic_term_list_free_rec_list_branch_false_body
          hNoFree⟩⟩

/--
One-step semantic theorem for the quantifier-shaped branch.

This is the hook needed by the main recursive proof: once the recursive
hypothesis can prove the body under the extended bound stack, this theorem
turns that into evaluation equality for the whole quantified term.
-/
theorem smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false
    {op : UserOp} {v vs body except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hBodyEval :
      eoHasSmtTranslation body ->
        ∀ {bodyBoundVars : List EoVarKey},
          EoVarEnvPerm
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
            bodyBoundVars ->
          __contains_atomic_term_list_free_rec body except
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
            Term.Boolean false ->
          ∀ {M' N' : SmtModel},
            model_agrees_except_on_eo_env exceptVars bodyBoundVars M' N' ->
              __smtx_model_eval M' (__eo_to_smt body) =
                __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    body_obligations_of_contains_atomic_term_list_free_rec_uop_list_branch
      hBound hTrans hNoFree with
    ⟨hBodyTrans, binderVars, hBinderEnv, hExtendedBound, hBodyNoFree⟩
  exact
    smt_model_eval_uop_list_branch_eq_of_body_eval_eq
      hBinderEnv hTrans hAgree
      (by
        intro M' N' hAgree'
        exact
          hBodyEval hBodyTrans hExtendedBound hBodyNoFree hAgree')

theorem smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {op : UserOp} {v vs body except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBodyEval :
      eoHasSmtTranslation body ->
        ∀ {bodyBoundVars : List EoVarKey},
          EoVarEnvPerm
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
            bodyBoundVars ->
          __contains_atomic_term_list_free_rec body except
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
            Term.Boolean false ->
          ∀ {M' N' : SmtModel},
            model_agrees_except_on_env
              (exceptVars.map EoVarKey.toSmt)
              (bodyBoundVars.map EoVarKey.toSmt) M' N' ->
              __smtx_model_eval M' (__eo_to_smt body) =
                __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    body_obligations_of_contains_atomic_term_list_free_rec_uop_list_branch
      hBound hTrans hNoFree with
    ⟨hBodyTrans, binderVars, hBinderEnv, hExtendedBound, hBodyNoFree⟩
  exact
    smt_model_eval_uop_list_branch_eq_of_body_eval_eq_mapped
      hBinderEnv hTrans hAgree
      (by
        intro M' N' hAgree'
        exact
          hBodyEval hBodyTrans hExtendedBound hBodyNoFree hAgree')

/--
One-step semantic theorem for the raw generated quantifier/list branch.

This is the branch hook with the exact shape generated by
`__contains_atomic_term_list_free_rec`.
-/
theorem smt_model_eval_list_branch_eq_of_contains_atomic_term_list_free_rec_false
    {q v vs body except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hBodyEval :
      eoHasSmtTranslation body ->
        ∀ {bodyBoundVars : List EoVarKey},
          EoVarEnvPerm
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
            bodyBoundVars ->
          __contains_atomic_term_list_free_rec body except
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
            Term.Boolean false ->
          ∀ {M' N' : SmtModel},
            model_agrees_except_on_eo_env exceptVars bodyBoundVars M' N' ->
              __smtx_model_eval M' (__eo_to_smt body) =
                __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst q
    exact
      smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false
        hBound hTrans hNoFree hAgree hBodyEval
  · subst q
    exact
      smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false
        hBound hTrans hNoFree hAgree hBodyEval

theorem smt_model_eval_list_branch_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {q v vs body except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBodyEval :
      eoHasSmtTranslation body ->
        ∀ {bodyBoundVars : List EoVarKey},
          EoVarEnvPerm
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
            bodyBoundVars ->
          __contains_atomic_term_list_free_rec body except
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
            Term.Boolean false ->
          ∀ {M' N' : SmtModel},
            model_agrees_except_on_env
              (exceptVars.map EoVarKey.toSmt)
              (bodyBoundVars.map EoVarKey.toSmt) M' N' ->
              __smtx_model_eval M' (__eo_to_smt body) =
                __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst q
    exact
      smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false_mapped
        hBound hTrans hNoFree hAgree hBodyEval
  · subst q
    exact
      smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false_mapped
        hBound hTrans hNoFree hAgree hBodyEval
