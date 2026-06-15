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

private theorem smtx_typeof_none_ne_bool :
    __smtx_typeof SmtTerm.None ≠ SmtType.Bool :=
  TranslationProofs.smtx_typeof_none_ne_bool

private theorem smtx_typeof_not_arg_of_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  cases h : __smtx_typeof t <;>
    simp [h, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_not_bool_of_arg_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  cases h : __smtx_typeof t <;>
    simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢

private theorem qexists_non_nil_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None ->
    x ≠ Term.__eo_List_nil := by
  intro hNN hx
  subst x
  apply hNN
  unfold qexists qterm
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_non_nil_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    x ≠ Term.__eo_List_nil := by
  intro hNN hx
  subst x
  apply hNN
  unfold qforall qterm
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem smtx_typeof_eo_to_smt_exists_bool_of_non_nil_non_none
    (xs : Term) (body : SmtTerm)
    (hNN : __smtx_typeof (__eo_to_smt_exists xs body) ≠ SmtType.None)
    (hNonNil : xs ≠ Term.__eo_List_nil) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  induction xs, body using __eo_to_smt_exists.induct with
  | case1 F =>
      exact False.elim (hNonNil rfl)
  | case2 s T xs F ih =>
      change
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs F)) =
          SmtType.Bool
      rw [smtx_typeof_exists_term_eq]
      by_cases hTail :
          __smtx_typeof (__eo_to_smt_exists xs F) = SmtType.Bool
      · simp [hTail, native_ite, native_Teq]
        by_cases hGuard :
            __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool =
              SmtType.None
        · have hNone :
              __smtx_typeof
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists xs F)) =
                SmtType.None := by
            rw [smtx_typeof_exists_term_eq]
            simp [hTail, hGuard, native_ite, native_Teq]
          exact False.elim (hNN hNone)
        · exact smtx_typeof_guard_wf_of_non_none
            (__eo_to_smt_type T) SmtType.Bool hGuard
      · have hNone :
            __smtx_typeof
                (SmtTerm.exists s (__eo_to_smt_type T)
                  (__eo_to_smt_exists xs F)) =
              SmtType.None := by
          rw [smtx_typeof_exists_term_eq]
          cases hTy : __smtx_typeof (__eo_to_smt_exists xs F) <;>
            simp [native_ite, native_Teq]
          · exact False.elim (hTail hTy)
        exact False.elim (hNN hNone)
  | case3 xs F hNotNil hNotConsVar =>
      have hNone :
          __smtx_typeof (__eo_to_smt_exists xs F) = SmtType.None := by
        cases xs with
        | Apply f a =>
            cases f with
            | Apply g y =>
                cases g with
                | __eo_List_cons =>
                    cases y with
                    | Var name T =>
                        cases name with
                        | String s =>
                            exact False.elim (hNotConsVar s T a rfl)
                        | _ =>
                            simp [__eo_to_smt_exists,
                              TranslationProofs.smtx_typeof_none]
                    | _ =>
                        simp [__eo_to_smt_exists,
                          TranslationProofs.smtx_typeof_none]
                | _ =>
                    simp [__eo_to_smt_exists,
                      TranslationProofs.smtx_typeof_none]
            | _ =>
                simp [__eo_to_smt_exists,
                  TranslationProofs.smtx_typeof_none]
        | __eo_List_nil =>
            exact False.elim (hNotNil rfl)
        | _ =>
            simp [__eo_to_smt_exists,
              TranslationProofs.smtx_typeof_none]
      exact False.elim (hNN hNone)

private theorem qexists_typeof_bool_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool := by
  intro hNN
  have hx : x ≠ Term.__eo_List_nil :=
    qexists_non_nil_of_non_none x F hNN
  rw [eo_to_smt_exists_eq x F hx] at hNN ⊢
  exact smtx_typeof_eo_to_smt_exists_bool_of_non_nil_non_none
    x (__eo_to_smt F) hNN hx

private theorem qforall_typeof_bool_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
  intro hNN
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F hNN
  rw [eo_to_smt_forall_eq x F hx] at hNN ⊢
  exact smtx_typeof_not_bool_of_arg_bool _
    (smtx_typeof_not_arg_of_non_none _ hNN)

private theorem qterm_typeof_bool_of_quant_non_none
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNN : __smtx_typeof (__eo_to_smt (qterm Q x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool := by
  rcases hQ with hForall | hExists
  · subst Q
    exact qforall_typeof_bool_of_non_none x F hNN
  · subst Q
    exact qexists_typeof_bool_of_non_none x F hNN

private theorem qexists_body_typeof_bool_of_typeof_bool
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
  intro hTy
  have hx : x ≠ Term.__eo_List_nil :=
    qexists_non_nil_of_non_none x F (by rw [hTy]; simp)
  rw [eo_to_smt_exists_eq x F hx] at hTy
  exact TranslationProofs.eo_to_smt_exists_body_bool_of_bool
    x (__eo_to_smt F) hTy

private theorem qforall_body_typeof_bool_of_typeof_bool
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
  intro hTy
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F (by rw [hTy]; simp)
  have hExists :
      __smtx_typeof
          (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool := by
    rw [eo_to_smt_forall_eq x F hx] at hTy
    exact smtx_typeof_not_arg_of_bool _ hTy
  have hNotBody :
      __smtx_typeof (SmtTerm.not (__eo_to_smt F)) = SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool
      x (SmtTerm.not (__eo_to_smt F)) hExists
  exact smtx_typeof_not_arg_of_bool _ hNotBody

private theorem qterm_body_typeof_bool_of_quant_typeof_bool
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
  rcases hQ with hForall | hExists
  · subst Q
    exact qforall_body_typeof_bool_of_typeof_bool x F hTy
  · subst Q
    exact qexists_body_typeof_bool_of_typeof_bool x F hTy

private theorem smtx_model_eval_exists_eq_of_body_constant_bool
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (b : Bool)
    (hDefTy : __smtx_typeof_value (__smtx_type_default T) = T)
    (hDefCan : __smtx_value_canonical_bool (__smtx_type_default T) = true)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.exists s T body) = SmtValue.Boolean b := by
  cases b
  · have hNoSat :
        ¬ ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true := by
      intro hSat
      rcases hSat with ⟨v, hvTy, hvCan, hvEval⟩
      have hEval := hConst v hvTy hvCan
      rw [hBody] at hEval
      rw [hEval] at hvEval
      cases hvEval
    simp [__smtx_model_eval, hNoSat]
  · have hSat :
        ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true := by
      refine ⟨__smtx_type_default T, hDefTy, hDefCan, ?_⟩
      rw [hConst (__smtx_type_default T) hDefTy hDefCan, hBody]
    simp [__smtx_model_eval, hSat]

private theorem smtx_model_eval_forall_eq_of_body_constant_bool
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (b : Bool)
    (hDefTy : __smtx_typeof_value (__smtx_type_default T) = T)
    (hDefCan : __smtx_value_canonical_bool (__smtx_type_default T) = true)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.forall s T body) = SmtValue.Boolean b := by
  cases b
  · have hNotAll :
        ¬ ∀ v : SmtValue,
          __smtx_typeof_value v = T ->
            __smtx_value_canonical_bool v = true ->
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true := by
      intro hAll
      have hEval := hAll (__smtx_type_default T) hDefTy hDefCan
      rw [hConst (__smtx_type_default T) hDefTy hDefCan, hBody] at hEval
      cases hEval
    simp [__smtx_model_eval, hNotAll]
  · have hAll :
        ∀ v : SmtValue,
          __smtx_typeof_value v = T ->
            __smtx_value_canonical_bool v = true ->
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true := by
      intro v hvTy hvCan
      rw [hConst v hvTy hvCan, hBody]
    simp [__smtx_model_eval]
    exact hAll

private theorem native_inhabited_type_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    native_inhabited_type T = true := by
  cases T <;>
    simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
      __smtx_value_canonical_bool, native_and] at hWF ⊢
  all_goals first | exact hWF.1 | assumption

private theorem smtx_type_default_typed_canonical_bool_of_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical_bool (__smtx_type_default T) = true := by
  have hDef :=
    Smtm.type_default_typed_canonical_of_native_inhabited_type T
      (native_inhabited_type_of_type_wf T hWF)
  exact ⟨hDef.1, by simpa [__smtx_value_canonical] using hDef.2⟩

private theorem smtx_model_eval_exists_eq_of_body_constant_bool_of_wf
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (b : Bool)
    (hWF : __smtx_type_wf T = true)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.exists s T body) = SmtValue.Boolean b := by
  rcases smtx_type_default_typed_canonical_bool_of_wf T hWF with
    ⟨hDefTy, hDefCan⟩
  exact smtx_model_eval_exists_eq_of_body_constant_bool
    M s T body b hDefTy hDefCan hBody hConst

private theorem smtx_model_eval_forall_eq_of_body_constant_bool_of_wf
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (b : Bool)
    (hWF : __smtx_type_wf T = true)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.forall s T body) = SmtValue.Boolean b := by
  rcases smtx_type_default_typed_canonical_bool_of_wf T hWF with
    ⟨hDefTy, hDefCan⟩
  exact smtx_model_eval_forall_eq_of_body_constant_bool
    M s T body b hDefTy hDefCan hBody hConst

private theorem native_model_push_shadow
    (M : SmtModel) (s1 s2 : native_String) (T1 T2 : SmtType)
    (v1 v2 : SmtValue)
    (hEq :
      ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
        { isVar := true, name := s2, ty := T2 }) :
    native_model_push (native_model_push M s1 T1 v1) s2 T2 v2 =
      native_model_push M s2 T2 v2 := by
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
              if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
              else values k)
            nativeFuns
      congr
      funext k
      by_cases h2 : k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey)
      · simp [h2]
      · have h1 : k ≠ ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) := by
          intro hk
          exact h2 (by simpa [hEq] using hk)
        simp [h1, h2]

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

private theorem smtx_model_eval_eo_to_smt_exists_eq_of_model_push_const
    (xs : Term) (body : SmtTerm)
    (s : native_String) (T : SmtType) (v : SmtValue)
    (hConst : ∀ M : SmtModel,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    ∀ M : SmtModel,
      __smtx_model_eval (native_model_push M s T v)
          (__eo_to_smt_exists xs body) =
        __smtx_model_eval M (__eo_to_smt_exists xs body) := by
  revert s T v
  induction xs, body using __eo_to_smt_exists.induct with
  | case1 F =>
      intro s T v hConst M
      simpa [__eo_to_smt_exists] using hConst M
  | case2 s' Ueo a F ih =>
      intro s T v hConst M
      let U := __eo_to_smt_type Ueo
      change
        __smtx_model_eval (native_model_push M s T v)
            (SmtTerm.exists s' U (__eo_to_smt_exists a F)) =
          __smtx_model_eval M
            (SmtTerm.exists s' U (__eo_to_smt_exists a F))
      refine smtx_model_eval_exists_eq_of_body_eval_eq ?_
      intro w
      by_cases hKey :
          ({ isVar := true, name := s, ty := T } : SmtModelKey) =
            { isVar := true, name := s', ty := U }
      · rw [native_model_push_shadow M s s' T U v w hKey]
      · rw [native_model_push_comm M s s' T U v w hKey]
        exact ih s T v hConst (native_model_push M s' U w)
  | case3 xs F hNotNil hNotConsVar =>
      intro s T v hConst M
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name Ueo =>
                      cases name with
                      | String s' =>
                          exact False.elim (hNotConsVar s' Ueo a rfl)
                      | _ =>
                          simp [__eo_to_smt_exists, __smtx_model_eval]
                  | _ =>
                      simp [__eo_to_smt_exists, __smtx_model_eval]
              | _ =>
                  simp [__eo_to_smt_exists, __smtx_model_eval]
          | _ =>
              simp [__eo_to_smt_exists, __smtx_model_eval]
      | __eo_List_nil =>
          exact False.elim (hNotNil rfl)
      | _ =>
          simp [__eo_to_smt_exists, __smtx_model_eval]

private theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
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
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro hTy
  have hTail :
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
    smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool ≠ SmtType.None := by
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

private theorem eo_smt_var_env_of_eo_to_smt_exists_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    ∃ vars : List SmtVarKey, EoSmtVarEnv xs vars := by
  intro hTy
  induction xs, body using __eo_to_smt_exists.induct with
  | case1 F =>
      exact ⟨[], EoSmtVarEnv.nil⟩
  | case2 s T xs F ih =>
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists xs F) = SmtType.Bool :=
        smtx_typeof_exists_tail_bool_of_cons_bool s T xs F hTy
      rcases ih hTailTy with ⟨vars, hEnv⟩
      exact ⟨(s, __eo_to_smt_type T) :: vars, EoSmtVarEnv.cons hEnv⟩
  | case3 xs F hNotNil hNotConsVar =>
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name T =>
                      cases name with
                      | String s =>
                          exact False.elim (hNotConsVar s T a rfl)
                      | _ =>
                          simp [__eo_to_smt_exists] at hTy
                  | _ =>
                      simp [__eo_to_smt_exists] at hTy
              | _ =>
                  simp [__eo_to_smt_exists] at hTy
          | _ =>
              simp [__eo_to_smt_exists] at hTy
      | __eo_List_nil =>
          exact False.elim (hNotNil rfl)
      | _ =>
          simp [__eo_to_smt_exists] at hTy

private theorem qterm_binder_env_of_quant_typeof_bool
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTy : __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool) :
    ∃ vars : List SmtVarKey, EoSmtVarEnv x vars := by
  rcases hQ with hForall | hExists
  · subst Q
    have hTyForall :
        __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
      simpa [qforall, qterm] using hTy
    have hx : x ≠ Term.__eo_List_nil :=
      qforall_non_nil_of_non_none x F (by rw [hTyForall]; simp)
    have hExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool := by
      rw [eo_to_smt_forall_eq x F hx] at hTyForall
      exact smtx_typeof_not_arg_of_bool _ hTyForall
    exact eo_smt_var_env_of_eo_to_smt_exists_bool
      x (SmtTerm.not (__eo_to_smt F)) hExistsTy
  · subst Q
    have hTyExists :
        __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool := by
      simpa [qexists, qterm] using hTy
    have hx : x ≠ Term.__eo_List_nil :=
      qexists_non_nil_of_non_none x F (by rw [hTyExists]; simp)
    have hExistsTy :
        __smtx_typeof (__eo_to_smt_exists x (__eo_to_smt F)) =
          SmtType.Bool := by
      rw [eo_to_smt_exists_eq x F hx] at hTyExists
      exact hTyExists
    exact eo_smt_var_env_of_eo_to_smt_exists_bool
      x (__eo_to_smt F) hExistsTy

private theorem smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_bool
    (xs : Term) (body : SmtTerm) (M : SmtModel) (b : Bool)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : ∀ (M : SmtModel) (s : native_String) (T : Term)
      (v : SmtValue),
      __smtx_typeof_value v = __eo_to_smt_type T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (__eo_to_smt_exists xs body) =
      SmtValue.Boolean b := by
  revert hTy hConst M b
  induction xs, body using __eo_to_smt_exists.induct with
  | case1 F =>
      intro M b hTy hBody hConst
      simpa [__eo_to_smt_exists] using hBody
  | case2 s T xs F ih =>
      intro M b hTy hBody hConst
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists xs F) = SmtType.Bool :=
        smtx_typeof_exists_tail_bool_of_cons_bool s T xs F hTy
      have hWF :
          __smtx_type_wf (__eo_to_smt_type T) = true :=
        smtx_type_wf_of_exists_cons_bool s T xs F hTy
      have hTailEval :
          __smtx_model_eval M (__eo_to_smt_exists xs F) =
            SmtValue.Boolean b :=
        ih M b hTailTy hBody hConst
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs F)) =
          SmtValue.Boolean b
      refine smtx_model_eval_exists_eq_of_body_constant_bool_of_wf
        M s (__eo_to_smt_type T) (__eo_to_smt_exists xs F) b hWF
        hTailEval ?_
      intro v hvTy hvCan
      exact smtx_model_eval_eo_to_smt_exists_eq_of_model_push_const
        xs F s (__eo_to_smt_type T) v
        (fun M' => hConst M' s T v hvTy hvCan) M
  | case3 xs F hNotNil hNotConsVar =>
      intro M b hTy hBody hConst
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name T =>
                      cases name with
                      | String s =>
                          exact False.elim (hNotConsVar s T a rfl)
                      | _ =>
                          simp [__eo_to_smt_exists] at hTy
                  | _ =>
                      simp [__eo_to_smt_exists] at hTy
              | _ =>
                  simp [__eo_to_smt_exists] at hTy
          | _ =>
              simp [__eo_to_smt_exists] at hTy
      | __eo_List_nil =>
          exact False.elim (hNotNil rfl)
      | _ =>
          simp [__eo_to_smt_exists] at hTy

private theorem smtx_model_eval_qexists_eq_of_body_constant_bool
    (x F : Term) (M : SmtModel) (b : Bool)
    (hx : x ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool)
    (hBody : __smtx_model_eval M (__eo_to_smt F) = SmtValue.Boolean b)
    (hConst : ∀ (M : SmtModel) (s : native_String) (T : Term)
      (v : SmtValue),
      __smtx_typeof_value v = __eo_to_smt_type T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
          (__eo_to_smt F) =
        __smtx_model_eval M (__eo_to_smt F)) :
    __smtx_model_eval M (__eo_to_smt (qexists x F)) =
      SmtValue.Boolean b := by
  rw [eo_to_smt_exists_eq x F hx] at hTy ⊢
  exact smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_bool
    x (__eo_to_smt F) M b hTy hBody hConst

private theorem smtx_model_eval_qforall_eq_of_body_constant_bool
    (x F : Term) (M : SmtModel) (b : Bool)
    (hx : x ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool)
    (hBody : __smtx_model_eval M (__eo_to_smt F) = SmtValue.Boolean b)
    (hConst : ∀ (M : SmtModel) (s : native_String) (T : Term)
      (v : SmtValue),
      __smtx_typeof_value v = __eo_to_smt_type T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
          (__eo_to_smt F) =
        __smtx_model_eval M (__eo_to_smt F)) :
    __smtx_model_eval M (__eo_to_smt (qforall x F)) =
      SmtValue.Boolean b := by
  have hExistsTy :
      __smtx_typeof (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool := by
    have hTy' := hTy
    rw [eo_to_smt_forall_eq x F hx] at hTy'
    exact smtx_typeof_not_arg_of_bool _ hTy'
  have hNotBody :
      __smtx_model_eval M (SmtTerm.not (__eo_to_smt F)) =
        SmtValue.Boolean (SmtEval.native_not b) := by
    cases b <;>
      simp [__smtx_model_eval, hBody, __smtx_model_eval_not,
        SmtEval.native_not]
  have hNotConst :
      ∀ (M : SmtModel) (s : native_String) (T : Term) (v : SmtValue),
        __smtx_typeof_value v = __eo_to_smt_type T ->
        __smtx_value_canonical_bool v = true ->
        __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
            (SmtTerm.not (__eo_to_smt F)) =
          __smtx_model_eval M (SmtTerm.not (__eo_to_smt F)) := by
    intro M' s T v hvTy hvCan
    rw [__smtx_model_eval.eq_6, __smtx_model_eval.eq_6]
    rw [hConst M' s T v hvTy hvCan]
  have hExistsEval :
      __smtx_model_eval M
          (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtValue.Boolean (SmtEval.native_not b) :=
    smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_bool
      x (SmtTerm.not (__eo_to_smt F)) M (SmtEval.native_not b)
      hExistsTy hNotBody hNotConst
  rw [eo_to_smt_forall_eq x F hx]
  cases b <;>
    simp [__smtx_model_eval, hExistsEval, __smtx_model_eval_not,
      SmtEval.native_not]

private def body_constant_on_eo_binders (body : SmtTerm) : Term -> Prop
  | Term.Apply (Term.Apply Term.__eo_List_cons
      (Term.Var (Term.String s) T)) xs =>
      (∀ (M : SmtModel) (v : SmtValue),
        __smtx_typeof_value v = __eo_to_smt_type T ->
        __smtx_value_canonical_bool v = true ->
        __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
            body =
          __smtx_model_eval M body) ∧
      body_constant_on_eo_binders body xs
  | _ => True

private theorem smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_on_binders
    (xs : Term) (body : SmtTerm) (M : SmtModel) (b : Bool)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool)
    (hBody : __smtx_model_eval M body = SmtValue.Boolean b)
    (hConst : body_constant_on_eo_binders body xs) :
    __smtx_model_eval M (__eo_to_smt_exists xs body) =
      SmtValue.Boolean b := by
  revert hTy hBody hConst M b
  induction xs, body using __eo_to_smt_exists.induct with
  | case1 F =>
      intro M b hTy hBody hConst
      simpa [__eo_to_smt_exists] using hBody
  | case2 s T xs F ih =>
      intro M b hTy hBody hConst
      have hHeadConst :
          ∀ (M : SmtModel) (v : SmtValue),
            __smtx_typeof_value v = __eo_to_smt_type T ->
            __smtx_value_canonical_bool v = true ->
            __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                F =
              __smtx_model_eval M F := hConst.1
      have hTailConst : body_constant_on_eo_binders F xs := hConst.2
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists xs F) = SmtType.Bool :=
        smtx_typeof_exists_tail_bool_of_cons_bool s T xs F hTy
      have hWF :
          __smtx_type_wf (__eo_to_smt_type T) = true :=
        smtx_type_wf_of_exists_cons_bool s T xs F hTy
      have hTailEval :
          __smtx_model_eval M (__eo_to_smt_exists xs F) =
            SmtValue.Boolean b :=
        ih M b hTailTy hBody hTailConst
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs F)) =
          SmtValue.Boolean b
      refine smtx_model_eval_exists_eq_of_body_constant_bool_of_wf
        M s (__eo_to_smt_type T) (__eo_to_smt_exists xs F) b hWF
        hTailEval ?_
      intro v hvTy hvCan
      exact smtx_model_eval_eo_to_smt_exists_eq_of_model_push_const
        xs F s (__eo_to_smt_type T) v
        (fun M' => hHeadConst M' v hvTy hvCan) M
  | case3 xs F hNotNil hNotConsVar =>
      intro M b hTy hBody hConst
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name T =>
                      cases name with
                      | String s =>
                          exact False.elim (hNotConsVar s T a rfl)
                      | _ =>
                          simp [__eo_to_smt_exists] at hTy
                  | _ =>
                      simp [__eo_to_smt_exists] at hTy
              | _ =>
                  simp [__eo_to_smt_exists] at hTy
          | _ =>
              simp [__eo_to_smt_exists] at hTy
      | __eo_List_nil =>
          exact False.elim (hNotNil rfl)
      | _ =>
          simp [__eo_to_smt_exists] at hTy

private theorem smtx_model_eval_qexists_eq_of_body_constant_on_binders
    (x F : Term) (M : SmtModel) (b : Bool)
    (hx : x ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool)
    (hBody : __smtx_model_eval M (__eo_to_smt F) = SmtValue.Boolean b)
    (hConst : body_constant_on_eo_binders (__eo_to_smt F) x) :
    __smtx_model_eval M (__eo_to_smt (qexists x F)) =
      SmtValue.Boolean b := by
  rw [eo_to_smt_exists_eq x F hx] at hTy ⊢
  exact smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_on_binders
    x (__eo_to_smt F) M b hTy hBody hConst

private theorem body_constant_on_eo_binders_not
    (body : SmtTerm) :
    ∀ xs,
      body_constant_on_eo_binders body xs ->
      body_constant_on_eo_binders (SmtTerm.not body) xs
  | xs, hConst => by
      cases xs with
      | Apply f tail =>
          cases f with
          | Apply g head =>
              cases g with
              | __eo_List_cons =>
                  cases head with
                  | Var name T =>
                      cases name with
                      | String s =>
                          constructor
                          · intro M v hvTy hvCan
                            rw [__smtx_model_eval.eq_6, __smtx_model_eval.eq_6]
                            exact congrArg __smtx_model_eval_not
                              (hConst.1 M v hvTy hvCan)
                          · exact body_constant_on_eo_binders_not body tail
                              hConst.2
                      | _ =>
                          trivial
                  | _ =>
                      trivial
              | _ =>
                  trivial
          | _ =>
              trivial
      | _ =>
          trivial

private theorem smtx_model_eval_qforall_eq_of_body_constant_on_binders
    (x F : Term) (M : SmtModel) (b : Bool)
    (hx : x ≠ Term.__eo_List_nil)
    (hTy : __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool)
    (hBody : __smtx_model_eval M (__eo_to_smt F) = SmtValue.Boolean b)
    (hConst : body_constant_on_eo_binders (__eo_to_smt F) x) :
    __smtx_model_eval M (__eo_to_smt (qforall x F)) =
      SmtValue.Boolean b := by
  have hExistsTy :
      __smtx_typeof (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool := by
    have hTy' := hTy
    rw [eo_to_smt_forall_eq x F hx] at hTy'
    exact smtx_typeof_not_arg_of_bool _ hTy'
  have hNotBody :
      __smtx_model_eval M (SmtTerm.not (__eo_to_smt F)) =
        SmtValue.Boolean (SmtEval.native_not b) := by
    cases b <;>
      simp [__smtx_model_eval, hBody, __smtx_model_eval_not,
        SmtEval.native_not]
  have hNotConst :
      body_constant_on_eo_binders (SmtTerm.not (__eo_to_smt F)) x := by
    exact body_constant_on_eo_binders_not (__eo_to_smt F) x hConst
  have hExistsEval :
      __smtx_model_eval M
          (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtValue.Boolean (SmtEval.native_not b) :=
    smtx_model_eval_eo_to_smt_exists_eq_of_body_constant_on_binders
      x (SmtTerm.not (__eo_to_smt F)) M (SmtEval.native_not b)
      hExistsTy hNotBody hNotConst
  rw [eo_to_smt_forall_eq x F hx]
  cases b <;>
    simp [__smtx_model_eval, hExistsEval, __smtx_model_eval_not,
      SmtEval.native_not]

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

private theorem eo_and_eq_true_cases_local (x y : Term) :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_and, __eo_requires, native_ite,
    native_teq, native_and, native_not, SmtEval.native_not] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [hW] at h

private theorem eo_ite_true_branch_eq_false_cases
    (c d : Term) :
    __eo_ite c (Term.Boolean true) d = Term.Boolean false ->
    c = Term.Boolean false ∧ d = Term.Boolean false := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b <;> simp at h ⊢
    exact h

private theorem eo_ite_false_branch_eq_false_cases
    (c d : Term) :
    __eo_ite c (Term.Boolean false) d = Term.Boolean false ->
    c = Term.Boolean true ∨
      (c = Term.Boolean false ∧ d = Term.Boolean false) := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b <;> simp at h ⊢
    exact h

private structure scannerModelRel
    (xs bvs : Term) (M N : SmtModel) : Prop where
  globals : model_agrees_on_globals M N
  vars_eq :
    ∀ (s : native_String) (T : Term),
      __eo_ite
          (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T)))
          (Term.Boolean false)
          (__eo_is_neg (__eo_list_find Term.__eo_List_cons bvs
            (Term.Var (Term.String s) T))) =
        Term.Boolean false ->
      native_model_var_lookup M s (__eo_to_smt_type T) =
        native_model_var_lookup N s (__eo_to_smt_type T)

private theorem scannerModelRel_refl
    (xs bvs : Term) (M : SmtModel) :
    scannerModelRel xs bvs M M := by
  exact ⟨model_agrees_on_globals_refl M, by intro s T _; rfl⟩

private theorem eo_is_neg_list_find_nil_var
    (s : native_String) (T : Term) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons Term.__eo_List_nil
          (Term.Var (Term.String s) T)) =
      Term.Boolean true := by
  simp [__eo_list_find, __eo_is_list, __eo_get_nil_rec,
    __eo_requires, __eo_is_ok, __eo_is_list_nil, __eo_list_find_rec,
    __eo_is_neg, native_ite, native_teq, native_not,
    SmtEval.native_not]
  native_decide

private theorem eo_get_nil_rec_ne_stuck_of_is_list_true {f xs : Term}
    (hList : __eo_is_list f xs = Term.Boolean true) :
    __eo_get_nil_rec f xs ≠ Term.Stuck := by
  intro h
  cases f <;> cases xs <;> simp [__eo_is_list, __eo_is_ok,
    __eo_get_nil_rec, __eo_requires, native_ite, native_teq,
    native_not] at hList h
  all_goals first | exact hList h | exact hList.2 (h hList.1)

private theorem eo_is_list_cons_of_tail_list (x xs : Term)
    (hList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true) :
    __eo_is_list Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) =
      Term.Boolean true := by
  have hNilNe := eo_get_nil_rec_ne_stuck_of_is_list_true hList
  simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
    native_ite, native_teq, native_not]
  exact hNilNe

private theorem eo_is_list_tail_of_apply_apply_list (f x y : Term)
    (hList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply f x) y) =
        Term.Boolean true) :
    __eo_is_list Term.__eo_List_cons y = Term.Boolean true := by
  cases f <;> simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec,
    __eo_requires, native_ite, native_teq, native_not] at hList ⊢
  case __eo_List_cons =>
    cases y <;> simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec,
      __eo_requires, native_ite, native_teq, native_not] at hList ⊢
    all_goals exact hList

private theorem eo_is_list_head_eq_of_apply_apply_list (f x y : Term)
    (hList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply f x) y) =
        Term.Boolean true) :
    f = Term.__eo_List_cons := by
  cases f <;> simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec,
    __eo_requires, native_ite, native_teq, native_not] at hList ⊢

private theorem term_ne_stuck_of_eo_is_list_true {f xs : Term}
    (hList : __eo_is_list f xs = Term.Boolean true) :
    xs ≠ Term.Stuck := by
  intro h
  subst xs
  cases f <;> simp [__eo_is_list] at hList

private theorem term_var_string_ne_stuck (s : native_String) (T : Term) :
    Term.Var (Term.String s) T ≠ Term.Stuck := by
  intro h
  cases h

private theorem eo_eq_true_of_eq_ne_stuck
    {x : Term} (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  simp [__eo_eq, hx, native_teq]

private theorem eo_eq_false_of_ne_nonstuck
    {x y : Term} (hNe : x ≠ y)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_eq x y = Term.Boolean false := by
  simp [__eo_eq, hx, hy, native_teq, eq_comm, hNe]

private theorem eo_eq_var_string_true
    (s : native_String) (T : Term) :
    __eo_eq (Term.Var (Term.String s) T)
      (Term.Var (Term.String s) T) =
    Term.Boolean true := by
  simp [__eo_eq, native_teq]

private theorem eo_eq_var_string_false_of_ne
    {s s' : native_String} {T T' : Term}
    (hNe :
      Term.Var (Term.String s) T ≠
        Term.Var (Term.String s') T') :
    __eo_eq (Term.Var (Term.String s) T)
      (Term.Var (Term.String s') T') =
    Term.Boolean false := by
  simp [__eo_eq, native_teq, eq_comm, hNe]

private theorem eo_eq_var_string_bool_of_ne_stuck
    {z : Term} (hz : z ≠ Term.Stuck) (s : native_String) (T : Term) :
    ∃ b : Bool, __eo_eq z (Term.Var (Term.String s) T) = Term.Boolean b := by
  cases z <;> simp [__eo_eq] at hz ⊢

private theorem native_zlt_plus_one_nonneg
    {n : native_Int}
    (hN : native_zlt n 0 = false) :
    native_zlt (native_zplus n 1) 0 = false := by
  simp [native_zlt, native_zplus] at hN ⊢
  omega

private def eo_var_list : Term -> Prop
  | Term.__eo_List_nil => True
  | Term.Apply (Term.Apply Term.__eo_List_cons
      (Term.Var (Term.String _) _)) xs =>
      eo_var_list xs
  | _ => False

private def eo_var_list_mem (z : Term) : Term -> Prop
  | Term.__eo_List_nil => False
  | Term.Apply (Term.Apply Term.__eo_List_cons x) xs =>
      x = z ∨ eo_var_list_mem z xs
  | _ => False

private theorem eo_smt_var_env_mem_wf_of_exists_bool
    {xs : Term} {vars : List SmtVarKey} {body : SmtTerm}
    (hEnv : EoSmtVarEnv xs vars)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool) :
    ∀ (s : native_String) (T : Term),
      eo_var_list_mem (Term.Var (Term.String s) T) xs ->
        __smtx_type_wf (__eo_to_smt_type T) = true := by
  induction hEnv with
  | nil =>
      intro s T hMem
      exact False.elim hMem
  | cons hTail ih =>
      rename_i s0 T0 tail varsTail
      intro s T hMem
      rcases hMem with hHead | hTailMem
      · cases hHead
        exact smtx_type_wf_of_exists_cons_bool s0 T0 tail body hTy
      · have hTailTy :
            __smtx_typeof (__eo_to_smt_exists tail body) =
              SmtType.Bool :=
          smtx_typeof_exists_tail_bool_of_cons_bool
            s0 T0 tail body hTy
        exact ih hTailTy s T hTailMem

private theorem eo_var_list_of_env :
    ∀ {xs : Term} {vars : List SmtVarKey},
      EoSmtVarEnv xs vars -> eo_var_list xs
  | _, _, EoSmtVarEnv.nil => by
      trivial
  | _, _, EoSmtVarEnv.cons hTail => by
      simpa [eo_var_list] using eo_var_list_of_env hTail

private theorem eo_smt_var_env_of_var_list {xs : Term}
    (hVarList : eo_var_list xs) :
    ∃ vars : List SmtVarKey, EoSmtVarEnv xs vars := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            rcases ih hTailVar with ⟨vars, hEnv⟩
            exact ⟨(s, __eo_to_smt_type T) :: vars,
              EoSmtVarEnv.cons hEnv⟩
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          exact ⟨[], EoSmtVarEnv.nil⟩
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_is_list {xs : Term}
    (hVarList : eo_var_list xs) :
    __eo_is_list Term.__eo_List_cons xs = Term.Boolean true := by
  cases xs with
  | __eo_List_nil =>
      exact EoSmtVarEnv.nil.is_list
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g <;> try exact False.elim hVarList
          case __eo_List_cons =>
            cases x <;> try exact False.elim hVarList
            case Var name T =>
              cases name <;> try exact False.elim hVarList
              case String s =>
                exact eo_is_list_cons_of_tail_list
                  (Term.Var (Term.String s) T) a
                  (eo_var_list_is_list hVarList)
      | _ => exact False.elim hVarList
  | _ => exact False.elim hVarList

private theorem eo_var_list_ne_stuck {xs : Term}
    (hVarList : eo_var_list xs) :
    xs ≠ Term.Stuck := by
  intro h
  subst xs
  exact hVarList

private theorem eo_var_list_erase_all_rec
    {xs : Term} (hVarList : eo_var_list xs) {z : Term}
    (hz : z ≠ Term.Stuck) :
    eo_var_list (__eo_list_erase_all_rec xs z) := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hRec := ih hTailVar
            have hRecNe :
                __eo_list_erase_all_rec y z ≠ Term.Stuck :=
              eo_var_list_ne_stuck hRec
            rcases eo_eq_var_string_bool_of_ne_stuck hz s T with ⟨b, hb⟩
            cases b
            · simpa [eo_var_list, __eo_list_erase_all_rec, hb, __eo_not,
                __eo_prepend_if, hRecNe, term_var_string_ne_stuck s T,
                SmtEval.native_not]
                using hRec
            · simpa [eo_var_list, __eo_list_erase_all_rec, hb, __eo_not,
                __eo_prepend_if, hRecNe, term_var_string_ne_stuck s T,
                SmtEval.native_not]
                using hRec
  | case3 nil =>
      simpa [__eo_list_erase_all_rec, hz]

private theorem eo_var_list_erase_rec
    {xs : Term} (hVarList : eo_var_list xs) {z : Term}
    (hz : z ≠ Term.Stuck) :
    eo_var_list (__eo_list_erase_rec xs z) := by
  induction xs, z using __eo_list_erase_rec.induct with
  | case1 z =>
      exact False.elim hVarList
  | case2 xs hZStuck =>
      exact False.elim (hz rfl)
  | case3 f x y z hZNotStuck ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            by_cases hEq : Term.Var (Term.String s) T = z
            · have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) z =
                    Term.Boolean true := by
                rw [hEq]
                exact eo_eq_true_of_eq_ne_stuck hz
              simpa [eo_var_list, __eo_list_erase_rec, hEqTerm,
                __eo_ite, native_ite, native_teq] using hTailVar
            · have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) z =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hEq hHeadNe hz
              have hRec : eo_var_list (__eo_list_erase_rec y z) :=
                ih hTailVar hz
              have hRecNe :
                  __eo_list_erase_rec y z ≠ Term.Stuck :=
                eo_var_list_ne_stuck hRec
              simpa [eo_var_list, __eo_list_erase_rec, hEqTerm,
                __eo_ite, __eo_mk_apply, hRecNe, native_ite, native_teq]
                using hRec
  | case4 nil z hNil hZ hNotApply =>
      simpa [__eo_list_erase_rec] using hVarList

private theorem eo_var_list_setof_rec
    {xs : Term} (hVarList : eo_var_list xs) :
    eo_var_list (__eo_list_setof_rec xs) := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hSetTail := ih hTailVar
            have hErase :
                eo_var_list
                  (__eo_list_erase_all_rec (__eo_list_setof_rec y)
                    (Term.Var (Term.String s) T)) :=
              eo_var_list_erase_all_rec hSetTail
                (term_var_string_ne_stuck s T)
            have hEraseNe :
                __eo_list_erase_all_rec (__eo_list_setof_rec y)
                    (Term.Var (Term.String s) T) ≠
                  Term.Stuck :=
              eo_var_list_ne_stuck hErase
            simpa [eo_var_list, __eo_list_setof_rec, __eo_mk_apply,
              hEraseNe] using hErase
  | case3 nil =>
      simpa [__eo_list_setof_rec]

private theorem eo_list_setof_rec_is_list_of_var_list
    {xs : Term} (hVarList : eo_var_list xs) :
    __eo_is_list Term.__eo_List_cons (__eo_list_setof_rec xs) =
      Term.Boolean true :=
  eo_var_list_is_list (eo_var_list_setof_rec hVarList)

private theorem eo_var_list_setof
    {xs : Term} (hVarList : eo_var_list xs) :
    eo_var_list (__eo_list_setof Term.__eo_List_cons xs) := by
  have hList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hSetRec : eo_var_list (__eo_list_setof_rec xs) :=
    eo_var_list_setof_rec hVarList
  simpa [__eo_list_setof, hList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hSetRec

private theorem eo_list_erase_all_rec_is_list_of_var_list
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck) :
    __eo_is_list Term.__eo_List_cons (__eo_list_erase_all_rec xs z) =
      Term.Boolean true :=
  eo_var_list_is_list (eo_var_list_erase_all_rec hVarList hz)

private theorem eo_var_list_diff_rec
    {xs ys : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys) :
    eo_var_list (__eo_list_diff_rec xs ys) := by
  induction xs, ys using __eo_list_diff_rec.induct with
  | case1 ys =>
      exact False.elim hXsVar
  | case2 xs hYsStuck =>
      exact False.elim (eo_var_list_ne_stuck hYsVar rfl)
  | case3 f x y ys hYsNotStuck v0 ih =>
      cases f <;> try exact False.elim hXsVar
      case __eo_List_cons =>
        cases x <;> try exact False.elim hXsVar
        case Var name T =>
          cases name <;> try exact False.elim hXsVar
          case String s =>
            have hTailVar : eo_var_list y := hXsVar
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hEraseVar :
                eo_var_list
                  (__eo_list_erase_rec ys (Term.Var (Term.String s) T)) :=
              eo_var_list_erase_rec hYsVar hHeadNe
            have hEraseNe :
                __eo_list_erase_rec ys (Term.Var (Term.String s) T) ≠
                  Term.Stuck :=
              eo_var_list_ne_stuck hEraseVar
            have hRec :
                eo_var_list (__eo_list_diff_rec y v0) :=
              ih hTailVar (by simpa [v0] using hEraseVar)
            have hRecNe : __eo_list_diff_rec y v0 ≠ Term.Stuck :=
              eo_var_list_ne_stuck hRec
            by_cases hSame :
                __eo_list_erase_rec ys (Term.Var (Term.String s) T) = ys
            · have hv0 : v0 = ys := by
                simpa [v0] using hSame
              have hYsNe : ys ≠ Term.Stuck :=
                eo_var_list_ne_stuck hYsVar
              have hEqTerm :
                  __eo_eq v0 ys = Term.Boolean true := by
                rw [hv0]
                exact eo_eq_true_of_eq_ne_stuck hYsNe
              simpa [eo_var_list, __eo_list_diff_rec, v0, hEqTerm,
                __eo_prepend_if, hHeadNe, hRecNe] using hRec
            · have hv0Ne : v0 ≠ ys := by
                simpa [v0] using hSame
              have hYsNe : ys ≠ Term.Stuck :=
                eo_var_list_ne_stuck hYsVar
              have hv0Stuck : v0 ≠ Term.Stuck := by
                simpa [v0] using hEraseNe
              have hEqTerm :
                  __eo_eq v0 ys = Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hv0Ne hv0Stuck hYsNe
              simpa [__eo_list_diff_rec, v0, hEqTerm,
                __eo_prepend_if, hRecNe] using hRec
  | case4 nil ys hNil hYs hNotApply =>
      simpa [__eo_list_diff_rec] using hXsVar

private theorem eo_var_list_diff
    {xs ys : Term} (hXsVar : eo_var_list xs) (hYsVar : eo_var_list ys) :
    eo_var_list (__eo_list_diff Term.__eo_List_cons xs ys) := by
  have hXsList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hXsVar
  have hYsList : __eo_is_list Term.__eo_List_cons ys = Term.Boolean true :=
    eo_var_list_is_list hYsVar
  have hDiffRec : eo_var_list (__eo_list_diff_rec xs ys) :=
    eo_var_list_diff_rec hXsVar hYsVar
  simpa [__eo_list_diff, hXsList, hYsList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hDiffRec

private theorem eo_list_concat_rec_nil_eq_of_var_list
    {xs : Term} (hVarList : eo_var_list xs) :
    __eo_list_concat_rec xs Term.__eo_List_nil = xs := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hRec :
                __eo_list_concat_rec y Term.__eo_List_nil = y :=
              ih hTailVar
            have hTailNe : y ≠ Term.Stuck := eo_var_list_ne_stuck hTailVar
            simp [__eo_list_concat_rec, hRec, __eo_mk_apply, hTailNe]
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          rfl
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_list_concat_nil_eq_of_var_list
    {xs : Term} (hVarList : eo_var_list xs) :
    __eo_list_concat Term.__eo_List_cons xs Term.__eo_List_nil = xs := by
  have hXsList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hNilList :
      __eo_is_list Term.__eo_List_cons Term.__eo_List_nil =
        Term.Boolean true :=
    eo_var_list_is_list (by trivial : eo_var_list Term.__eo_List_nil)
  have hRec : __eo_list_concat_rec xs Term.__eo_List_nil = xs :=
    eo_list_concat_rec_nil_eq_of_var_list hVarList
  simpa [__eo_list_concat, hXsList, hNilList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hRec

private theorem eo_is_neg_list_find_rec_false_of_var_list_mem
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck)
    (hMem : eo_var_list_mem z xs) :
    ∀ n : native_Int,
      native_zlt n 0 = false ->
        __eo_is_neg
            (__eo_list_find_rec xs z (Term.Numeral n)) =
          Term.Boolean false := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hxNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            rcases hMem with hHead | hTail
            · intro n hN
              have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) z =
                    Term.Boolean true := by
                rw [hHead]
                exact eo_eq_true_of_eq_ne_stuck hz
              simp [__eo_list_find_rec, hEqTerm, __eo_ite,
                __eo_is_neg, native_ite, native_teq, hN]
            · intro n hN
              by_cases hEq :
                  Term.Var (Term.String s) T = z
              · have hEqTerm :
                    __eo_eq (Term.Var (Term.String s) T) z =
                      Term.Boolean true := by
                  rw [hEq]
                  exact eo_eq_true_of_eq_ne_stuck hz
                simp [__eo_list_find_rec, hEqTerm, __eo_ite,
                  __eo_is_neg, native_ite, native_teq, hN]
              · have hEqTerm :
                    __eo_eq (Term.Var (Term.String s) T) z =
                      Term.Boolean false :=
                  eo_eq_false_of_ne_nonstuck hEq hxNe hz
                have hN' :
                    native_zlt (native_zplus n 1) 0 = false :=
                  native_zlt_plus_one_nonneg hN
                have hRec :=
                  ih hTailVar hTail (native_zplus n 1) hN'
                simpa [__eo_list_find_rec, hEqTerm, __eo_ite,
                  native_ite, native_teq] using hRec
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          exact False.elim hMem
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_is_neg_list_find_false_of_var_list_mem
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck)
    (hMem : eo_var_list_mem z xs) :
    __eo_is_neg (__eo_list_find Term.__eo_List_cons xs z) =
      Term.Boolean false := by
  have hList : __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hFindRec :
      __eo_is_neg (__eo_list_find_rec xs z (Term.Numeral 0)) =
        Term.Boolean false :=
    eo_is_neg_list_find_rec_false_of_var_list_mem
      hVarList hz hMem 0 hZero
  simpa [__eo_list_find, hList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hFindRec

private theorem eo_var_list_mem_of_eo_is_neg_list_find_rec_false
    {xs z : Term} (hVarList : eo_var_list xs) (hz : z ≠ Term.Stuck) :
    ∀ n : native_Int,
      native_zlt n 0 = false ->
        __eo_is_neg
            (__eo_list_find_rec xs z (Term.Numeral n)) =
          Term.Boolean false ->
        eo_var_list_mem z xs := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hxNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            intro n hN hFind
            by_cases hEq :
                Term.Var (Term.String s) T = z
            · exact Or.inl hEq
            · have hEqTerm :
                  __eo_eq (Term.Var (Term.String s) T) z =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hEq hxNe hz
              have hTailFind :
                  __eo_is_neg
                      (__eo_list_find_rec y z
                        (Term.Numeral (native_zplus n 1))) =
                    Term.Boolean false := by
                simpa [__eo_list_find_rec, hEqTerm, __eo_ite,
                  native_ite, native_teq] using hFind
              have hN' :
                  native_zlt (native_zplus n 1) 0 = false :=
                native_zlt_plus_one_nonneg hN
              exact Or.inr (ih hTailVar (native_zplus n 1) hN'
                hTailFind)
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          intro n hN hFind
          have hNeg : native_zlt (-1 : native_Int) 0 = true := by
            native_decide
          simp [__eo_list_find_rec, __eo_is_neg, hNeg] at hFind
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_var_list_mem_erase_all_rec_of_ne
    {xs z e : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (he : e ≠ Term.Stuck)
    (hNe : z ≠ e) (hMem : eo_var_list_mem z xs) :
    eo_var_list_mem z (__eo_list_erase_all_rec xs e) := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe :
                Term.Var (Term.String s) T ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hEraseTailVar :
                eo_var_list (__eo_list_erase_all_rec y e) :=
              eo_var_list_erase_all_rec hTailVar he
            have hEraseTailNe :
                __eo_list_erase_all_rec y e ≠ Term.Stuck :=
              eo_var_list_ne_stuck hEraseTailVar
            rcases hMem with hHead | hTail
            · have hEHead :
                  e ≠ Term.Var (Term.String s) T := by
                intro hEq
                apply hNe
                exact hHead.symm.trans hEq.symm
              have hEqTerm :
                  __eo_eq e (Term.Var (Term.String s) T) =
                    Term.Boolean false :=
                eo_eq_false_of_ne_nonstuck hEHead he hHeadNe
              simpa [eo_var_list_mem, __eo_list_erase_all_rec,
                hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                hHeadNe, SmtEval.native_not] using
                (Or.inl hHead :
                  Term.Var (Term.String s) T = z ∨
                    eo_var_list_mem z (__eo_list_erase_all_rec y e))
            · have hRec :
                  eo_var_list_mem z (__eo_list_erase_all_rec y e) :=
                ih hTailVar hTail
              by_cases hEHead :
                  e = Term.Var (Term.String s) T
              · have hEqTerm :
                    __eo_eq e (Term.Var (Term.String s) T) =
                      Term.Boolean true := by
                  rw [hEHead]
                  exact eo_eq_true_of_eq_ne_stuck hHeadNe
                simpa [eo_var_list_mem, __eo_list_erase_all_rec,
                  hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                  hHeadNe, SmtEval.native_not] using hRec
              · have hEqTerm :
                    __eo_eq e (Term.Var (Term.String s) T) =
                      Term.Boolean false :=
                  eo_eq_false_of_ne_nonstuck hEHead he hHeadNe
                simpa [eo_var_list_mem, __eo_list_erase_all_rec,
                  hEqTerm, __eo_not, __eo_prepend_if, hEraseTailNe,
                  hHeadNe, SmtEval.native_not] using
                  (Or.inr hRec :
                    Term.Var (Term.String s) T = z ∨
                      eo_var_list_mem z (__eo_list_erase_all_rec y e))
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          exact False.elim hMem
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_is_neg_list_find_cons_of_tail
    (x z xs : Term)
    (hx : x ≠ Term.Stuck) (hz : z ≠ Term.Stuck)
    (hTailVar : eo_var_list xs)
    (hTailFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs z) =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) z) =
      Term.Boolean false := by
  have hTailList :
      __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hTailVar
  have hWholeList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) =
        Term.Boolean true :=
    eo_is_list_cons_of_tail_list x xs hTailList
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hOne : native_zlt (1 : native_Int) 0 = false := by
    native_decide
  have hTailFindRec0 :
      __eo_is_neg
          (__eo_list_find_rec xs z (Term.Numeral 0)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hTailList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hTailFind
  have hTailMem :
      eo_var_list_mem z xs :=
    eo_var_list_mem_of_eo_is_neg_list_find_rec_false
      hTailVar hz 0 hZero hTailFindRec0
  have hTailFindRec1 :
      __eo_is_neg
          (__eo_list_find_rec xs z (Term.Numeral 1)) =
        Term.Boolean false :=
    eo_is_neg_list_find_rec_false_of_var_list_mem
      hTailVar hz hTailMem 1 hOne
  by_cases hEq : x = z
  · have hEqTerm : __eo_eq x z = Term.Boolean true := by
      subst z
      exact eo_eq_true_of_eq_ne_stuck hx
    simp [__eo_list_find, hWholeList, __eo_requires,
      __eo_list_find_rec, hEqTerm, __eo_ite,
      __eo_is_neg, native_ite, native_teq, native_not, SmtEval.native_not]
    native_decide
  · have hEqTerm : __eo_eq x z = Term.Boolean false :=
      eo_eq_false_of_ne_nonstuck hEq hx hz
    simpa [__eo_list_find, hWholeList, hTailList, __eo_requires,
      __eo_list_find_rec, hEqTerm, __eo_ite, native_ite,
      native_teq, native_not, SmtEval.native_not] using hTailFindRec1

private theorem eo_is_neg_list_find_erase_all_rec_of_ne
    {xs z e : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (he : e ≠ Term.Stuck)
    (hNe : z ≠ e)
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs z) =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_erase_all_rec xs e) z) =
      Term.Boolean false := by
  have hXsList :
      __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hEraseVar :
      eo_var_list (__eo_list_erase_all_rec xs e) :=
    eo_var_list_erase_all_rec hVarList he
  have hEraseList :
      __eo_is_list Term.__eo_List_cons
          (__eo_list_erase_all_rec xs e) =
        Term.Boolean true :=
    eo_var_list_is_list hEraseVar
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hFindRec0 :
      __eo_is_neg
          (__eo_list_find_rec xs z (Term.Numeral 0)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hXsList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hFind
  have hMem :
      eo_var_list_mem z xs :=
    eo_var_list_mem_of_eo_is_neg_list_find_rec_false
      hVarList hz 0 hZero hFindRec0
  have hEraseMem :
      eo_var_list_mem z (__eo_list_erase_all_rec xs e) :=
    eo_var_list_mem_erase_all_rec_of_ne hVarList hz he hNe hMem
  have hFindEraseRec :
      __eo_is_neg
          (__eo_list_find_rec (__eo_list_erase_all_rec xs e) z
            (Term.Numeral 0)) =
        Term.Boolean false :=
    eo_is_neg_list_find_rec_false_of_var_list_mem
      hEraseVar hz hEraseMem 0 hZero
  simpa [__eo_list_find, hEraseList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hFindEraseRec

private theorem eo_is_neg_list_find_cons_var_of_tail
    (s s' : native_String) (T T' xs : Term)
    (hTailVar : eo_var_list xs)
    (hTailFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T)) =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s') T')) xs)
          (Term.Var (Term.String s) T)) =
      Term.Boolean false := by
  have hTailList :
      __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hTailVar
  have hWholeList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s') T')) xs) =
        Term.Boolean true :=
    eo_is_list_cons_of_tail_list (Term.Var (Term.String s') T') xs
      hTailList
  have hz : Term.Var (Term.String s) T ≠ Term.Stuck :=
    term_var_string_ne_stuck s T
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hOne : native_zlt (1 : native_Int) 0 = false := by
    native_decide
  have hTailFindRec0 :
      __eo_is_neg
          (__eo_list_find_rec xs (Term.Var (Term.String s) T)
            (Term.Numeral 0)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hTailList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hTailFind
  have hTailMem :
      eo_var_list_mem (Term.Var (Term.String s) T) xs :=
    eo_var_list_mem_of_eo_is_neg_list_find_rec_false
      hTailVar hz 0 hZero hTailFindRec0
  have hTailFindRec1 :
      __eo_is_neg
          (__eo_list_find_rec xs (Term.Var (Term.String s) T)
            (Term.Numeral 1)) =
        Term.Boolean false :=
    eo_is_neg_list_find_rec_false_of_var_list_mem
      hTailVar hz hTailMem 1 hOne
  by_cases hEq :
      Term.Var (Term.String s') T' = Term.Var (Term.String s) T
  · have hEqTerm :
        __eo_eq (Term.Var (Term.String s') T')
            (Term.Var (Term.String s) T) =
          Term.Boolean true := by
      rw [hEq]
      exact eo_eq_var_string_true s T
    simp [__eo_list_find, hWholeList, __eo_requires,
      __eo_list_find_rec, hEqTerm, __eo_ite,
      __eo_is_neg, native_ite, native_teq, native_not, SmtEval.native_not]
    native_decide
  · have hEqTerm :
        __eo_eq (Term.Var (Term.String s') T')
            (Term.Var (Term.String s) T) =
          Term.Boolean false :=
      eo_eq_var_string_false_of_ne hEq
    simpa [__eo_list_find, hWholeList, hTailList, __eo_requires,
      __eo_list_find_rec, hEqTerm, __eo_ite, native_ite,
      native_teq, native_not, SmtEval.native_not] using hTailFindRec1

private theorem eo_is_neg_list_find_tail_of_cons_var_ne
    (s s' : native_String) (T T' xs : Term)
    (hTailVar : eo_var_list xs)
    (hNe :
      Term.Var (Term.String s) T ≠
        Term.Var (Term.String s') T')
    (hFindCons :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) xs)
            (Term.Var (Term.String s') T')) =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons xs
          (Term.Var (Term.String s') T')) =
      Term.Boolean false := by
  have hTailList :
      __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hTailVar
  have hWholeList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs) =
        Term.Boolean true :=
    eo_is_list_cons_of_tail_list (Term.Var (Term.String s) T) xs
      hTailList
  have hHeadNe :
      Term.Var (Term.String s) T ≠ Term.Stuck :=
    term_var_string_ne_stuck s T
  have hTargetNe :
      Term.Var (Term.String s') T' ≠ Term.Stuck :=
    term_var_string_ne_stuck s' T'
  have hEqTerm :
      __eo_eq (Term.Var (Term.String s) T)
          (Term.Var (Term.String s') T') =
        Term.Boolean false :=
    eo_eq_var_string_false_of_ne hNe
  have hTailFindRec1 :
      __eo_is_neg
          (__eo_list_find_rec xs (Term.Var (Term.String s') T')
            (Term.Numeral 1)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hWholeList, hTailList, __eo_requires,
      __eo_list_find_rec, hEqTerm, __eo_ite, native_ite,
      native_teq, native_not, SmtEval.native_not] using hFindCons
  have hOne : native_zlt (1 : native_Int) 0 = false := by
    native_decide
  have hZero : native_zlt (0 : native_Int) 0 = false := by
    native_decide
  have hTailMem :
      eo_var_list_mem (Term.Var (Term.String s') T') xs :=
    eo_var_list_mem_of_eo_is_neg_list_find_rec_false
      hTailVar hTargetNe 1 hOne hTailFindRec1
  have hTailFindRec0 :
      __eo_is_neg
          (__eo_list_find_rec xs (Term.Var (Term.String s') T')
            (Term.Numeral 0)) =
        Term.Boolean false :=
    eo_is_neg_list_find_rec_false_of_var_list_mem
      hTailVar hTargetNe hTailMem 0 hZero
  simpa [__eo_list_find, hTailList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hTailFindRec0

private theorem eo_is_neg_list_find_setof_rec_of_var_list_mem
    {xs z : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (hMem : eo_var_list_mem z xs) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_setof_rec xs) z) =
      Term.Boolean false := by
  induction xs using __eo_list_setof_rec.induct with
  | case1 =>
      exact False.elim hVarList
  | case2 f x y ih =>
      cases f <;> try exact False.elim hVarList
      case __eo_List_cons =>
        cases x <;> try exact False.elim hVarList
        case Var name T =>
          cases name <;> try exact False.elim hVarList
          case String s =>
            let head := Term.Var (Term.String s) T
            have hTailVar : eo_var_list y := hVarList
            have hHeadNe : head ≠ Term.Stuck :=
              term_var_string_ne_stuck s T
            have hSetTailVar :
                eo_var_list (__eo_list_setof_rec y) :=
              eo_var_list_setof_rec hTailVar
            have hEraseVar :
                eo_var_list
                  (__eo_list_erase_all_rec (__eo_list_setof_rec y) head) :=
              eo_var_list_erase_all_rec hSetTailVar hHeadNe
            have hEraseNe :
                __eo_list_erase_all_rec (__eo_list_setof_rec y) head ≠
                  Term.Stuck :=
              eo_var_list_ne_stuck hEraseVar
            rcases hMem with hHead | hTail
            · subst z
              have hEqTerm : __eo_eq head head = Term.Boolean true :=
                eo_eq_true_of_eq_ne_stuck hHeadNe
              have hConsList :
                  __eo_is_list Term.__eo_List_cons
                      (Term.Apply (Term.Apply Term.__eo_List_cons head)
                        (__eo_list_erase_all_rec (__eo_list_setof_rec y)
                          head)) =
                    Term.Boolean true :=
                eo_is_list_cons_of_tail_list head
                  (__eo_list_erase_all_rec (__eo_list_setof_rec y) head)
                  (eo_var_list_is_list hEraseVar)
              simp [head, __eo_list_setof_rec, __eo_mk_apply, hEraseNe,
                __eo_list_find, hConsList, __eo_requires,
                __eo_list_find_rec, hEqTerm, __eo_ite, __eo_is_neg,
                native_ite, native_teq, native_not, SmtEval.native_not]
              native_decide
            · by_cases hEq : head = z
              · subst z
                have hEqTerm : __eo_eq head head = Term.Boolean true :=
                  eo_eq_true_of_eq_ne_stuck hHeadNe
                have hConsList :
                    __eo_is_list Term.__eo_List_cons
                        (Term.Apply (Term.Apply Term.__eo_List_cons head)
                          (__eo_list_erase_all_rec (__eo_list_setof_rec y)
                            head)) =
                      Term.Boolean true :=
                  eo_is_list_cons_of_tail_list head
                    (__eo_list_erase_all_rec (__eo_list_setof_rec y) head)
                    (eo_var_list_is_list hEraseVar)
                simp [head, __eo_list_setof_rec, __eo_mk_apply, hEraseNe,
                  __eo_list_find, hConsList, __eo_requires,
                  __eo_list_find_rec, hEqTerm, __eo_ite, __eo_is_neg,
                  native_ite, native_teq, native_not, SmtEval.native_not]
                native_decide
              · have hZHead : z ≠ head := by
                  intro hZH
                  exact hEq hZH.symm
                have hTailFind :
                    __eo_is_neg
                        (__eo_list_find Term.__eo_List_cons
                          (__eo_list_setof_rec y) z) =
                      Term.Boolean false :=
                  ih hTailVar hTail
                have hTailFindErase :
                    __eo_is_neg
                        (__eo_list_find Term.__eo_List_cons
                          (__eo_list_erase_all_rec
                            (__eo_list_setof_rec y) head) z) =
                      Term.Boolean false :=
                  eo_is_neg_list_find_erase_all_rec_of_ne
                    hSetTailVar hz hHeadNe hZHead hTailFind
                have hConsFind :
                    __eo_is_neg
                        (__eo_list_find Term.__eo_List_cons
                          (Term.Apply (Term.Apply Term.__eo_List_cons head)
                            (__eo_list_erase_all_rec
                              (__eo_list_setof_rec y) head)) z) =
                      Term.Boolean false :=
                  eo_is_neg_list_find_cons_of_tail head z
                    (__eo_list_erase_all_rec (__eo_list_setof_rec y) head)
                    hHeadNe hz hEraseVar hTailFindErase
                simpa [head, __eo_list_setof_rec, __eo_mk_apply,
                  hEraseNe] using hConsFind
  | case3 nil _hNilNe hNotApplyApply =>
      cases nil with
      | __eo_List_nil =>
          exact False.elim hMem
      | Apply f a =>
          cases f with
          | Apply g x =>
              exact False.elim (hNotApplyApply g x a rfl)
          | _ =>
              exact False.elim hVarList
      | _ =>
          exact False.elim hVarList

private theorem eo_is_neg_list_find_setof_of_var_list_mem
    {xs z : Term} (hVarList : eo_var_list xs)
    (hz : z ≠ Term.Stuck) (hMem : eo_var_list_mem z xs) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons xs) z) =
      Term.Boolean false := by
  have hList :
      __eo_is_list Term.__eo_List_cons xs = Term.Boolean true :=
    eo_var_list_is_list hVarList
  have hFind :=
    eo_is_neg_list_find_setof_rec_of_var_list_mem
      hVarList hz hMem
  simpa [__eo_list_setof, hList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using hFind

private theorem eo_is_neg_list_find_setof_cons_head
    (s : native_String) (T xs : Term)
    (hTailVar : eo_var_list xs) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) xs))
          (Term.Var (Term.String s) T)) =
      Term.Boolean false := by
  have hWholeList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs) =
        Term.Boolean true :=
    eo_is_list_cons_of_tail_list (Term.Var (Term.String s) T) xs
      (eo_var_list_is_list hTailVar)
  have hWholeVar :
      eo_var_list
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) xs) := hTailVar
  have hSetList :
      __eo_is_list Term.__eo_List_cons
          (__eo_list_setof_rec
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) xs)) =
        Term.Boolean true :=
    eo_list_setof_rec_is_list_of_var_list hWholeVar
  have hSetTailList :
      __eo_is_list Term.__eo_List_cons
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs)
            (Term.Var (Term.String s) T)) =
        Term.Boolean true :=
    eo_list_erase_all_rec_is_list_of_var_list
      (eo_var_list_setof_rec hTailVar) (term_var_string_ne_stuck s T)
  have hSetTailNe :
      __eo_list_erase_all_rec (__eo_list_setof_rec xs)
          (Term.Var (Term.String s) T) ≠ Term.Stuck :=
    term_ne_stuck_of_eo_is_list_true hSetTailList
  have hConsSetList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply
            (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
            (__eo_list_erase_all_rec (__eo_list_setof_rec xs)
              (Term.Var (Term.String s) T))) =
        Term.Boolean true := by
    simpa [__eo_list_setof_rec, __eo_mk_apply, hSetTailNe] using hSetList
  rw [__eo_list_setof]
  simp [hWholeList, __eo_requires, native_ite, native_teq, native_not]
  rw [__eo_list_setof_rec]
  simp [__eo_mk_apply, hSetTailNe, __eo_list_find, hConsSetList,
    hSetTailList, __eo_requires, __eo_list_find_rec, __eo_eq, __eo_ite,
    __eo_is_neg, native_ite, native_teq, native_not, SmtEval.native_not]
  native_decide

private theorem eo_to_smt_type_eq_self_of_wf
    {T U : Term}
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTy : __eo_to_smt_type U = __eo_to_smt_type T) :
    U = T := by
  have hByRec :
      ∀ {A : SmtType},
        __eo_to_smt_type T = A ->
          __smtx_type_wf_rec A native_reflist_nil = true ->
            U = T := by
    intro A hTA hRec
    have hU : __eo_to_smt_type U = A := hTy.trans hTA
    have hField :
        TranslationProofs.smtx_type_field_wf_rec A native_reflist_nil :=
      TranslationProofs.smtx_type_field_wf_rec_of_type_wf_rec hRec
    exact TranslationProofs.eo_to_smt_type_injective_of_field_wf_rec
      (T := U) (U := T) (A := A) hU hTA hField
  cases hA : __eo_to_smt_type T with
  | RegLan =>
      have hU : U = Term.UOp UserOp.RegLan :=
        TranslationProofs.eo_to_smt_type_eq_reglan (by
          simpa [hA] using hTy)
      have hT : T = Term.UOp UserOp.RegLan :=
        TranslationProofs.eo_to_smt_type_eq_reglan hA
      rw [hU, hT]
  | FunType A B =>
      have hWF' : __smtx_type_wf (SmtType.FunType A B) = true := by
        simpa [hA] using hWF
      rcases TranslationProofs.fun_type_wf_rec_components_of_wf hWF' with
        ⟨hARec, hBRec⟩
      have hAField :
          TranslationProofs.smtx_type_field_wf_rec A native_reflist_nil :=
        TranslationProofs.smtx_type_field_wf_rec_of_type_wf_rec hARec
      have hBField :
          TranslationProofs.smtx_type_field_wf_rec B native_reflist_nil :=
        TranslationProofs.smtx_type_field_wf_rec_of_type_wf_rec hBRec
      have hUFun : __eo_to_smt_type U = SmtType.FunType A B := by
        simpa [hA] using hTy
      rcases TranslationProofs.eo_to_smt_type_eq_fun hA with
        ⟨T1, T2, hTShape, hT1, hT2⟩
      rcases TranslationProofs.eo_to_smt_type_eq_fun hUFun with
        ⟨U1, U2, hUShape, hU1, hU2⟩
      subst T
      subst U
      have h1 : U1 = T1 :=
        TranslationProofs.eo_to_smt_type_injective_of_field_wf_rec
          (T := U1) (U := T1) (A := A)
          hU1 hT1 hAField
      have h2 : U2 = T2 :=
        TranslationProofs.eo_to_smt_type_injective_of_field_wf_rec
          (T := U2) (U := T2) (A := B)
          hU2 hT2 hBField
      subst U1
      subst U2
      rfl
  | None =>
      simp [hA, __smtx_type_wf, __smtx_type_wf_component,
        __smtx_type_wf_rec, native_inhabited_type, native_and] at hWF
  | TypeRef s =>
      simp [hA, __smtx_type_wf, __smtx_type_wf_component,
        __smtx_type_wf_rec, native_inhabited_type, native_and] at hWF
  | DtcAppType A B =>
      simp [hA, __smtx_type_wf, __smtx_type_wf_component,
        __smtx_type_wf_rec, native_inhabited_type, native_and] at hWF
  | Bool =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | Int =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | Real =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | BitVec w =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | Char =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | Datatype s d =>
      have hParts :
          (__smtx_typeof_value
                (__smtx_type_default (SmtType.Datatype s d)) =
              SmtType.Datatype s d ∧
            __smtx_value_canonical_bool
                (__smtx_type_default (SmtType.Datatype s d)) =
              true) ∧
            __smtx_type_wf_rec (SmtType.Datatype s d)
                native_reflist_nil =
              true := by
        simpa [hA, __smtx_type_wf, __smtx_type_wf_component,
          native_inhabited_type, native_and] using hWF
      exact hByRec hA hParts.2
  | USort i =>
      exact hByRec hA (by simp [__smtx_type_wf_rec])
  | Seq A =>
      have hParts :
          (__smtx_typeof_value (__smtx_type_default (SmtType.Seq A)) =
              SmtType.Seq A ∧
            __smtx_value_canonical_bool
                (__smtx_type_default (SmtType.Seq A)) =
              true) ∧
            __smtx_type_wf_rec (SmtType.Seq A) native_reflist_nil =
              true := by
        simpa [hA, __smtx_type_wf, __smtx_type_wf_component,
          native_inhabited_type, native_and] using hWF
      exact hByRec hA hParts.2
  | Map A B =>
      have hParts :
          (__smtx_typeof_value (__smtx_type_default (SmtType.Map A B)) =
              SmtType.Map A B ∧
            __smtx_value_canonical_bool
                (__smtx_type_default (SmtType.Map A B)) =
              true) ∧
            __smtx_type_wf_rec (SmtType.Map A B) native_reflist_nil =
              true := by
        simpa [hA, __smtx_type_wf, __smtx_type_wf_component,
          native_inhabited_type, native_and] using hWF
      exact hByRec hA hParts.2
  | Set A =>
      have hParts :
          (__smtx_typeof_value (__smtx_type_default (SmtType.Set A)) =
              SmtType.Set A ∧
            __smtx_value_canonical_bool
                (__smtx_type_default (SmtType.Set A)) =
              true) ∧
            __smtx_type_wf_rec (SmtType.Set A) native_reflist_nil =
              true := by
        simpa [hA, __smtx_type_wf, __smtx_type_wf_component,
          native_inhabited_type, native_and] using hWF
      exact hByRec hA hParts.2

private theorem eo_is_neg_list_find_setof_cons_head_same_smt_type
    (s : native_String) (T T' xs : Term)
    (hTailVar : eo_var_list xs)
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTy : __eo_to_smt_type T' = __eo_to_smt_type T) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) xs))
          (Term.Var (Term.String s) T')) =
      Term.Boolean false := by
  have hT' : T' = T := eo_to_smt_type_eq_self_of_wf hWF hTy
  subst T'
  exact eo_is_neg_list_find_setof_cons_head s T xs hTailVar

private theorem scannerModelRel_push_nil_of_xs_hit
    (xs : Term) (M : SmtModel) (s : native_String) (T : Term)
    (v : SmtValue)
    (hHit :
      ∀ T',
        __eo_to_smt_type T' = __eo_to_smt_type T ->
          __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T')) = Term.Boolean false) :
    scannerModelRel xs Term.__eo_List_nil M
      (native_model_push M s (__eo_to_smt_type T) v) := by
  refine ⟨?_, ?_⟩
  · exact
      ⟨by
        intro s' U
        simp [native_model_lookup, native_model_key, native_model_push],
      by
        intro fid U V
        simp [native_model_fun_lookup, native_model_key, native_model_push]⟩
  · intro s' T' hAllowed
    by_cases hKey :
        ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
          SmtModelKey) =
          { isVar := true, name := s, ty := __eo_to_smt_type T }
    · have hAllowedSame :
          __eo_ite
              (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s') T')))
              (Term.Boolean false)
              (__eo_is_neg
                (__eo_list_find Term.__eo_List_cons Term.__eo_List_nil
                  (Term.Var (Term.String s') T'))) =
            Term.Boolean false := by
        exact hAllowed
      have hName : s' = s := congrArg SmtModelKey.name hKey
      have hTy : __eo_to_smt_type T' = __eo_to_smt_type T :=
        congrArg SmtModelKey.ty hKey
      subst s'
      rw [hHit T' hTy, eo_is_neg_list_find_nil_var] at hAllowedSame
      simp [__eo_ite, native_ite, native_teq] at hAllowedSame
    · simpa [native_model_var_lookup, native_model_push, hKey]

private theorem scannerModelRel_push_of_xs_hit_bvs_miss
    (xs bvs : Term) (M : SmtModel) (s : native_String) (T : Term)
    (v : SmtValue)
    (hHit :
      ∀ T',
        __eo_to_smt_type T' = __eo_to_smt_type T ->
          __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T')) = Term.Boolean false)
    (hMiss :
      ∀ T',
        __eo_to_smt_type T' = __eo_to_smt_type T ->
          __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs
            (Term.Var (Term.String s) T')) = Term.Boolean true) :
    scannerModelRel xs bvs M
      (native_model_push M s (__eo_to_smt_type T) v) := by
  refine ⟨?_, ?_⟩
  · exact
      ⟨by
        intro s' U
        simp [native_model_lookup, native_model_key, native_model_push],
      by
        intro fid U V
        simp [native_model_fun_lookup, native_model_key, native_model_push]⟩
  · intro s' T' hAllowed
    by_cases hKey :
        ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
          SmtModelKey) =
          { isVar := true, name := s, ty := __eo_to_smt_type T }
    · have hName : s' = s := congrArg SmtModelKey.name hKey
      have hTy : __eo_to_smt_type T' = __eo_to_smt_type T :=
        congrArg SmtModelKey.ty hKey
      subst s'
      rw [hHit T' hTy, hMiss T' hTy] at hAllowed
      simp [__eo_ite, native_ite, native_teq] at hAllowed
    · simpa [native_model_var_lookup, native_model_push, hKey]

private theorem scannerModelRel_push_nil_of_setof_cons_head
    (M : SmtModel) (s : native_String) (T xs : Term) (v : SmtValue)
    (hTailVar : eo_var_list xs)
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true) :
    scannerModelRel
      (__eo_list_setof Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) xs))
      Term.__eo_List_nil M
      (native_model_push M s (__eo_to_smt_type T) v) := by
  exact scannerModelRel_push_nil_of_xs_hit
    (__eo_list_setof Term.__eo_List_cons
      (Term.Apply (Term.Apply Term.__eo_List_cons
        (Term.Var (Term.String s) T)) xs))
    M s T v
    (fun T' hTy =>
      eo_is_neg_list_find_setof_cons_head_same_smt_type
        s T T' xs hTailVar hWF hTy)

private theorem scannerModelRel_push_nil_of_setof_mem
    (M : SmtModel) (s : native_String) (T xs : Term) (v : SmtValue)
    (hVarList : eo_var_list xs)
    (hMem : eo_var_list_mem (Term.Var (Term.String s) T) xs)
    (hWF : __smtx_type_wf (__eo_to_smt_type T) = true) :
    scannerModelRel
      (__eo_list_setof Term.__eo_List_cons xs)
      Term.__eo_List_nil M
      (native_model_push M s (__eo_to_smt_type T) v) := by
  exact scannerModelRel_push_nil_of_xs_hit
    (__eo_list_setof Term.__eo_List_cons xs) M s T v
    (fun T' hTy => by
      have hT' : T' = T := eo_to_smt_type_eq_self_of_wf hWF hTy
      subst T'
      exact eo_is_neg_list_find_setof_of_var_list_mem
        hVarList (term_var_string_ne_stuck s T) hMem)

private theorem scannerModelRel_push_same_cons_var
    (xs bvs : Term) (M N : SmtModel)
    (s : native_String) (T : Term) (v : SmtValue)
    (hBvsVar : eo_var_list bvs)
    (hRel : scannerModelRel xs bvs M N) :
    scannerModelRel xs
      (Term.Apply (Term.Apply Term.__eo_List_cons
        (Term.Var (Term.String s) T)) bvs)
      (native_model_push M s (__eo_to_smt_type T) v)
      (native_model_push N s (__eo_to_smt_type T) v) := by
  refine ⟨model_agrees_on_globals_push₂ hRel.globals, ?_⟩
  intro s' T' hAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
        SmtModelKey) =
        { isVar := true, name := s, ty := __eo_to_smt_type T }
  · simpa [native_model_var_lookup, native_model_push, hKey]
  · have hOldAllowed :
        __eo_ite
            (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s') T')))
            (Term.Boolean false)
            (__eo_is_neg (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s') T'))) =
          Term.Boolean false := by
      rcases eo_ite_false_branch_eq_false_cases
          (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s') T')))
          (__eo_is_neg
            (__eo_list_find Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) bvs)
              (Term.Var (Term.String s') T'))) hAllowed with
        hXsMiss | ⟨hXsHit, hBvsNewHit⟩
      · simp [__eo_ite, hXsMiss, native_ite, native_teq]
      · have hTermNe :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s') T' := by
          intro hTerm
          cases hTerm
          exact hKey rfl
        have hBvsHit :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s') T')) =
              Term.Boolean false :=
          eo_is_neg_list_find_tail_of_cons_var_ne
            s s' T T' bvs hBvsVar hTermNe hBvsNewHit
        simp [__eo_ite, hXsHit, hBvsHit, native_ite, native_teq]
    simpa [native_model_var_lookup, native_model_push, hKey]
      using hRel.vars_eq s' T' hOldAllowed

private theorem body_constant_on_eo_binders_of_scanner_eval_aux
    (body : SmtTerm) (xs bvs binders : Term) {vars : List SmtVarKey}
    (hBinders : EoSmtVarEnv binders vars)
    (hHit :
      ∀ (s : native_String) (T : Term),
        eo_var_list_mem (Term.Var (Term.String s) T) binders ->
          ∀ T',
            __eo_to_smt_type T' = __eo_to_smt_type T ->
              __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) T')) = Term.Boolean false)
    (hMiss :
      ∀ (s : native_String) (T : Term),
        eo_var_list_mem (Term.Var (Term.String s) T) binders ->
          ∀ T',
            __eo_to_smt_type T' = __eo_to_smt_type T ->
              __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs
                (Term.Var (Term.String s) T')) = Term.Boolean true)
    (hEval :
      ∀ M N : SmtModel,
        scannerModelRel xs bvs M N ->
          __smtx_model_eval M body =
            __smtx_model_eval N body) :
    body_constant_on_eo_binders body binders := by
  induction hBinders with
  | nil =>
      trivial
  | cons hTail ih =>
      rename_i s T tail varsTail
      have hHeadMem :
          eo_var_list_mem (Term.Var (Term.String s) T)
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) tail) := by
        exact Or.inl rfl
      constructor
      · intro M v _hvTy _hvCan
        exact
          (hEval M (native_model_push M s (__eo_to_smt_type T) v)
            (scannerModelRel_push_of_xs_hit_bvs_miss
              xs bvs M s T v
              (hHit s T hHeadMem)
              (hMiss s T hHeadMem))).symm
      · apply ih
        · intro s' T' hMemTail
          exact hHit s' T' (Or.inr hMemTail)
        · intro s' T' hMemTail
          exact hMiss s' T' (Or.inr hMemTail)

private theorem body_constant_on_eo_binders_of_scan_setof_aux
    (F orig binders : Term) {vars : List SmtVarKey}
    (hOrigVar : eo_var_list orig)
    (hBinders : EoSmtVarEnv binders vars)
    (hMemOrig :
      ∀ (s : native_String) (T : Term),
        eo_var_list_mem (Term.Var (Term.String s) T) binders ->
          eo_var_list_mem (Term.Var (Term.String s) T) orig)
    (hWf :
      ∀ (s : native_String) (T : Term),
        eo_var_list_mem (Term.Var (Term.String s) T) binders ->
          __smtx_type_wf (__eo_to_smt_type T) = true)
    (hEval :
      ∀ M N : SmtModel,
        scannerModelRel (__eo_list_setof Term.__eo_List_cons orig)
          Term.__eo_List_nil M N ->
          __smtx_model_eval M (__eo_to_smt F) =
            __smtx_model_eval N (__eo_to_smt F)) :
    body_constant_on_eo_binders (__eo_to_smt F) binders := by
  induction hBinders with
  | nil =>
      trivial
  | cons hTail ih =>
      rename_i s T tail varsTail
      have hHeadMem :
          eo_var_list_mem (Term.Var (Term.String s) T)
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) tail) := by
        exact Or.inl rfl
      constructor
      · intro M v _hvTy _hvCan
        exact
          (hEval M (native_model_push M s (__eo_to_smt_type T) v)
            (scannerModelRel_push_nil_of_setof_mem
              M s T orig v hOrigVar (hMemOrig s T hHeadMem)
              (hWf s T hHeadMem))).symm
      · apply ih
        · intro s' T' hMemTail
          exact hMemOrig s' T' (Or.inr hMemTail)
        · intro s' T' hMemTail
          exact hWf s' T' (Or.inr hMemTail)

private theorem smtx_model_eval_none_eq (M : SmtModel) :
    __smtx_model_eval M SmtTerm.None = SmtValue.NotValue := by
  simp [__smtx_model_eval]

private theorem smtx_model_eval_var_eq
    (M : SmtModel) (s : native_String) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.Var s T) =
      native_model_var_lookup M s T := by
  simp [__smtx_model_eval]

private theorem contains_atomic_qterm_body_of_false
    {Q y F xs bvs : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv y vars)
    (hy : y ≠ Term.__eo_List_nil)
    (hQNe : Q ≠ Term.Stuck)
    (hScan :
      __contains_atomic_term_list_free_rec (qterm Q y F) xs bvs =
        Term.Boolean false) :
    __contains_atomic_term_list_free_rec F xs
        (__eo_list_concat Term.__eo_List_cons y bvs) =
      Term.Boolean false := by
  cases hEnv with
  | nil =>
      exact False.elim (hy rfl)
  | cons hTail =>
      rename_i s T tail varsTail
      have hXs : xs ≠ Term.Stuck := by
        intro h
        subst xs
        cases bvs <;> simp [qterm, __contains_atomic_term_list_free_rec] at hScan
      have hBvs : bvs ≠ Term.Stuck := by
        intro h
        subst bvs
        cases xs <;> simp [qterm, __contains_atomic_term_list_free_rec] at hScan
      simp only [qterm] at hScan
      rw [Eo.__contains_atomic_term_list_free_rec.eq_4
        xs bvs Q (Term.Var (Term.String s) T) tail F hXs hBvs] at hScan
      exact hScan

private theorem smtx_model_eval_var_eq_of_scannerModelRel
    (xs bvs : Term) (M N : SmtModel)
    (hRel : scannerModelRel xs bvs M N)
    (s : native_String) (T : Term)
    (hScan :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) xs bvs =
        Term.Boolean false) :
    __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
      __smtx_model_eval N (__eo_to_smt (Term.Var (Term.String s) T)) := by
  rw [TranslationProofs.eo_to_smt_var, smtx_model_eval_var_eq,
    smtx_model_eval_var_eq]
  have hXs : xs ≠ Term.Stuck := by
    intro h
    subst xs
    cases bvs <;> simp [__contains_atomic_term_list_free_rec] at hScan
  have hBvs : bvs ≠ Term.Stuck := by
    intro h
    subst bvs
    cases xs <;> simp [__contains_atomic_term_list_free_rec] at hScan
  rw [Eo.__contains_atomic_term_list_free_rec.eq_6 xs bvs
    (Term.String s) T hXs hBvs] at hScan
  exact hRel.vars_eq s T hScan

private theorem smtx_model_eval_uconst_eq
    (M : SmtModel) (s : native_String) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.UConst s T) =
      native_model_lookup M s T := by
  simp [__smtx_model_eval]

private theorem smtx_model_eval_uconst_eq_of_scannerModelRel
    (xs bvs : Term) (M N : SmtModel)
    (hRel : scannerModelRel xs bvs M N)
    (i : native_Nat) (T : Term) :
    __smtx_model_eval M (__eo_to_smt (Term.UConst i T)) =
      __smtx_model_eval N (__eo_to_smt (Term.UConst i T)) := by
  rw [TranslationProofs.eo_to_smt_uconst, smtx_model_eval_uconst_eq,
    smtx_model_eval_uconst_eq]
  exact hRel.globals.1 (native_uconst_id i) (__eo_to_smt_type T)

private theorem smtx_model_eval_eq_of_closed_nil_scannerModelRel
    {xs bvs : Term} {M N : SmtModel} {t : SmtTerm}
    (hRel : scannerModelRel xs bvs M N)
    (hClosed : SmtTermClosedIn [] t) :
    __smtx_model_eval M t = __smtx_model_eval N t := by
  exact smt_model_eval_eq_of_closedIn t [] M N hClosed
    (model_agrees_on_env_nil_of_globals hRel.globals)

private theorem smtTermClosedIn_eo_to_smt_uop2_at_bv_nil
    (a b : Term) :
    SmtTermClosedIn []
      (__eo_to_smt (Term.UOp2 UserOp2._at_bv a b)) := by
  change SmtTermClosedIn []
    (__eo_to_smt__at_bv (__eo_to_smt a) (__eo_to_smt b))
  cases __eo_to_smt a <;> cases __eo_to_smt b <;> try trivial
  case Numeral.Numeral n w =>
    change SmtTermClosedIn []
      (native_ite (native_zleq 0 w)
        (SmtTerm.Binary w (native_mod_total n (native_int_pow2 w)))
        SmtTerm.None)
    cases native_zleq 0 w <;> trivial

private theorem smtTermClosedIn_eo_to_smt_uop3_witness_string_length_nil
    (a b c : Term) :
    SmtTermClosedIn []
      (__eo_to_smt (Term.UOp3 UserOp3._at_witness_string_length a b c)) := by
  change SmtTermClosedIn []
    (native_ite (__eo_to_smt_nat_is_valid b)
      (native_ite (__eo_to_smt_nat_is_valid c)
        (SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type a)
          (SmtTerm.eq
            (SmtTerm.str_len
              (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type a)))
            (__eo_to_smt b))
          native_nat_zero)
        SmtTerm.None)
      SmtTerm.None)
  cases b <;> try (change SmtTermClosedIn [] SmtTerm.None; trivial)
  case Numeral n =>
    change SmtTermClosedIn []
      (native_ite (native_zleq 0 n)
        (native_ite (__eo_to_smt_nat_is_valid c)
          (SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type a)
            (SmtTerm.eq
              (SmtTerm.str_len
                (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type a)))
              (SmtTerm.Numeral n))
            native_nat_zero)
          SmtTerm.None)
        SmtTerm.None)
    cases native_zleq 0 n
    · trivial
    · cases c <;> try (change SmtTermClosedIn [] SmtTerm.None; trivial)
      case Numeral m =>
        change SmtTermClosedIn []
          (native_ite (native_zleq 0 m)
            (SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type a)
              (SmtTerm.eq
                (SmtTerm.str_len
                  (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type a)))
                (SmtTerm.Numeral n))
              native_nat_zero)
            SmtTerm.None)
        cases native_zleq 0 m
        · change SmtTermClosedIn [] SmtTerm.None
          trivial
        · change SmtTermClosedIn []
            (SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type a)
              (SmtTerm.eq
                (SmtTerm.str_len
                  (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type a)))
                (SmtTerm.Numeral n))
              native_nat_zero)
          simp [SmtTermClosedIn]

private theorem contains_atomic_term_list_free_rec_vars_ne_stuck_of_false
    {t xs bvs : Term} :
    __contains_atomic_term_list_free_rec t xs bvs = Term.Boolean false ->
    xs ≠ Term.Stuck := by
  intro h hxs
  subst xs
  cases t <;> cases bvs <;>
    simp [__contains_atomic_term_list_free_rec] at h

private theorem smtx_model_eval_eq_of_contains_atomic_false
    (t xs bvs : Term) :
    (∀ M N : SmtModel,
      scannerModelRel xs bvs M N ->
      __contains_atomic_term_list_free_rec t xs bvs =
        Term.Boolean false ->
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_model_eval M (__eo_to_smt t) =
        __smtx_model_eval N (__eo_to_smt t)) := by
  induction t, xs, bvs using Eo.__contains_atomic_term_list_free_rec.induct with
  | case1 xs bvs =>
      intro M N hRel hScan hNN
      simp [__contains_atomic_term_list_free_rec] at hScan
  | case2 t bvs ht =>
      intro M N hRel hScan hNN
      simp [__contains_atomic_term_list_free_rec] at hScan
  | case3 t xs ht hxs =>
      intro M N hRel hScan hNN
      simp [__contains_atomic_term_list_free_rec] at hScan
  | case4 q x ys a xs bvs hXs hBvs ih =>
      intro M N hRel hScan hNN
      sorry
  | case5 f a xs bvs hXs hBvs hNotQuant ihF ihA =>
      intro M N hRel hScan hNN
      have hScan' :
          __eo_ite (__contains_atomic_term_list_free_rec f xs bvs)
              (Term.Boolean true)
              (__contains_atomic_term_list_free_rec a xs bvs) =
            Term.Boolean false := by
        simpa [__contains_atomic_term_list_free_rec] using hScan
      rcases eo_ite_true_branch_eq_false_cases
          (__contains_atomic_term_list_free_rec f xs bvs)
          (__contains_atomic_term_list_free_rec a xs bvs) hScan' with
        ⟨hFScan, hAScan⟩
      sorry
  | case6 name T xs bvs hXs hBvs =>
      intro M N hRel hScan hNN
      cases name with
      | String s =>
          exact smtx_model_eval_var_eq_of_scannerModelRel
            xs bvs M N hRel s T hScan
      | _ =>
          exfalso
          exact hNN TranslationProofs.smtx_typeof_none
  | case7 F n xs bvs hXs hBvs ih =>
      intro M N hRel hScan hNN
      sorry
  | case8 s r n xs bvs hXs hBvs ihS ihR =>
      intro M N hRel hScan hNN
      have hScan' :
          __eo_ite (__contains_atomic_term_list_free_rec s xs bvs)
              (Term.Boolean true)
              (__contains_atomic_term_list_free_rec r xs bvs) =
            Term.Boolean false := by
        simpa [__contains_atomic_term_list_free_rec] using hScan
      rcases eo_ite_true_branch_eq_false_cases
          (__contains_atomic_term_list_free_rec s xs bvs)
          (__contains_atomic_term_list_free_rec r xs bvs) hScan' with
        ⟨hSScan, hRScan⟩
      sorry
  | case9 x xs bvs hx hXs hBvs hNotQuant hNotApp hNotVar
      hNotSkolem hNotReUnfold =>
      intro M N hRel hScan hNN
      cases x with
      | UOp op =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_uop [] op)
      | UOp1 op a =>
          cases op
          case seq_empty =>
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (smtTermClosedIn_eo_to_smt_seq_empty [] a)
          case set_empty =>
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (smtTermClosedIn_eo_to_smt_set_empty [] a)
          all_goals
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | UOp2 op a b =>
          cases op
          case _at_bv =>
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (smtTermClosedIn_eo_to_smt_uop2_at_bv_nil a b)
          case _at_quantifiers_skolemize =>
            exfalso
            exact hNotSkolem a b rfl
          all_goals
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | UOp3 op a b c =>
          cases op
          case _at_re_unfold_pos_component =>
            exfalso
            exact hNotReUnfold a b c rfl
          case _at_witness_string_length =>
            exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
              (smtTermClosedIn_eo_to_smt_uop3_witness_string_length_nil
                a b c)
      | __eo_List =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | __eo_List_nil =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | __eo_List_cons =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | Bool =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | Boolean b =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_boolean [] b)
      | Numeral n =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_numeral [] n)
      | Rational r =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_rational [] r)
      | String s =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_string [] s)
      | Binary w n =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_binary [] w n)
      | «Type» =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | Stuck =>
          exact False.elim (hx rfl)
      | Apply f a =>
          exact False.elim (hNotApp f a rfl)
      | FunType =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | Var name T =>
          exact False.elim (hNotVar name T rfl)
      | DatatypeType s d =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | DatatypeTypeRef s =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | DtcAppType A B =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | DtCons s d i =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_dtcons [] s d i)
      | DtSel s d i j =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_dtsel [] s d i j)
      | USort i =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (by change SmtTermClosedIn [] SmtTerm.None; trivial)
      | UConst i T =>
          exact smtx_model_eval_eq_of_closed_nil_scannerModelRel hRel
            (smtTermClosedIn_eo_to_smt_uconst [] i T)

private theorem get_unused_vars_ne_stuck_of_contains_false
    {Q x F G : Term} :
    __contains_atomic_term_list_free_rec G
        (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
      Term.Boolean false ->
    __get_unused_vars (qterm Q x F) G ≠ Term.Stuck :=
  contains_atomic_term_list_free_rec_vars_ne_stuck_of_false

private theorem get_unused_vars_fallback_shape_of_not_stuck
    (Q x F G : Term) :
    __eo_l_1___get_unused_vars (qterm Q x F) G ≠ Term.Stuck ->
    G = F ∧
      __eo_l_1___get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x := by
  intro hGet
  by_cases hGStuck : G = Term.Stuck
  · subst G
    simp [__eo_l_1___get_unused_vars] at hGet
  · have hReq :
        __eo_requires (__eo_eq F G) (Term.Boolean true)
            (__eo_list_setof Term.__eo_List_cons x) ≠
          Term.Stuck := by
      cases G <;>
        simp_all [qterm, __eo_l_1___get_unused_vars]
    have hG : G = F :=
      RuleProofs.eq_of_requires_eq_true_not_stuck F G
        (__eo_list_setof Term.__eo_List_cons x) hReq
    subst G
    constructor
    · rfl
    · simp [qterm, __eo_l_1___get_unused_vars, __eo_eq, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]

private theorem get_unused_vars_shape_of_not_stuck
    (Q x F G : Term) :
    __get_unused_vars (qterm Q x F) G ≠ Term.Stuck ->
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
  intro hGet
  let G0 := G
  cases G with
  | Apply g F2 =>
      let G1 := Term.Apply g F2
      cases g with
      | Apply Q2 y =>
          let sx := __eo_list_setof Term.__eo_List_cons x
          let guard := __eo_and (__eo_eq Q Q2) (__eo_eq F F2)
          let branch :=
            __eo_requires (__eo_list_minclude Term.__eo_List_cons sx y)
              (Term.Boolean true)
              (__eo_list_diff Term.__eo_List_cons sx y)
          by_cases hGuardTrue : guard = Term.Boolean true
          · have hGetEqBranch :
                __get_unused_vars (qterm Q x F) ((Q2.Apply y).Apply F2) =
                  branch := by
              simp [__get_unused_vars, qterm, sx, guard, branch,
                hGuardTrue, __eo_ite, native_ite, native_teq]
            have hBranchNe : branch ≠ Term.Stuck := by
              intro hBranch
              exact hGet (by rw [hGetEqBranch, hBranch])
            have hIncl :
                __eo_list_minclude Term.__eo_List_cons sx y =
                  Term.Boolean true :=
              eq_of_requires_ne_stuck hBranchNe
            rcases eo_and_eq_true_cases_local
                (__eo_eq Q Q2) (__eo_eq F F2) hGuardTrue with
              ⟨hQ, hF⟩
            have hQ2 : Q2 = Q :=
              RuleProofs.eq_of_eo_eq_true Q Q2 hQ
            have hF2 : F2 = F :=
              RuleProofs.eq_of_eo_eq_true F F2 hF
            subst Q2
            subst F2
            right
            refine ⟨y, rfl, ?_, ?_⟩
            · simpa [sx] using hIncl
            · rw [hGetEqBranch]
              simp [branch, sx, hIncl, __eo_requires, native_ite, native_teq,
                native_not, SmtEval.native_not]
          · by_cases hGuardFalse : guard = Term.Boolean false
            · have hGetEqFallback :
                  __get_unused_vars (qterm Q x F) ((Q2.Apply y).Apply F2) =
                    __eo_l_1___get_unused_vars (qterm Q x F)
                      ((Q2.Apply y).Apply F2) := by
                simp [__get_unused_vars, qterm, guard,
                  hGuardFalse, __eo_ite, native_ite, native_teq]
              have hFallbackNe :
                  __eo_l_1___get_unused_vars (qterm Q x F)
                      ((Q2.Apply y).Apply F2) ≠
                    Term.Stuck := by
                intro hFallback
                exact hGet (by rw [hGetEqFallback, hFallback])
              rcases get_unused_vars_fallback_shape_of_not_stuck
                  Q x F ((Q2.Apply y).Apply F2) hFallbackNe with
                ⟨hGF, hFallbackEq⟩
              left
              refine ⟨hGF, ?_⟩
              rw [hGetEqFallback]
              exact hFallbackEq
            · have hGetStuck :
                  __get_unused_vars (qterm Q x F) ((Q2.Apply y).Apply F2) =
                    Term.Stuck := by
                simp [__get_unused_vars, qterm, guard,
                  hGuardTrue, hGuardFalse, __eo_ite, native_ite, native_teq]
              exact False.elim (hGet hGetStuck)
      | _ =>
          have hFallbackNe :
              __eo_l_1___get_unused_vars (qterm Q x F) G1 ≠
                Term.Stuck := by
            simpa [G1, __get_unused_vars, qterm] using hGet
          rcases get_unused_vars_fallback_shape_of_not_stuck
              Q x F G1 hFallbackNe with
            ⟨hGF, hFallbackEq⟩
          left
          refine ⟨by simpa [G1] using hGF, ?_⟩
          simpa [G1, __get_unused_vars, qterm] using hFallbackEq
  | _ =>
      have hFallbackNe :
          __eo_l_1___get_unused_vars (qterm Q x F) G0 ≠ Term.Stuck := by
        simpa [G0, __get_unused_vars, qterm] using hGet
      rcases get_unused_vars_fallback_shape_of_not_stuck Q x F G0 hFallbackNe with
        ⟨hGF, hFallbackEq⟩
      left
      refine ⟨by simpa [G0] using hGF, ?_⟩
      simpa [G0, __get_unused_vars, qterm] using hFallbackEq

private theorem quant_unused_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = qeq (qterm Q x F) G ∧
      (Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists) ∧
      __contains_atomic_term_list_free_rec G
        (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
          Term.Boolean false ∧
      __eo_prog_quant_unused_vars x1 = qeq (qterm Q x F) G := by
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
                          let noFree :=
                            __contains_atomic_term_list_free_rec G
                              (__get_unused_vars v0 G) Term.__eo_List_nil
                          let inner :=
                            __eo_requires noFree (Term.Boolean false)
                              (qeq v0 G)
                          have hReq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner ≠ Term.Stuck := by
                            simpa [qeq, qterm, v0, noFree, inner,
                              __eo_prog_quant_unused_vars] using hProg
                          have hGuard :
                              __eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                  (__eo_eq Q (Term.UOp UserOp.exists)) =
                                Term.Boolean true :=
                            eq_of_requires_ne_stuck hReq
                          have hInnerNe : inner ≠ Term.Stuck :=
                            body_ne_stuck_of_requires_ne_stuck hReq
                          have hNoFree :
                              noFree = Term.Boolean false :=
                            eq_of_requires_ne_stuck hInnerNe
                          rcases eo_or_eq_true_cases_local
                              (__eo_eq Q (Term.UOp UserOp.forall))
                              (__eo_eq Q (Term.UOp UserOp.exists)) hGuard with
                            hForall | hExists
                          · have hQ : Q = Term.UOp UserOp.forall :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.forall) hForall).symm
                            subst Q
                            refine ⟨Term.UOp UserOp.forall, x, F, G, rfl,
                              Or.inl rfl, ?_, ?_⟩
                            · simpa [v0, qterm, noFree] using hNoFree
                            · change __eo_prog_quant_unused_vars
                                (qeq (qterm (Term.UOp UserOp.forall) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.forall) x F) G
                              have hGuard' :
                                  __eo_or
                                      (__eo_eq (Term.UOp UserOp.forall)
                                        (Term.UOp UserOp.forall))
                                      (__eo_eq (Term.UOp UserOp.forall)
                                        (Term.UOp UserOp.exists)) =
                                    Term.Boolean true := by
                                simp [__eo_or, __eo_eq, native_or, native_teq]
                              have hNoFree' :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (qterm (Term.UOp UserOp.forall) x F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [v0, qterm, noFree] using hNoFree
                              have hNoFreeRaw :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (((Term.UOp UserOp.forall).Apply x).Apply F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [qterm] using hNoFree'
                              simp [qeq, qterm, __eo_prog_quant_unused_vars,
                                hGuard', hNoFreeRaw, __eo_requires, native_ite,
                                native_teq, native_not, SmtEval.native_not]
                          · have hQ : Q = Term.UOp UserOp.exists :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.exists) hExists).symm
                            subst Q
                            refine ⟨Term.UOp UserOp.exists, x, F, G, rfl,
                              Or.inr rfl, ?_, ?_⟩
                            · simpa [v0, qterm, noFree] using hNoFree
                            · change __eo_prog_quant_unused_vars
                                (qeq (qterm (Term.UOp UserOp.exists) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.exists) x F) G
                              have hGuard' :
                                  __eo_or
                                      (__eo_eq (Term.UOp UserOp.exists)
                                        (Term.UOp UserOp.forall))
                                      (__eo_eq (Term.UOp UserOp.exists)
                                        (Term.UOp UserOp.exists)) =
                                    Term.Boolean true := by
                                simp [__eo_or, __eo_eq, native_or, native_teq]
                              have hNoFree' :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (qterm (Term.UOp UserOp.exists) x F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [v0, qterm, noFree] using hNoFree
                              have hNoFreeRaw :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (((Term.UOp UserOp.exists).Apply x).Apply F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [qterm] using hNoFree'
                              simp [qeq, qterm, __eo_prog_quant_unused_vars,
                                hGuard', hNoFreeRaw, __eo_requires, native_ite,
                                native_teq, native_not, SmtEval.native_not]
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

private theorem quant_unused_vars_has_smt_translation
    (A : Term)
    (hTransA : RuleProofs.eo_has_smt_translation A)
    (hTy : __eo_typeof (__eo_prog_quant_unused_vars A) = Term.Bool) :
    RuleProofs.eo_has_smt_translation (__eo_prog_quant_unused_vars A) := by
  have hProg : __eo_prog_quant_unused_vars A ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases quant_unused_shape_of_not_stuck A hProg with
    ⟨Q, x, F, G, hA, _hQ, _hNoFree, hProgEq⟩
  rw [hProgEq]
  simpa [hA] using hTransA

private theorem quant_unused_eval
    (M : SmtModel) (hM : model_total_typed M)
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
        (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
          Term.Boolean false)
    (hBool : RuleProofs.eo_has_bool_type (qeq (qterm Q x F) G)) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M (__eo_to_smt G) := by
  have hGetNe :
      __get_unused_vars (qterm Q x F) G ≠ Term.Stuck :=
    get_unused_vars_ne_stuck_of_contains_false hNoFree
  rcases get_unused_vars_shape_of_not_stuck Q x F G hGetNe with
    hSame | hQuant
  · rcases hSame with ⟨hG, hUnused⟩
    subst G
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (qterm Q x F) F hBool with
      ⟨hSameTy, hQuantNN⟩
    have hQuantTy :
        __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool :=
      qterm_typeof_bool_of_quant_non_none Q x F hQ hQuantNN
    have hBodyTy :
        __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
      qterm_body_typeof_bool_of_quant_typeof_bool Q x F hQ hQuantTy
    rcases smt_model_eval_bool_is_boolean M hM (__eo_to_smt F) hBodyTy with
      ⟨b, hBodyEval⟩
    have hConst : body_constant_on_eo_binders (__eo_to_smt F) x := by
      rcases qterm_binder_env_of_quant_typeof_bool Q x F hQ hQuantTy with
        ⟨vars, hBinders⟩
      have hBinderVarList : eo_var_list x := eo_var_list_of_env hBinders
      have hScanSetof :
          __contains_atomic_term_list_free_rec F
              (__eo_list_setof Term.__eo_List_cons x)
              Term.__eo_List_nil =
            Term.Boolean false := by
        simpa [hUnused] using hNoFree
      have hExistsTyForBinders :
          ∃ body : SmtTerm,
            __smtx_typeof (__eo_to_smt_exists x body) =
              SmtType.Bool := by
        rcases hQ with hForall | hExists
        · subst Q
          have hTyForall :
              __smtx_typeof (__eo_to_smt (qforall x F)) =
                SmtType.Bool := by
            simpa [qforall, qterm] using hQuantTy
          have hx : x ≠ Term.__eo_List_nil :=
            qforall_non_nil_of_non_none x F hQuantNN
          refine ⟨SmtTerm.not (__eo_to_smt F), ?_⟩
          rw [eo_to_smt_forall_eq x F hx] at hTyForall
          exact smtx_typeof_not_arg_of_bool _ hTyForall
        · subst Q
          have hTyExists :
              __smtx_typeof (__eo_to_smt (qexists x F)) =
                SmtType.Bool := by
            simpa [qexists, qterm] using hQuantTy
          have hx : x ≠ Term.__eo_List_nil :=
            qexists_non_nil_of_non_none x F hQuantNN
          refine ⟨__eo_to_smt F, ?_⟩
          simpa [eo_to_smt_exists_eq x F hx] using hTyExists
      rcases hExistsTyForBinders with ⟨binderBody, hExistsTy⟩
      have hWfAll :
          ∀ (s : native_String) (T : Term),
            eo_var_list_mem (Term.Var (Term.String s) T) x ->
              __smtx_type_wf (__eo_to_smt_type T) = true :=
        eo_smt_var_env_mem_wf_of_exists_bool hBinders hExistsTy
      exact body_constant_on_eo_binders_of_scan_setof_aux
        F x x hBinderVarList hBinders
        (fun _ _ hMem => hMem) hWfAll
        (fun M' N' hRel => by
          exact
            smtx_model_eval_eq_of_contains_atomic_false F
              (__eo_list_setof Term.__eo_List_cons x)
              Term.__eo_List_nil M' N' hRel hScanSetof
              (by rw [hBodyTy]; simp))
    rcases hQ with hForall | hExists
    · subst Q
      have hx : x ≠ Term.__eo_List_nil :=
        qforall_non_nil_of_non_none x F hQuantNN
      exact
        (smtx_model_eval_qforall_eq_of_body_constant_on_binders
          x F M b hx hQuantTy hBodyEval hConst).trans hBodyEval.symm
    · subst Q
      have hx : x ≠ Term.__eo_List_nil :=
        qexists_non_nil_of_non_none x F hQuantNN
      exact
        (smtx_model_eval_qexists_eq_of_body_constant_on_binders
          x F M b hx hQuantTy hBodyEval hConst).trans hBodyEval.symm
  · rcases hQuant with ⟨y, hG, hInclude, hUnused⟩
    subst G
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (qterm Q x F) (qterm Q y F) hBool with
      ⟨hSameTy, hQuantNN⟩
    have hLeftTy :
        __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool :=
      qterm_typeof_bool_of_quant_non_none Q x F hQ hQuantNN
    have hBodyTy :
        __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
      qterm_body_typeof_bool_of_quant_typeof_bool Q x F hQ hLeftTy
    have hRightTy :
        __smtx_typeof (__eo_to_smt (qterm Q y F)) = SmtType.Bool := by
      rw [← hSameTy]
      exact hLeftTy
    rcases qterm_binder_env_of_quant_typeof_bool Q x F hQ hLeftTy with
      ⟨xVars, hXBinders⟩
    rcases qterm_binder_env_of_quant_typeof_bool Q y F hQ hRightTy with
      ⟨yVars, hYBinders⟩
    have hXVarList : eo_var_list x := eo_var_list_of_env hXBinders
    have hYVarList : eo_var_list y := eo_var_list_of_env hYBinders
    have hUnusedVarList :
        eo_var_list
          (__eo_list_diff Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y) :=
      eo_var_list_diff (eo_var_list_setof hXVarList) hYVarList
    rcases eo_smt_var_env_of_var_list hUnusedVarList with
      ⟨unusedVars, hUnusedBinders⟩
    let unused :=
      __eo_list_diff Term.__eo_List_cons
        (__eo_list_setof Term.__eo_List_cons x) y
    have hYNonNil : y ≠ Term.__eo_List_nil := by
      have hRightNN :
          __smtx_typeof (__eo_to_smt (qterm Q y F)) ≠ SmtType.None := by
        rw [hRightTy]
        simp
      rcases hQ with hForall | hExists
      · subst Q
        exact qforall_non_nil_of_non_none y F hRightNN
      · subst Q
        exact qexists_non_nil_of_non_none y F hRightNN
    have hQNe : Q ≠ Term.Stuck := by
      rcases hQ with hForall | hExists
      · subst Q
        intro h
        cases h
      · subst Q
        intro h
        cases h
    have hScanRight :
        __contains_atomic_term_list_free_rec (qterm Q y F)
            unused Term.__eo_List_nil =
          Term.Boolean false := by
      simpa [unused, hUnused] using hNoFree
    have hScanBody :
        __contains_atomic_term_list_free_rec F unused
            (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil) =
          Term.Boolean false :=
      contains_atomic_qterm_body_of_false hYBinders hYNonNil hQNe hScanRight
    have hConcatY :
        __eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil = y :=
      eo_list_concat_nil_eq_of_var_list hYVarList
    have hScanBodyY :
        __contains_atomic_term_list_free_rec F unused y =
          Term.Boolean false := by
      simpa [hConcatY] using hScanBody
    have hBodyStable :
        ∀ M' N' : SmtModel,
          scannerModelRel unused y M' N' ->
            __smtx_model_eval M' (__eo_to_smt F) =
              __smtx_model_eval N' (__eo_to_smt F) := by
      intro M' N' hRel
      exact
        smtx_model_eval_eq_of_contains_atomic_false F unused y
          M' N' hRel hScanBodyY
          (by rw [hBodyTy]; simp)
    -- Remaining bridge: `hNoFree` must yield constancy under the binders in
    -- `diff (setof x) y`, allowing the quantifier over `x` to be reduced to
    -- the quantifier over `y`.
    sorry

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
  have hProg :
      __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                  using hCmdTrans
              have hProgTy :
                  __eo_typeof (__eo_prog_quant_unused_vars a1) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) = Term.Bool
                  at hResultTy
                exact hResultTy
              have hProgQuant :
                  __eo_prog_quant_unused_vars a1 ≠ Term.Stuck := by
                exact term_ne_stuck_of_typeof_bool hProgTy
              rcases quant_unused_shape_of_not_stuck a1 hProgQuant with
                ⟨Q, x, F, G, hA1, hQ, hNoFree, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (qeq (qterm Q x F) G) := by
                simpa [hA1] using hTransA1
              have hFormulaType :
                  __eo_typeof (qeq (qterm Q x F) G) = Term.Bool := by
                rw [hProgEq] at hProgTy
                exact hProgTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (qeq (qterm Q x F) G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (qeq (qterm Q x F) G) hTransFormula hFormulaType
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_unused_vars a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M
                  (qterm Q x F) G
                · exact hFormulaBool
                · have hEvalEq :=
                    quant_unused_eval M hM Q x F G hQ hNoFree hFormulaBool
                  rw [hEvalEq]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M (__eo_to_smt G))
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_unused_vars a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
