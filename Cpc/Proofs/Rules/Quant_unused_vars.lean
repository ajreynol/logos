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

private theorem smtx_model_eval_none_eq (M : SmtModel) :
    __smtx_model_eval M SmtTerm.None = SmtValue.NotValue := by
  simp [__smtx_model_eval]

private theorem smtx_model_eval_var_eq
    (M : SmtModel) (s : native_String) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.Var s T) =
      native_model_var_lookup M s T := by
  simp [__smtx_model_eval]

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

private theorem contains_atomic_term_list_free_rec_vars_ne_stuck_of_false
    {t xs bvs : Term} :
    __contains_atomic_term_list_free_rec t xs bvs = Term.Boolean false ->
    xs ≠ Term.Stuck := by
  intro h hxs
  subst xs
  cases t <;> cases bvs <;>
    simp [__contains_atomic_term_list_free_rec] at h

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
    -- Remaining bridge: `hNoFree` must yield constancy of `F` under every
    -- binder in `x`, then `qforall`/`qexists` can be dropped with the lemmas
    -- above.
    sorry
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
