import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Closed.UOpIndices

open Eo
open SmtEval
open Smtm
open TranslationProofs

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def eoListOfTerms : List Term -> Term
  | [] => Term.__eo_List_nil
  | x :: xs => Term.Apply (Term.Apply Term.__eo_List_cons x) (eoListOfTerms xs)

private def IsQuantVarTerm : Term -> Prop
  | Term.Var (Term.String _) _ => True
  | _ => False

private abbrev QuantBinder := native_String × SmtType

private def quantTermBinder : Term -> QuantBinder
  | Term.Var (Term.String s) T => (s, __eo_to_smt_type T)
  | _ => (native_string_lit "", SmtType.None)

private def smtExistsOfBinders : List QuantBinder -> SmtTerm -> SmtTerm
  | [], body => body
  | b :: bs, body => SmtTerm.exists b.1 b.2 (smtExistsOfBinders bs body)

private def quantUnusedVarsList : List Term -> Term -> List Term
  | [], _ => []
  | x :: xs, F =>
      let rest := quantUnusedVarsList xs F
      if __contains_atomic_term F x = Term.Boolean true then
        x :: rest.erase x
      else
        rest

private theorem quantVarTerm_ne_stuck {t : Term} :
    IsQuantVarTerm t -> t ≠ Term.Stuck := by
  intro h
  cases t <;> simp [IsQuantVarTerm] at h ⊢

private theorem eo_eq_eq_true_of_eq_local {x y : Term} :
    x = y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean true := by
  intro hEq hX _hY
  subst y
  simp [__eo_eq, native_teq]

private theorem eo_eq_eq_false_of_ne_local {x y : Term} :
    x ≠ y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean false := by
  intro hNe hX hY
  have hNeYX : y ≠ x := by
    intro h
    exact hNe h.symm
  simp [__eo_eq, native_teq, hNeYX]

private theorem eoListOfTerms_ne_stuck (xs : List Term) :
    eoListOfTerms xs ≠ Term.Stuck := by
  cases xs <;> simp [eoListOfTerms]

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

private theorem uop_indices_safe_apply_left {f x : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.Apply f x)) :
    NativeEoToSmtUOpIndicesSafe f := by
  exact native_and_left_eq_true (by
    simpa [NativeEoToSmtUOpIndicesSafe,
      native_eo_to_smt_uop_indices_safe] using h)

private theorem uop_indices_safe_apply_right {f x : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.Apply f x)) :
    NativeEoToSmtUOpIndicesSafe x := by
  exact native_and_right_eq_true (by
    simpa [NativeEoToSmtUOpIndicesSafe,
      native_eo_to_smt_uop_indices_safe] using h)

private theorem term_ne_stuck_of_eo_to_smt_type_bool
    {t : Term}
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Bool) :
    t ≠ Term.Stuck := by
  intro hStuck
  subst t
  have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl] at hTy
    exact hTy
  exact TranslationProofs.smtx_typeof_none_ne_bool hNone

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

private theorem smtx_typeof_not_arg_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  cases h : __smtx_typeof t <;>
    simp [h, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  cases h : __smtx_typeof t <;>
    simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢

private theorem smtx_model_eval_exists_unused
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBody : __smtx_typeof body = SmtType.Bool)
    (hInv :
      ∀ v : SmtValue,
        __smtx_model_eval (native_model_push M s T v) body =
          __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.exists s T body) =
      __smtx_model_eval M body := by
  classical
  rcases smt_model_eval_bool_is_boolean M hM body hBody with ⟨b, hb⟩
  rcases canonical_type_inhabited_of_type_wf T hWF with
    ⟨w, hwTy, hwCanon⟩
  have hwCanonBool : __smtx_value_canonical_bool w = true := by
    simpa [Smtm.__smtx_value_canonical] using hwCanon
  cases b
  · let P : Prop :=
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true
    have hNotP : ¬ P := by
      intro hP
      rcases hP with ⟨v, _hvTy, _hvCanon, hEval⟩
      have hEvalFalse :
          __smtx_model_eval (native_model_push M s T v) body =
            SmtValue.Boolean false := by
        rw [hInv v, hb]
      cases hEvalFalse.symm.trans hEval
    rw [__smtx_model_eval.eq_135, hb]
    change (if _ : P then SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean false
    simp [hNotP]
  · let P : Prop :=
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true
    have hP : P := by
      exact ⟨w, hwTy, hwCanonBool, by rw [hInv w, hb]⟩
    rw [__smtx_model_eval.eq_135, hb]
    change (if _ : P then SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean true
    simp [hP]

private theorem smtx_model_eval_forall_unused
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBody : __smtx_typeof body = SmtType.Bool)
    (hInv :
      ∀ v : SmtValue,
        __smtx_model_eval (native_model_push M s T v) body =
          __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.forall s T body) =
      __smtx_model_eval M body := by
  classical
  rcases smt_model_eval_bool_is_boolean M hM body hBody with ⟨b, hb⟩
  rcases canonical_type_inhabited_of_type_wf T hWF with
    ⟨w, hwTy, hwCanon⟩
  have hwCanonBool : __smtx_value_canonical_bool w = true := by
    simpa [Smtm.__smtx_value_canonical] using hwCanon
  cases b
  · let P : Prop :=
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
          __smtx_value_canonical_bool v = true ->
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true
    have hNotP : ¬ P := by
      intro hP
      have hEvalTrue := hP w hwTy hwCanonBool
      have hEvalFalse :
          __smtx_model_eval (native_model_push M s T w) body =
            SmtValue.Boolean false := by
        rw [hInv w, hb]
      cases hEvalFalse.symm.trans hEvalTrue
    rw [__smtx_model_eval.eq_136, hb]
    change (if _ : P then SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean false
    simp [hNotP]
  · let P : Prop :=
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
          __smtx_value_canonical_bool v = true ->
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true
    have hP : P := by
      intro v _hvTy _hvCanon
      rw [hInv v, hb]
    rw [__smtx_model_eval.eq_136, hb]
    change (if _ : P then SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean true
    simp [hP]

private theorem smtx_model_eval_not_not_of_bool
    (M : SmtModel) (hM : model_total_typed M) (body : SmtTerm)
    (hBody : __smtx_typeof body = SmtType.Bool) :
    __smtx_model_eval M (SmtTerm.not (SmtTerm.not body)) =
      __smtx_model_eval M body := by
  rcases smt_model_eval_bool_is_boolean M hM body hBody with ⟨b, hb⟩
  cases b <;>
    simp [__smtx_model_eval, hb, __smtx_model_eval_not, native_not]

private theorem smtx_model_eval_not_congr
    (M N : SmtModel) (body : SmtTerm)
    (hEval :
      __smtx_model_eval M body =
        __smtx_model_eval N body) :
    __smtx_model_eval M (SmtTerm.not body) =
      __smtx_model_eval N (SmtTerm.not body) := by
  simp [__smtx_model_eval, hEval]

private theorem smtx_model_eval_not_congr_term
    (M : SmtModel) (a b : SmtTerm)
    (hEval :
      __smtx_model_eval M a =
        __smtx_model_eval M b) :
    __smtx_model_eval M (SmtTerm.not a) =
      __smtx_model_eval M (SmtTerm.not b) := by
  simp [__smtx_model_eval, hEval]

private theorem smtx_model_eval_forall_encoded_unused
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBody : __smtx_typeof body = SmtType.Bool)
    (hInv :
      ∀ v : SmtValue,
        __smtx_model_eval (native_model_push M s T v) body =
          __smtx_model_eval M body) :
    __smtx_model_eval M
        (SmtTerm.not (SmtTerm.exists s T (SmtTerm.not body))) =
      __smtx_model_eval M body := by
  have hNotBody : __smtx_typeof (SmtTerm.not body) = SmtType.Bool := by
    rw [typeof_not_eq, hBody]
    simp [native_ite, native_Teq]
  have hInvNot :
      ∀ v : SmtValue,
        __smtx_model_eval (native_model_push M s T v) (SmtTerm.not body) =
          __smtx_model_eval M (SmtTerm.not body) := by
    intro v
    exact smtx_model_eval_not_congr
      (native_model_push M s T v) M body (hInv v)
  have hExists :=
    smtx_model_eval_exists_unused M hM s T (SmtTerm.not body)
      hWF hNotBody hInvNot
  exact
    (smtx_model_eval_not_congr_term M
      (SmtTerm.exists s T (SmtTerm.not body)) (SmtTerm.not body)
      hExists).trans
      (smtx_model_eval_not_not_of_bool M hM body hBody)

private theorem smtExistsOfBinders_cons_congr
    (M : SmtModel) (b : QuantBinder) (t u : SmtTerm) :
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

private theorem smtExistsOfBinders_swap
    (M : SmtModel) (b1 b2 : QuantBinder) (tail : List QuantBinder)
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

private theorem smtExistsOfBinders_eval_perm
    (body : SmtTerm) {xs ys : List QuantBinder}
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

private theorem smtExistsOfBinders_duplicate_head
    (M : SmtModel) (b : QuantBinder) (tail : List QuantBinder)
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
      rcases hSat with ⟨_v1, _hv1, _hc1, v2, hv2, hc2, hEval⟩
      exact ⟨v2, hv2, hc2, by
        simpa [native_model_push_same] using hEval⟩
    · intro hSat
      rcases hSat with ⟨v, hv, hc, hEval⟩
      exact ⟨v, hv, hc, v, hv, hc, by
        simpa [native_model_push_same] using hEval⟩
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, rest, hPropEq]

private theorem smtExistsOfBinders_duplicate_erase
    (M : SmtModel) (b : QuantBinder) (bs : List QuantBinder)
    (body : SmtTerm) :
    __smtx_model_eval M (smtExistsOfBinders (b :: bs) body) =
      __smtx_model_eval M (smtExistsOfBinders (b :: bs.erase b) body) := by
  classical
  by_cases hb : b ∈ bs
  · have hPerm :
        (b :: bs).Perm (b :: b :: bs.erase b) := by
      exact List.Perm.cons b (List.perm_cons_erase hb)
    rw [smtExistsOfBinders_eval_perm body hPerm M]
    exact smtExistsOfBinders_duplicate_head M b (bs.erase b) body
  · have hErase : bs.erase b = bs := (List.erase_eq_self_iff).2 hb
    simp [hErase]

private theorem smtExistsOfBinders_duplicate_erase_term
    (M : SmtModel) (x : Term) (xs : List Term) (body : SmtTerm) :
    __smtx_model_eval M
        (smtExistsOfBinders (quantTermBinder x :: xs.map quantTermBinder)
          body) =
      __smtx_model_eval M
        (smtExistsOfBinders
          (quantTermBinder x :: (xs.erase x).map quantTermBinder) body) := by
  classical
  induction xs generalizing M with
  | nil =>
      simp
  | cons y ys ih =>
      by_cases hyx : y = x
      · subst y
        simp
        exact smtExistsOfBinders_duplicate_head M
          (quantTermBinder x) (ys.map quantTermBinder) body
      · have hErase : (y :: ys).erase x = y :: ys.erase x := by
          simpa [hyx] using List.erase_cons_tail (a := y) (b := x)
            (l := ys) (by simpa [hyx])
        rw [hErase]
        let bY := quantTermBinder y
        let bx := quantTermBinder x
        let tail := ys.map quantTermBinder
        let tailErase := (ys.erase x).map quantTermBinder
        have hSwapL :
            __smtx_model_eval M (smtExistsOfBinders (bx :: bY :: tail) body) =
              __smtx_model_eval M
                (smtExistsOfBinders (bY :: bx :: tail) body) := by
          exact smtExistsOfBinders_swap M bx bY tail body
        have hInner :
            ∀ M2,
              __smtx_model_eval M2
                  (smtExistsOfBinders (bx :: tail) body) =
                __smtx_model_eval M2
                  (smtExistsOfBinders (bx :: tailErase) body) := by
          intro M2
          simpa [bx, tail, tailErase] using ih M2
        have hLift :
            __smtx_model_eval M
                (smtExistsOfBinders (bY :: bx :: tail) body) =
              __smtx_model_eval M
                (smtExistsOfBinders (bY :: bx :: tailErase) body) := by
          exact smtExistsOfBinders_cons_congr M bY
            (smtExistsOfBinders (bx :: tail) body)
            (smtExistsOfBinders (bx :: tailErase) body)
            hInner
        have hSwapR :
            __smtx_model_eval M
                (smtExistsOfBinders (bY :: bx :: tailErase) body) =
              __smtx_model_eval M
                (smtExistsOfBinders (bx :: bY :: tailErase) body) := by
          exact (smtExistsOfBinders_swap M bx bY tailErase body).symm
        simpa [bx, bY, tail, tailErase] using hSwapL.trans
          (hLift.trans hSwapR)

private theorem smtExistsOfBinders_tail_bool_of_cons_bool
    (b : QuantBinder) (bs : List QuantBinder) (body : SmtTerm) :
    __smtx_typeof (smtExistsOfBinders (b :: bs) body) = SmtType.Bool ->
    __smtx_typeof (smtExistsOfBinders bs body) = SmtType.Bool := by
  rcases b with ⟨s, T⟩
  intro hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.exists s T (smtExistsOfBinders bs body)) := by
    unfold term_has_non_none_type
    have hExists :
        __smtx_typeof (SmtTerm.exists s T (smtExistsOfBinders bs body)) =
          SmtType.Bool := by
      simpa [smtExistsOfBinders] using hTy
    rw [hExists]
    simp
  exact exists_body_bool_of_non_none hNN

private theorem smtExistsOfBinders_head_wf_of_cons_bool
    (b : QuantBinder) (bs : List QuantBinder) (body : SmtTerm) :
    __smtx_typeof (smtExistsOfBinders (b :: bs) body) = SmtType.Bool ->
    __smtx_type_wf b.2 = true := by
  rcases b with ⟨s, T⟩
  intro hTy
  have hTail :
      __smtx_typeof (smtExistsOfBinders bs body) = SmtType.Bool :=
    smtExistsOfBinders_tail_bool_of_cons_bool (s, T) bs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
    intro hNone
    have hExists :
        __smtx_typeof (SmtTerm.exists s T (smtExistsOfBinders bs body)) =
          SmtType.Bool := by
      simpa [smtExistsOfBinders] using hTy
    rw [__smtx_typeof.eq_135, hTail] at hExists
    simp [native_ite, native_Teq, hNone] at hExists
  exact smtx_typeof_guard_wf_wf_of_non_none T SmtType.Bool hGuardNN

private theorem smtExistsOfBinders_eval_eq_push_of_body_inv
    (sx : native_String) (Tx : SmtType)
    (body : SmtTerm)
    (hInv :
      ∀ (M0 : SmtModel) (v : SmtValue),
        __smtx_model_eval (native_model_push M0 sx Tx v) body =
          __smtx_model_eval M0 body) :
    ∀ (bs : List QuantBinder) (M : SmtModel) (v : SmtValue),
      __smtx_model_eval (native_model_push M sx Tx v)
          (smtExistsOfBinders bs body) =
        __smtx_model_eval M (smtExistsOfBinders bs body)
  | [], M, v => by
      exact hInv M v
  | b :: bs, M, v => by
      rcases b with ⟨sy, Ty⟩
      apply smtx_model_eval_exists_eq_of_body_eval_eq
      intro w
      by_cases hKey :
          ({ isVar := true, name := sx, ty := Tx } : SmtModelKey) =
            { isVar := true, name := sy, ty := Ty }
      · cases hKey
        simpa [native_model_push_same] using
          smtExistsOfBinders_eval_eq_push_of_body_inv sx Tx body hInv
            bs M w
      · have hComm :
            native_model_push (native_model_push M sx Tx v) sy Ty w =
              native_model_push (native_model_push M sy Ty w) sx Tx v := by
          exact native_model_push_comm M sx sy Tx Ty v w hKey
        rw [hComm]
        exact smtExistsOfBinders_eval_eq_push_of_body_inv sx Tx body hInv
          bs (native_model_push M sy Ty w) v

private theorem smtExistsOfBinders_unused_head
    (M : SmtModel) (hM : model_total_typed M)
    (b : QuantBinder) (bs : List QuantBinder) (body : SmtTerm)
    (hTy : __smtx_typeof (smtExistsOfBinders (b :: bs) body) = SmtType.Bool)
    (hInv :
      ∀ (M0 : SmtModel) (v : SmtValue),
        __smtx_model_eval (native_model_push M0 b.1 b.2 v) body =
          __smtx_model_eval M0 body) :
    __smtx_model_eval M (smtExistsOfBinders (b :: bs) body) =
      __smtx_model_eval M (smtExistsOfBinders bs body) := by
  rcases b with ⟨s, T⟩
  have hWF : __smtx_type_wf T = true :=
    smtExistsOfBinders_head_wf_of_cons_bool (s, T) bs body hTy
  have hBodyTy :
      __smtx_typeof (smtExistsOfBinders bs body) = SmtType.Bool :=
    smtExistsOfBinders_tail_bool_of_cons_bool (s, T) bs body hTy
  exact smtx_model_eval_exists_unused M hM s T
    (smtExistsOfBinders bs body) hWF hBodyTy
    (fun v =>
      smtExistsOfBinders_eval_eq_push_of_body_inv s T body hInv bs M v)

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
                __smtx_typeof (__eo_to_smt_exists a body) =
                  SmtType.Bool := by
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
              simpa [__eo_to_smt_exists] using hTy
            exact False.elim (TranslationProofs.smtx_typeof_none_ne_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simpa [__eo_to_smt_exists] using hTy
          exact False.elim (TranslationProofs.smtx_typeof_none_ne_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (TranslationProofs.smtx_typeof_none_ne_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        simpa [__eo_to_smt_exists] using hTy
      exact False.elim (TranslationProofs.smtx_typeof_none_ne_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    exact False.elim (TranslationProofs.smtx_typeof_none_ne_bool hNone)

private theorem eo_to_smt_exists_body_bool_of_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __smtx_typeof body = SmtType.Bool := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    simpa [__eo_to_smt_exists] using hTy
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
                __smtx_typeof (__eo_to_smt_exists a body) =
                  SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            exact eo_to_smt_exists_body_bool_of_bool a body hSub
          all_goals
            subst hname
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            exact False.elim (TranslationProofs.smtx_typeof_none_ne_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simpa [__eo_to_smt_exists] using hTy
          exact False.elim (TranslationProofs.smtx_typeof_none_ne_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (TranslationProofs.smtx_typeof_none_ne_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        simpa [__eo_to_smt_exists] using hTy
      exact False.elim (TranslationProofs.smtx_typeof_none_ne_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    exact False.elim (TranslationProofs.smtx_typeof_none_ne_bool hNone)

private theorem eo_to_smt_exists_bool_of_non_nil_non_none
    (xs : Term) (body : SmtTerm)
    (hxs : xs ≠ Term.__eo_List_nil)
    (hNN : __smtx_typeof (__eo_to_smt_exists xs body) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  cases h : xs
  case __eo_List_nil =>
    exact False.elim (hxs h)
  case Apply f a =>
    cases hf : f
    case Apply g y =>
      cases hg : g
      case __eo_List_cons =>
        cases hy : y
        case Var name T =>
          cases hname : name
          case String s =>
            have hExistsNN :
                term_has_non_none_type
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              simpa [h, hf, hg, hy, hname, __eo_to_smt_exists] using hNN
            simpa [h, hf, hg, hy, hname, __eo_to_smt_exists] using
              exists_term_typeof_of_non_none hExistsNN
          all_goals
            exfalso
            apply hNN
            simp [h, hf, hg, hy, hname, __eo_to_smt_exists,
              TranslationProofs.smtx_typeof_none]
        all_goals
          exfalso
          apply hNN
          simp [h, hf, hg, hy, __eo_to_smt_exists,
            TranslationProofs.smtx_typeof_none]
      all_goals
        exfalso
        apply hNN
        simp [h, hf, hg, __eo_to_smt_exists,
          TranslationProofs.smtx_typeof_none]
    all_goals
      exfalso
      apply hNN
      simp [h, hf, __eo_to_smt_exists,
        TranslationProofs.smtx_typeof_none]
  all_goals
    exfalso
    apply hNN
    simp [h, __eo_to_smt_exists, TranslationProofs.smtx_typeof_none]

private theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs)
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
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs)
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
    rw [__smtx_typeof.eq_135, hTail] at hExists
    simp [native_ite, native_Teq, hNone] at hExists
  exact smtx_typeof_guard_wf_wf_of_non_none
    (__eo_to_smt_type T) SmtType.Bool hGuardNN

private theorem eo_to_smt_exists_eoListOfTerms_binders
    (xs : List Term) (body : SmtTerm)
    (hxs : ∀ t ∈ xs, IsQuantVarTerm t) :
    __eo_to_smt_exists (eoListOfTerms xs) body =
      smtExistsOfBinders (xs.map quantTermBinder) body := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, smtExistsOfBinders]
  | cons x xs ih =>
      have hx : IsQuantVarTerm x := hxs x (by simp)
      have htail : ∀ t ∈ xs, IsQuantVarTerm t := by
        intro t ht
        exact hxs t (by simp [ht])
      cases x <;> simp [IsQuantVarTerm] at hx
      case Var name T =>
        cases name <;> simp at hx
        case String s =>
          simp [eoListOfTerms, smtExistsOfBinders, quantTermBinder,
            ih htail]

private theorem eo_to_smt_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) x) F) =
      SmtTerm.not (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) := by
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem eo_to_smt_exists_quant_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) x) F) =
      __eo_to_smt_exists x (__eo_to_smt F) := by
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem quant_uop_non_nil_of_non_none
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNN :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Q x) F)) ≠
        SmtType.None) :
    x ≠ Term.__eo_List_nil := by
  intro hx
  subst x
  rcases hQ with hQ | hQ
  · subst Q
    apply hNN
    change __smtx_typeof SmtTerm.None = SmtType.None
    simp [TranslationProofs.smtx_typeof_none]
  · subst Q
    apply hNN
    change __smtx_typeof SmtTerm.None = SmtType.None
    simp [TranslationProofs.smtx_typeof_none]

private theorem quant_uop_inner_exists_bool_of_non_none
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNN :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Q x) F)) ≠
        SmtType.None) :
    (Q = Term.UOp UserOp.forall ->
        __smtx_typeof
            (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool) ∧
      (Q = Term.UOp UserOp.exists ->
        __smtx_typeof (__eo_to_smt_exists x (__eo_to_smt F)) =
          SmtType.Bool) := by
  have hx : x ≠ Term.__eo_List_nil :=
    quant_uop_non_nil_of_non_none Q x F hQ hNN
  constructor
  · intro hForall
    subst Q
    have hNN' :
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F)))) ≠
          SmtType.None := by
      simpa [eo_to_smt_forall_eq x F hx] using hNN
    exact smtx_typeof_not_arg_of_non_none _ hNN'
  · intro hExists
    subst Q
    have hNN' :
        __smtx_typeof (__eo_to_smt_exists x (__eo_to_smt F)) ≠
          SmtType.None := by
      simpa [eo_to_smt_exists_quant_eq x F hx] using hNN
    exact eo_to_smt_exists_bool_of_non_nil_non_none x (__eo_to_smt F)
      hx hNN'

private theorem quant_uop_binders_as_eoList_of_non_none
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNN :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Q x) F)) ≠
        SmtType.None) :
    ∃ xs, x = eoListOfTerms xs ∧ xs ≠ [] ∧
      ∀ t ∈ xs, IsQuantVarTerm t := by
  have hx : x ≠ Term.__eo_List_nil :=
    quant_uop_non_nil_of_non_none Q x F hQ hNN
  rcases hQ with hForall | hExists
  · have hInner :=
      (quant_uop_inner_exists_bool_of_non_none Q x F
        (Or.inl hForall) hNN).1 hForall
    rcases eo_to_smt_exists_bool_as_eoList x
        (SmtTerm.not (__eo_to_smt F)) hInner with
      ⟨xs, hxEq, hAll⟩
    refine ⟨xs, hxEq, ?_, hAll⟩
    intro hNil
    apply hx
    rw [hxEq, hNil]
    rfl
  · have hInner :=
      (quant_uop_inner_exists_bool_of_non_none Q x F
        (Or.inr hExists) hNN).2 hExists
    rcases eo_to_smt_exists_bool_as_eoList x
        (__eo_to_smt F) hInner with
      ⟨xs, hxEq, hAll⟩
    refine ⟨xs, hxEq, ?_, hAll⟩
    intro hNil
    apply hx
    rw [hxEq, hNil]
    rfl

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
          eo_eq_eq_true_of_eq_local rfl hx hx, List.erase_cons_head,
          native_ite, native_teq]
      · have hEqTerm : __eo_eq x e = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local hxe hx he
        have hTailEq := ih htail
        have hBeq : ¬(x == e) = true := by
          simp [hxe]
        rw [List.erase_cons_tail hBeq]
        simp [eoListOfTerms, __eo_list_erase_rec, __eo_ite,
          __eo_mk_apply, hEqTerm, hTailEq, eoListOfTerms_ne_stuck,
          native_ite, native_teq]

private theorem eo_list_erase_eoListOfTerms_eq
    {xs : List Term} {e : Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (he : e ≠ Term.Stuck) :
    __eo_list_erase Term.__eo_List_cons (eoListOfTerms xs) e =
      eoListOfTerms (xs.erase e) := by
  simp [__eo_list_erase, eoListOfTerms_is_list, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not,
    eo_list_erase_rec_eoListOfTerms_eq hxs he]

private theorem quantUnusedVarsList_no_stuck
    {xs : List Term} {F : Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck) :
    ∀ t ∈ quantUnusedVarsList xs F, t ≠ Term.Stuck := by
  induction xs with
  | nil =>
      intro t ht
      simp [quantUnusedVarsList] at ht
  | cons x xs ih =>
      intro u hu
      have hx : x ≠ Term.Stuck := hxs x (by simp)
      have hxsTail : ∀ z ∈ xs, z ≠ Term.Stuck := by
        intro z hz
        exact hxs z (by simp [hz])
      by_cases hC : __contains_atomic_term F x = Term.Boolean true
      · simp [quantUnusedVarsList, hC] at hu
        rcases hu with hu | hu
        · subst u
          exact hx
        · exact ih hxsTail u (List.mem_of_mem_erase hu)
      · simp [quantUnusedVarsList, hC] at hu
        exact ih hxsTail u hu

private theorem mk_quant_unused_vars_rec_eoListOfTerms_eq :
    ∀ {xs : List Term} {F : Term},
      F ≠ Term.Stuck ->
      (∀ t ∈ xs, t ≠ Term.Stuck) ->
      (∀ t ∈ xs,
        __contains_atomic_term F t = Term.Boolean true ∨
          __contains_atomic_term F t = Term.Boolean false) ->
        __mk_quant_unused_vars_rec (eoListOfTerms xs) F =
          eoListOfTerms (quantUnusedVarsList xs F)
  | [], F, hF, _hxs, _hContains => by
      cases F <;> simp [eoListOfTerms, quantUnusedVarsList,
        __mk_quant_unused_vars_rec] at hF ⊢
  | x :: xs, F, hF, hxs, hContains => by
      have hx : x ≠ Term.Stuck := hxs x (by simp)
      have hxsTail : ∀ t ∈ xs, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (by simp [ht])
      have hContainsTail :
          ∀ t ∈ xs,
            __contains_atomic_term F t = Term.Boolean true ∨
              __contains_atomic_term F t = Term.Boolean false := by
        intro t ht
        exact hContains t (by simp [ht])
      have hRec :=
        mk_quant_unused_vars_rec_eoListOfTerms_eq hF hxsTail hContainsTail
      rcases hContains x (by simp) with hCx | hCx
      · simp [eoListOfTerms, quantUnusedVarsList,
          __mk_quant_unused_vars_rec, hCx, hRec, __eo_ite,
          native_ite, native_teq]
        rw [eo_list_erase_eoListOfTerms_eq
          (xs := quantUnusedVarsList xs F) (e := x)
          (quantUnusedVarsList_no_stuck hxsTail) hx]
        exact eo_mk_apply_list_cons_eoListOfTerms x
          ((quantUnusedVarsList xs F).erase x)
      · simp [eoListOfTerms, quantUnusedVarsList,
          __mk_quant_unused_vars_rec, hCx, hRec, __eo_ite,
          native_ite, native_teq]

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
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.Apply Q x) F)
      (__mk_quant Q (__mk_quant_unused_vars_rec x F) F) hBool with
    ⟨_hSameTy, hLhsNN⟩
  rcases quant_uop_binders_as_eoList_of_non_none Q x F hQ hLhsNN with
    ⟨xs, hxEq, hxsNonempty, hxsAll⟩
  subst x
  have hxsNonStuck : ∀ t ∈ xs, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hxsAll t ht)
  have hSafeF : NativeEoToSmtUOpIndicesSafe F := by
    exact uop_indices_safe_apply_right
      (uop_indices_safe_apply_right
        (uop_indices_safe_apply_left hSafe))
  rcases hQ with hForall | hExists
  · subst Q
    have hInnerBool :
        __smtx_typeof
            (__eo_to_smt_exists (eoListOfTerms xs)
              (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool :=
      (quant_uop_inner_exists_bool_of_non_none
        (Term.UOp UserOp.forall) (eoListOfTerms xs) F
        (Or.inl rfl) hLhsNN).1 rfl
    have hBodyBool :
        __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
      have hNotBody :
        __smtx_typeof (SmtTerm.not (__eo_to_smt F)) =
          SmtType.Bool :=
        _root_.eo_to_smt_exists_body_bool_of_bool
          (eoListOfTerms xs) (SmtTerm.not (__eo_to_smt F)) hInnerBool
      exact _root_.smtx_typeof_not_arg_bool _ hNotBody
    have hFNeStuck : F ≠ Term.Stuck :=
      term_ne_stuck_of_eo_to_smt_type_bool hBodyBool
    -- Remaining work: induct over `xs`, using `hBodyBool`, the
    -- `contains_atomic_term` absence theorem for dropped binders, and the
    -- duplicate-erasure lemma for retained binders.
    sorry
  · subst Q
    have hInnerBool :
        __smtx_typeof
            (__eo_to_smt_exists (eoListOfTerms xs) (__eo_to_smt F)) =
          SmtType.Bool :=
      (quant_uop_inner_exists_bool_of_non_none
        (Term.UOp UserOp.exists) (eoListOfTerms xs) F
        (Or.inr rfl) hLhsNN).2 rfl
    have hBodyBool :
        __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
      _root_.eo_to_smt_exists_body_bool_of_bool
        (eoListOfTerms xs) (__eo_to_smt F) hInnerBool
    have hFNeStuck : F ≠ Term.Stuck :=
      term_ne_stuck_of_eo_to_smt_type_bool hBodyBool
    -- Same list induction as the `forall` branch, without the outer
    -- negation encoding.
    sorry
