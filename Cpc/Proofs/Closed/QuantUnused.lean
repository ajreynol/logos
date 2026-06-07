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

private theorem uop_indices_safe_uop1_closed {op : UserOp1} {x : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp1 op x)) :
    native_eo_to_smt_closed x = true := by
  exact native_and_left_eq_true (by
    simpa [NativeEoToSmtUOpIndicesSafe,
      native_eo_to_smt_uop_indices_safe] using h)

private theorem uop_indices_safe_uop1_safe {op : UserOp1} {x : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp1 op x)) :
    NativeEoToSmtUOpIndicesSafe x := by
  exact native_and_right_eq_true (by
    simpa [NativeEoToSmtUOpIndicesSafe,
      native_eo_to_smt_uop_indices_safe] using h)

private theorem uop_indices_safe_uop2_closed_left {op : UserOp2}
    {x y : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp2 op x y)) :
    native_eo_to_smt_closed x = true := by
  have hClosedBoth :
      native_and (native_eo_to_smt_closed x) (native_eo_to_smt_closed y) =
        true :=
    native_and_left_eq_true (by
      simpa [NativeEoToSmtUOpIndicesSafe,
        native_eo_to_smt_uop_indices_safe] using h)
  exact native_and_left_eq_true hClosedBoth

private theorem uop_indices_safe_uop2_closed_right {op : UserOp2}
    {x y : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp2 op x y)) :
    native_eo_to_smt_closed y = true := by
  have hClosedBoth :
      native_and (native_eo_to_smt_closed x) (native_eo_to_smt_closed y) =
        true :=
    native_and_left_eq_true (by
      simpa [NativeEoToSmtUOpIndicesSafe,
        native_eo_to_smt_uop_indices_safe] using h)
  exact native_and_right_eq_true hClosedBoth

private theorem uop_indices_safe_uop2_safe_left {op : UserOp2}
    {x y : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp2 op x y)) :
    NativeEoToSmtUOpIndicesSafe x := by
  have hSafeBoth :
      native_and (native_eo_to_smt_uop_indices_safe x)
          (native_eo_to_smt_uop_indices_safe y) =
        true :=
    native_and_right_eq_true (by
      simpa [NativeEoToSmtUOpIndicesSafe,
        native_eo_to_smt_uop_indices_safe] using h)
  exact native_and_left_eq_true hSafeBoth

private theorem uop_indices_safe_uop2_safe_right {op : UserOp2}
    {x y : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp2 op x y)) :
    NativeEoToSmtUOpIndicesSafe y := by
  have hSafeBoth :
      native_and (native_eo_to_smt_uop_indices_safe x)
          (native_eo_to_smt_uop_indices_safe y) =
        true :=
    native_and_right_eq_true (by
      simpa [NativeEoToSmtUOpIndicesSafe,
        native_eo_to_smt_uop_indices_safe] using h)
  exact native_and_right_eq_true hSafeBoth

private theorem uop_indices_safe_uop3_closed_left {op : UserOp3}
    {x y z : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp3 op x y z)) :
    native_eo_to_smt_closed x = true := by
  have hClosedAll :
      native_and
          (native_and (native_eo_to_smt_closed x)
            (native_eo_to_smt_closed y))
          (native_eo_to_smt_closed z) =
        true :=
    native_and_left_eq_true (by
      simpa [NativeEoToSmtUOpIndicesSafe,
        native_eo_to_smt_uop_indices_safe] using h)
  exact native_and_left_eq_true (native_and_left_eq_true hClosedAll)

private theorem uop_indices_safe_uop3_closed_middle {op : UserOp3}
    {x y z : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp3 op x y z)) :
    native_eo_to_smt_closed y = true := by
  have hClosedAll :
      native_and
          (native_and (native_eo_to_smt_closed x)
            (native_eo_to_smt_closed y))
          (native_eo_to_smt_closed z) =
        true :=
    native_and_left_eq_true (by
      simpa [NativeEoToSmtUOpIndicesSafe,
        native_eo_to_smt_uop_indices_safe] using h)
  exact native_and_right_eq_true (native_and_left_eq_true hClosedAll)

private theorem uop_indices_safe_uop3_closed_right {op : UserOp3}
    {x y z : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp3 op x y z)) :
    native_eo_to_smt_closed z = true := by
  have hClosedAll :
      native_and
          (native_and (native_eo_to_smt_closed x)
            (native_eo_to_smt_closed y))
          (native_eo_to_smt_closed z) =
        true :=
    native_and_left_eq_true (by
      simpa [NativeEoToSmtUOpIndicesSafe,
        native_eo_to_smt_uop_indices_safe] using h)
  exact native_and_right_eq_true hClosedAll

private theorem uop_indices_safe_uop3_safe_left {op : UserOp3}
    {x y z : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp3 op x y z)) :
    NativeEoToSmtUOpIndicesSafe x := by
  have hSafeAll :
      native_and
          (native_and (native_eo_to_smt_uop_indices_safe x)
            (native_eo_to_smt_uop_indices_safe y))
          (native_eo_to_smt_uop_indices_safe z) =
        true :=
    native_and_right_eq_true (by
      simpa [NativeEoToSmtUOpIndicesSafe,
        native_eo_to_smt_uop_indices_safe] using h)
  exact native_and_left_eq_true (native_and_left_eq_true hSafeAll)

private theorem uop_indices_safe_uop3_safe_middle {op : UserOp3}
    {x y z : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp3 op x y z)) :
    NativeEoToSmtUOpIndicesSafe y := by
  have hSafeAll :
      native_and
          (native_and (native_eo_to_smt_uop_indices_safe x)
            (native_eo_to_smt_uop_indices_safe y))
          (native_eo_to_smt_uop_indices_safe z) =
        true :=
    native_and_right_eq_true (by
      simpa [NativeEoToSmtUOpIndicesSafe,
        native_eo_to_smt_uop_indices_safe] using h)
  exact native_and_right_eq_true (native_and_left_eq_true hSafeAll)

private theorem uop_indices_safe_uop3_safe_right {op : UserOp3}
    {x y z : Term}
    (h : NativeEoToSmtUOpIndicesSafe (Term.UOp3 op x y z)) :
    NativeEoToSmtUOpIndicesSafe z := by
  have hSafeAll :
      native_and
          (native_and (native_eo_to_smt_uop_indices_safe x)
            (native_eo_to_smt_uop_indices_safe y))
          (native_eo_to_smt_uop_indices_safe z) =
        true :=
    native_and_right_eq_true (by
      simpa [NativeEoToSmtUOpIndicesSafe,
        native_eo_to_smt_uop_indices_safe] using h)
  exact native_and_right_eq_true hSafeAll

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

private theorem eo_to_smt_type_eq_of_top_valid_local
    {T U : Term}
    (hValid : eo_type_valid T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  cases T
  case UOp op =>
    cases op
    case RegLan =>
      have hUReg : __eo_to_smt_type U = SmtType.RegLan := by
        simpa [__eo_to_smt_type] using hEq.symm
      exact (TranslationProofs.eo_to_smt_type_eq_reglan hUReg).symm
    all_goals
      exact TranslationProofs.eo_to_smt_type_eq_of_valid_rec
        (by simpa [eo_type_valid] using hValid) hEq
  all_goals
    exact TranslationProofs.eo_to_smt_type_eq_of_valid_rec
      (by simpa [eo_type_valid] using hValid) hEq

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

private theorem model_agrees_on_globals_symm
    {M N : SmtModel}
    (hAgree : model_agrees_on_globals M N) :
    model_agrees_on_globals N M := by
  exact
    ⟨by
      intro s T
      exact (hAgree.1 s T).symm,
    by
      intro fid T U
      exact (hAgree.2 fid T U).symm⟩

private theorem smt_model_key_ne_of_smt_var_key_ne
    {s1 s2 : native_String} {T1 T2 : SmtType}
    (hNe : (s1, T1) ≠ (s2, T2)) :
    ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) ≠
      { isVar := true, name := s2, ty := T2 } := by
  intro hKey
  cases hKey
  exact hNe rfl

private theorem smtx_model_eval_var_eq_push_of_ne
    (M : SmtModel) (s0 s : native_String) (T0 T : SmtType)
    (v : SmtValue)
    (hNe : (s, T) ≠ (s0, T0)) :
    __smtx_model_eval (native_model_push M s0 T0 v) (SmtTerm.Var s T) =
      __smtx_model_eval M (SmtTerm.Var s T) := by
  have hKey :
      ({ isVar := true, name := s, ty := T } : SmtModelKey) ≠
        { isVar := true, name := s0, ty := T0 } :=
    smt_model_key_ne_of_smt_var_key_ne hNe
  simp [__smtx_model_eval, native_model_var_lookup, native_model_push, hKey]

private def SmtTermAvoidsVar
    (s0 : native_String) (T0 : SmtType) : SmtTerm -> Prop
  | SmtTerm.None => True
  | SmtTerm.Boolean _ => True
  | SmtTerm.Numeral _ => True
  | SmtTerm.Rational _ => True
  | SmtTerm.String _ => True
  | SmtTerm.Binary _ _ => True
  | SmtTerm.Apply f x =>
      SmtTermAvoidsVar s0 T0 f ∧ SmtTermAvoidsVar s0 T0 x
  | SmtTerm.Var s T => (s, T) ≠ (s0, T0)
  | SmtTerm.ite c t e =>
      SmtTermAvoidsVar s0 T0 c ∧ SmtTermAvoidsVar s0 T0 t ∧
        SmtTermAvoidsVar s0 T0 e
  | SmtTerm.eq x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.exists s T body =>
      (s, T) = (s0, T0) ∨ SmtTermAvoidsVar s0 T0 body
  | SmtTerm.forall s T body =>
      (s, T) = (s0, T0) ∨ SmtTermAvoidsVar s0 T0 body
  | SmtTerm.choice_nth s T body _ =>
      (s, T) = (s0, T0) ∨ SmtTermAvoidsVar s0 T0 body
  | SmtTerm.map_diff x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.DtCons _ _ _ => True
  | SmtTerm.DtSel _ _ _ _ => True
  | SmtTerm.DtTester _ _ _ => True
  | SmtTerm.UConst _ _ => True
  | SmtTerm.not x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.or x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.and x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.imp x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.xor x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm._at_purify x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.plus x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.neg x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.mult x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.lt x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.leq x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.gt x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.geq x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.to_real x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.to_int x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.is_int x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.abs x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.uneg x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.div x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.mod x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.multmult x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.divisible x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.int_pow2 x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.int_log2 x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.div_total x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.mod_total x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.multmult_total x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.select x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.store x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.concat x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.extract x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.repeat x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvnot x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.bvand x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvor x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvnand x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvnor x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvxor x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvxnor x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvcomp x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvneg x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.bvadd x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvmul x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvudiv x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvurem x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvsub x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvsdiv x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvsrem x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvsmod x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvult x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvule x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvugt x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvuge x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvslt x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvsle x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvsgt x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvsge x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvshl x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvlshr x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvashr x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.zero_extend x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.sign_extend x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.rotate_left x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.rotate_right x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvuaddo x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvnego x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.bvsaddo x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvumulo x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvsmulo x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvusubo x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvssubo x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.bvsdivo x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.seq_empty _ => True
  | SmtTerm.str_len x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.str_concat x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.str_substr x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.str_contains x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.str_replace x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.str_indexof x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.str_at x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.str_prefixof x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.str_suffixof x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.str_rev x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.str_update x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.str_to_lower x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.str_to_upper x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.str_to_code x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.str_from_code x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.str_is_digit x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.str_to_int x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.str_from_int x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.str_lt x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.str_leq x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.str_replace_all x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.str_replace_re x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.str_replace_re_all x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.str_indexof_re x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.re_allchar => True
  | SmtTerm.re_none => True
  | SmtTerm.re_all => True
  | SmtTerm.str_to_re x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.re_mult x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.re_plus x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.re_exp x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.re_opt x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.re_comp x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.re_range x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.re_concat x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.re_inter x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.re_union x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.re_diff x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.re_loop x y z =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y ∧
        SmtTermAvoidsVar s0 T0 z
  | SmtTerm.str_in_re x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.seq_unit x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.seq_nth x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.set_empty _ => True
  | SmtTerm.set_singleton x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.set_union x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.set_inter x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.set_minus x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.set_member x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.set_subset x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.qdiv x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.qdiv_total x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.int_to_bv x y =>
      SmtTermAvoidsVar s0 T0 x ∧ SmtTermAvoidsVar s0 T0 y
  | SmtTerm.ubv_to_int x => SmtTermAvoidsVar s0 T0 x
  | SmtTerm.sbv_to_int x => SmtTermAvoidsVar s0 T0 x

private theorem nativeEvalTChoiceNthAux_eq_push_of_avoids_below
    (root : SmtTerm)
    (hRec :
      ∀ {t : SmtTerm} {M' : SmtModel} {s0 : native_String}
          {T0 : SmtType} {v' : SmtValue},
        sizeOf t < sizeOf root ->
          SmtTermAvoidsVar s0 T0 t ->
            __smtx_model_eval (native_model_push M' s0 T0 v') t =
              __smtx_model_eval M' t) :
    ∀ {n : native_Nat} {s : native_String} {T : SmtType}
        {body : SmtTerm} {M : SmtModel} {s0 : native_String}
        {T0 : SmtType} {v : SmtValue},
      sizeOf body < sizeOf root ->
        ((s, T) = (s0, T0) ∨ SmtTermAvoidsVar s0 T0 body) ->
          nativeEvalTChoiceNthAux (native_model_push M s0 T0 v) s T body n =
            nativeEvalTChoiceNthAux M s T body n
  | native_nat_zero, s, T, body, M, s0, T0, v, hBodyLt, hAvoid =>
      by
        simp [nativeEvalTChoiceNthAux]
        exact native_eval_tchoice_eq_of_body_eval_eq (fun w =>
          by
            rcases hAvoid with hShadow | hAvoidBody
            · cases hShadow
              simpa [native_model_push_same]
            · by_cases hShadow : (s, T) = (s0, T0)
              · cases hShadow
                simpa [native_model_push_same]
              · have hKey :
                    ({ isVar := true, name := s0, ty := T0 } : SmtModelKey) ≠
                      { isVar := true, name := s, ty := T } := by
                  exact smt_model_key_ne_of_smt_var_key_ne
                    (by intro h; exact hShadow h.symm)
                have hEval :=
                  hRec (t := body) (M' := native_model_push M s T w)
                    (s0 := s0) (T0 := T0) (v' := v)
                    hBodyLt hAvoidBody
                simpa [native_model_push_comm M s0 s T0 T v w hKey]
                  using hEval)
  | native_nat_succ n, s, T, body, M, s0, T0, v, hBodyLt, hAvoid =>
      by
        have hChoiceEq :
            native_eval_tchoice (native_model_push M s0 T0 v) s T body =
              native_eval_tchoice M s T body := by
          simpa [nativeEvalTChoiceNthAux] using
            nativeEvalTChoiceNthAux_eq_push_of_avoids_below root hRec
              (n := native_nat_zero) (s := s) (T := T) (body := body)
              (M := M) (s0 := s0) (T0 := T0) (v := v)
              hBodyLt hAvoid
        rcases hAvoid with hShadow | hAvoidBody
        · cases hShadow
          cases body <;> simp [nativeEvalTChoiceNthAux,
            native_model_push_same] at *
          rename_i s' T' body'
          exact congrArg
            (fun q =>
              nativeEvalTChoiceNthAux (native_model_push M s T q)
                s' T' body' n)
            hChoiceEq
        · by_cases hShadow : (s, T) = (s0, T0)
          · cases hShadow
            cases body <;> simp [nativeEvalTChoiceNthAux,
              native_model_push_same] at *
            rename_i s' T' body'
            exact congrArg
              (fun q =>
                nativeEvalTChoiceNthAux (native_model_push M s T q)
                  s' T' body' n)
              hChoiceEq
          · have hKey :
                ({ isVar := true, name := s0, ty := T0 } : SmtModelKey) ≠
                  { isVar := true, name := s, ty := T } := by
              exact smt_model_key_ne_of_smt_var_key_ne
                (by intro h; exact hShadow h.symm)
            cases body <;> simp [nativeEvalTChoiceNthAux, hChoiceEq]
            rename_i s' T' body'
            have hBody'Lt : sizeOf body' < sizeOf root := by
              simp at hBodyLt
              omega
            have hAvoid' :
                (s', T') = (s0, T0) ∨ SmtTermAvoidsVar s0 T0 body' := by
              simpa [SmtTermAvoidsVar] using hAvoidBody
            have hEval :=
              nativeEvalTChoiceNthAux_eq_push_of_avoids_below root hRec
                (n := n) (s := s') (T := T') (body := body')
                (M := native_model_push M s T
                  (native_eval_tchoice M s T (SmtTerm.exists s' T' body')))
                (s0 := s0) (T0 := T0) (v := v)
                hBody'Lt hAvoid'
            simpa [nativeEvalTChoiceNthAux, hChoiceEq,
              native_model_push_comm M s0 s T0 T v
                (native_eval_tchoice M s T (SmtTerm.exists s' T' body'))
                hKey] using hEval

private theorem smtx_model_eval_eq_push_of_avoids_lt
    (n : Nat) {t : SmtTerm} {M : SmtModel} {s0 : native_String}
    {T0 : SmtType} {v : SmtValue}
    (hLt : sizeOf t < n)
    (hAvoid : SmtTermAvoidsVar s0 T0 t) :
    __smtx_model_eval (native_model_push M s0 T0 v) t =
      __smtx_model_eval M t := by
  cases n with
  | zero =>
      omega
  | succ n =>
      let hAgree : model_agrees_on_env [] (native_model_push M s0 T0 v) M :=
        model_agrees_on_env_nil_of_globals
          (model_agrees_on_globals_symm
            (model_agrees_on_globals_push M s0 T0 v))
      let hRec :
          ∀ {u : SmtTerm} {M' : SmtModel} {s' : native_String}
              {T' : SmtType} {v' : SmtValue},
            sizeOf u < sizeOf t ->
              SmtTermAvoidsVar s' T' u ->
                __smtx_model_eval (native_model_push M' s' T' v') u =
                  __smtx_model_eval M' u :=
        fun {u M' s' T' v'} hULt hAvoid' =>
          smtx_model_eval_eq_push_of_avoids_lt
            n (t := u) (M := M') (s0 := s') (T0 := T') (v := v')
            (by omega) hAvoid'
      let hEvalSame :
          ∀ u : SmtTerm,
              SmtTermAvoidsVar s0 T0 u ->
                sizeOf u < sizeOf t ->
                  __smtx_model_eval (native_model_push M s0 T0 v) u =
                    __smtx_model_eval M u :=
        fun u hAvoid' hULt =>
          hRec hULt hAvoid'
      cases t <;> simp [SmtTermAvoidsVar] at hAvoid ⊢
      case Var s T =>
        have hPair : (s, T) ≠ (s0, T0) := by
          intro hEq
          injection hEq with hs hT
          exact hAvoid hs hT
        exact smtx_model_eval_var_eq_push_of_ne M s0 s T0 T v hPair
      case UConst s T =>
        exact smtx_model_eval_uconst_eq_of_env hAgree
      case Apply f x =>
        exact smtx_model_eval_apply_eq_of_env hAgree
          (hRec (by simp; omega) hAvoid.1)
          (hRec (by simp; omega) hAvoid.2)
      case «exists» s T body =>
        exact smtx_model_eval_exists_eq_of_body_eval_eq (fun w =>
          by
            rcases hAvoid with hShadow | hAvoidBody
            · rcases hShadow with ⟨hs, hT⟩
              cases hs
              cases hT
              simpa [native_model_push_same]
            · by_cases hShadow : (s, T) = (s0, T0)
              · cases hShadow
                simpa [native_model_push_same]
              · have hKey :
                    ({ isVar := true, name := s0, ty := T0 } : SmtModelKey) ≠
                      { isVar := true, name := s, ty := T } := by
                  exact smt_model_key_ne_of_smt_var_key_ne
                    (by intro h; exact hShadow h.symm)
                have hEval :=
                  hRec (u := body) (M' := native_model_push M s T w)
                    (s' := s0) (T' := T0) (v' := v)
                    (by simp; omega) hAvoidBody
                simpa [native_model_push_comm M s0 s T0 T v w hKey]
                  using hEval)
      case «forall» s T body =>
        exact smtx_model_eval_forall_eq_of_body_eval_eq (fun w =>
          by
            rcases hAvoid with hShadow | hAvoidBody
            · rcases hShadow with ⟨hs, hT⟩
              cases hs
              cases hT
              simpa [native_model_push_same]
            · by_cases hShadow : (s, T) = (s0, T0)
              · cases hShadow
                simpa [native_model_push_same]
              · have hKey :
                    ({ isVar := true, name := s0, ty := T0 } : SmtModelKey) ≠
                      { isVar := true, name := s, ty := T } := by
                  exact smt_model_key_ne_of_smt_var_key_ne
                    (by intro h; exact hShadow h.symm)
                have hEval :=
                  hRec (u := body) (M' := native_model_push M s T w)
                    (s' := s0) (T' := T0) (v' := v)
                    (by simp; omega) hAvoidBody
                simpa [native_model_push_comm M s0 s T0 T v w hKey]
                  using hEval)
      case choice_nth s T body k =>
        rw [smtx_model_eval_choice_nth_eq_aux
            (native_model_push M s0 T0 v) s T body k,
          smtx_model_eval_choice_nth_eq_aux M s T body k]
        exact nativeEvalTChoiceNthAux_eq_push_of_avoids_below
          (SmtTerm.choice_nth s T body k) hRec
          (by simp; omega)
          (by
            rcases hAvoid with hShadow | hAvoidBody
            · rcases hShadow with ⟨hs, hT⟩
              exact Or.inl (by cases hs; cases hT; rfl)
            · exact Or.inr hAvoidBody)
      case not x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case _at_purify x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case to_real x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case to_int x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case is_int x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case abs x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case uneg x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case int_pow2 x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case int_log2 x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case bvnot x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case bvneg x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case bvnego x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case str_len x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case str_rev x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case str_to_lower x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case str_to_upper x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case str_to_code x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case str_from_code x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case str_is_digit x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case str_to_int x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case str_from_int x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case str_to_re x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case re_mult x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case re_plus x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case re_opt x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case re_comp x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case seq_unit x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case set_singleton x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case ubv_to_int x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      case sbv_to_int x =>
        simp [__smtx_model_eval, hRec (by simp) hAvoid]
      all_goals try
        simp [__smtx_model_eval, hAgree.globals.1,
          smtx_model_eval_apply_eq_of_globals hAgree.globals,
          smtx_seq_nth_eq_of_globals hAgree.globals]
      all_goals try
        rw [hEvalSame _ hAvoid.1 (by simp; omega),
          hEvalSame _ hAvoid.2 (by simp; omega)]
      all_goals try
        rw [hEvalSame _ hAvoid.1 (by simp; omega),
          hEvalSame _ hAvoid.2.1 (by simp; omega),
          hEvalSame _ hAvoid.2.2 (by simp; omega)]
      all_goals try
        simp [hAgree.globals.1, hAgree.globals.2,
          smtx_model_eval_apply_eq_of_globals hAgree.globals,
          smtx_seq_nth_eq_of_globals hAgree.globals,
          smtx_model_eval_dt_sel_eq_of_globals hAgree.globals]
termination_by n
decreasing_by
  all_goals omega

private theorem smtx_model_eval_eq_push_of_avoids
    {t : SmtTerm} {M : SmtModel} {s0 : native_String} {T0 : SmtType}
    {v : SmtValue}
    (hAvoid : SmtTermAvoidsVar s0 T0 t) :
    __smtx_model_eval (native_model_push M s0 T0 v) t =
      __smtx_model_eval M t := by
  exact smtx_model_eval_eq_push_of_avoids_lt
    (sizeOf t + 1) (by omega) hAvoid

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

private theorem smtExistsOfBinders_cons_congr_typed
    (M : SmtModel) (b : QuantBinder) (t u : SmtTerm) :
    (∀ v : SmtValue,
      __smtx_typeof_value v = b.2 ->
      __smtx_value_canonical_bool v = true ->
        __smtx_model_eval (native_model_push M b.1 b.2 v) t =
          __smtx_model_eval (native_model_push M b.1 b.2 v) u) ->
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
        simpa [hEval v hv hCan] using hT⟩
    · intro hSat
      rcases hSat with ⟨v, hv, hCan, hU⟩
      exact ⟨v, hv, hCan, by
        simpa [hEval v hv hCan] using hU⟩
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

private theorem smtExistsOfBinders_binder_wf_of_mem
    (body : SmtTerm) :
    ∀ {bs : List QuantBinder} {b : QuantBinder},
      b ∈ bs ->
      __smtx_typeof (smtExistsOfBinders bs body) = SmtType.Bool ->
      __smtx_type_wf b.2 = true
  | [], b, hMem, _hTy => by
      simp at hMem
  | c :: cs, b, hMem, hTy => by
      simp at hMem
      rcases hMem with hEq | hMem
      · subst b
        exact smtExistsOfBinders_head_wf_of_cons_bool c cs body hTy
      · exact smtExistsOfBinders_binder_wf_of_mem body hMem
          (smtExistsOfBinders_tail_bool_of_cons_bool c cs body hTy)

private theorem smtExistsOfBinders_quantTermBinder_wf_of_mem
    {xs : List Term} {body : SmtTerm} {t : Term}
    (ht : t ∈ xs)
    (hTy :
      __smtx_typeof (smtExistsOfBinders (xs.map quantTermBinder) body) =
        SmtType.Bool) :
    __smtx_type_wf (quantTermBinder t).2 = true :=
  smtExistsOfBinders_binder_wf_of_mem body
    (b := quantTermBinder t) (bs := xs.map quantTermBinder)
    (List.mem_map_of_mem (f := quantTermBinder) ht) hTy

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

private theorem quantUnusedVarsList_all
    {xs : List Term} {F : Term}
    (hxs : ∀ t ∈ xs, IsQuantVarTerm t) :
    ∀ t ∈ quantUnusedVarsList xs F, IsQuantVarTerm t := by
  induction xs with
  | nil =>
      intro t ht
      simp [quantUnusedVarsList] at ht
  | cons x xs ih =>
      intro t ht
      have hTail : ∀ u ∈ xs, IsQuantVarTerm u := by
        intro u hu
        exact hxs u (by simp [hu])
      by_cases hC : __contains_atomic_term F x = Term.Boolean true
      · simp [quantUnusedVarsList, hC] at ht
        rcases ht with ht | ht
        · subst t
          exact hxs x (by simp)
        · exact ih hTail t (List.mem_of_mem_erase ht)
      · simp [quantUnusedVarsList, hC] at ht
        exact ih hTail t ht

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

private theorem mk_quant_uop_nil_eq
    (op : UserOp) (F : Term) :
    __mk_quant (Term.UOp op) Term.__eo_List_nil F = F := by
  cases F <;> simp [__mk_quant]

private theorem mk_quant_uop_cons_eoListOfTerms_eq
    (op : UserOp) (x : Term) (xs : List Term) (F : Term)
    (hF : F ≠ Term.Stuck) :
    __mk_quant (Term.UOp op) (eoListOfTerms (x :: xs)) F =
      Term.Apply (Term.Apply (Term.UOp op) (eoListOfTerms (x :: xs))) F := by
  cases F <;> simp [eoListOfTerms, __mk_quant] at hF ⊢

private theorem eo_to_smt_mk_quant_exists_eoListOfTerms
    (xs : List Term) (F : Term)
    (hF : F ≠ Term.Stuck)
    (hxs : ∀ t ∈ xs, IsQuantVarTerm t) :
    __eo_to_smt
        (__mk_quant (Term.UOp UserOp.exists) (eoListOfTerms xs) F) =
      smtExistsOfBinders (xs.map quantTermBinder) (__eo_to_smt F) := by
  cases xs with
  | nil =>
      change
        __eo_to_smt
            (__mk_quant (Term.UOp UserOp.exists) Term.__eo_List_nil F) =
          smtExistsOfBinders ([] : List QuantBinder) (__eo_to_smt F)
      rw [mk_quant_uop_nil_eq]
      simp [smtExistsOfBinders]
  | cons x xs =>
      have hAll : ∀ t ∈ x :: xs, IsQuantVarTerm t := hxs
      have hxNonNil :
          eoListOfTerms (x :: xs) ≠ Term.__eo_List_nil := by
        simp [eoListOfTerms]
      rw [mk_quant_uop_cons_eoListOfTerms_eq UserOp.exists x xs F hF]
      rw [eo_to_smt_exists_quant_eq (eoListOfTerms (x :: xs)) F hxNonNil]
      exact eo_to_smt_exists_eoListOfTerms_binders (x :: xs)
        (__eo_to_smt F) hAll

private theorem smtx_model_eval_mk_quant_forall_eoListOfTerms
    (M : SmtModel) (hM : model_total_typed M)
    (F : Term)
    (hF : F ≠ Term.Stuck)
    (hBodyBool : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (xs : List Term)
    (hxs : ∀ t ∈ xs, IsQuantVarTerm t) :
    __smtx_model_eval M
        (__eo_to_smt
          (__mk_quant (Term.UOp UserOp.forall) (eoListOfTerms xs) F)) =
      __smtx_model_eval M
        (SmtTerm.not
          (smtExistsOfBinders (xs.map quantTermBinder)
            (SmtTerm.not (__eo_to_smt F)))) := by
  cases xs with
  | nil =>
      change
        __smtx_model_eval M
            (__eo_to_smt
              (__mk_quant (Term.UOp UserOp.forall) Term.__eo_List_nil F)) =
          __smtx_model_eval M
            (SmtTerm.not
              (smtExistsOfBinders ([] : List QuantBinder)
                (SmtTerm.not (__eo_to_smt F))))
      rw [mk_quant_uop_nil_eq]
      simp [smtExistsOfBinders]
      exact (smtx_model_eval_not_not_of_bool M hM (__eo_to_smt F)
        hBodyBool).symm
  | cons x xs =>
      have hAll : ∀ t ∈ x :: xs, IsQuantVarTerm t := hxs
      have hxNonNil :
          eoListOfTerms (x :: xs) ≠ Term.__eo_List_nil := by
        simp [eoListOfTerms]
      rw [mk_quant_uop_cons_eoListOfTerms_eq UserOp.forall x xs F hF]
      rw [eo_to_smt_forall_eq (eoListOfTerms (x :: xs)) F hxNonNil]
      rw [eo_to_smt_exists_eoListOfTerms_binders (x :: xs)
        (SmtTerm.not (__eo_to_smt F)) hAll]

private theorem smtExistsOfBinders_quantUnusedVarsList_eval :
    ∀ (xs : List Term) (M : SmtModel),
      model_total_typed M ->
      (F : Term) ->
      (body : SmtTerm) ->
      (∀ t ∈ xs, IsQuantVarTerm t) ->
      __smtx_typeof (smtExistsOfBinders (xs.map quantTermBinder) body) =
        SmtType.Bool ->
      (∀ t ∈ xs,
        __contains_atomic_term F t = Term.Boolean true ∨
          __contains_atomic_term F t = Term.Boolean false) ->
      (∀ (M0 : SmtModel) (t : Term) (v : SmtValue),
        t ∈ xs ->
        IsQuantVarTerm t ->
        __contains_atomic_term F t = Term.Boolean false ->
        __smtx_model_eval
            (native_model_push M0 (quantTermBinder t).1
              (quantTermBinder t).2 v)
            body =
          __smtx_model_eval M0 body) ->
      __smtx_model_eval M
          (smtExistsOfBinders (xs.map quantTermBinder) body) =
        __smtx_model_eval M
          (smtExistsOfBinders
            ((quantUnusedVarsList xs F).map quantTermBinder) body)
  | [], M, _hM, F, body, _hxs, _hTy, _hContains, _hInv => by
      simp [quantUnusedVarsList]
  | x :: xs, M, hM, F, body, hxs, hTy, hContains, hInv => by
      have hx : IsQuantVarTerm x := hxs x (by simp)
      have hxsTail : ∀ t ∈ xs, IsQuantVarTerm t := by
        intro t ht
        exact hxs t (by simp [ht])
      have hTyTail :
          __smtx_typeof
              (smtExistsOfBinders (xs.map quantTermBinder) body) =
            SmtType.Bool :=
        smtExistsOfBinders_tail_bool_of_cons_bool
          (quantTermBinder x) (xs.map quantTermBinder) body hTy
      have hContainsTail :
          ∀ t ∈ xs,
            __contains_atomic_term F t = Term.Boolean true ∨
              __contains_atomic_term F t = Term.Boolean false := by
        intro t ht
        exact hContains t (by simp [ht])
      have hInvTail :
          ∀ (M0 : SmtModel) (t : Term) (v : SmtValue),
            t ∈ xs ->
            IsQuantVarTerm t ->
            __contains_atomic_term F t = Term.Boolean false ->
            __smtx_model_eval
                (native_model_push M0 (quantTermBinder t).1
                  (quantTermBinder t).2 v)
                body =
              __smtx_model_eval M0 body := by
        intro M0 t v ht hQt hNo
        exact hInv M0 t v (by simp [ht]) hQt hNo
      rcases hContains x (by simp) with hCx | hCx
      · have hWF :
            __smtx_type_wf (quantTermBinder x).2 = true :=
          smtExistsOfBinders_head_wf_of_cons_bool
            (quantTermBinder x) (xs.map quantTermBinder) body hTy
        have hLift :
            __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder x :: xs.map quantTermBinder) body) =
              __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder x ::
                    (quantUnusedVarsList xs F).map quantTermBinder) body) := by
          exact smtExistsOfBinders_cons_congr_typed M
            (quantTermBinder x)
            (smtExistsOfBinders (xs.map quantTermBinder) body)
            (smtExistsOfBinders
              ((quantUnusedVarsList xs F).map quantTermBinder) body)
            (fun v hvTy hvCanon => by
              have hvCanon' : __smtx_value_canonical v := by
                simpa [Smtm.__smtx_value_canonical] using hvCanon
              exact
                smtExistsOfBinders_quantUnusedVarsList_eval xs
                  (native_model_push M (quantTermBinder x).1
                    (quantTermBinder x).2 v)
                  (model_total_typed_push hM (quantTermBinder x).1
                    (quantTermBinder x).2 v hWF hvTy hvCanon')
                  F body hxsTail hTyTail hContainsTail hInvTail)
        have hErase :=
          smtExistsOfBinders_duplicate_erase_term M x
            (quantUnusedVarsList xs F) body
        simpa [quantUnusedVarsList, hCx] using hLift.trans hErase
      · have hDrop :
            __smtx_model_eval M
                (smtExistsOfBinders
                  (quantTermBinder x :: xs.map quantTermBinder) body) =
              __smtx_model_eval M
                (smtExistsOfBinders (xs.map quantTermBinder) body) := by
          exact smtExistsOfBinders_unused_head M hM
            (quantTermBinder x) (xs.map quantTermBinder) body hTy
            (fun M0 v => hInv M0 x v (by simp) hx hCx)
        have hTail :=
          smtExistsOfBinders_quantUnusedVarsList_eval xs M hM F body
            hxsTail hTyTail hContainsTail hInvTail
        simpa [quantUnusedVarsList, hCx] using hDrop.trans hTail

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

private theorem EoSmtVarEnv_eoListOfTerms_no_stuck :
    ∀ {env : List Term} {vars : List SmtVarKey},
      EoSmtVarEnv (eoListOfTerms env) vars ->
        ∀ x, x ∈ env -> x ≠ Term.Stuck
  | [], vars, _hEnv => by
      intro x hx
      simp at hx
  | x :: xs, vars, hEnv => by
      change
        EoSmtVarEnv
          (Term.Apply (Term.Apply Term.__eo_List_cons x) (eoListOfTerms xs))
          vars at hEnv
      cases hEnv with
      | cons hTail =>
          intro z hz
          cases hz with
          | head =>
              simp
          | tail _ hzTail =>
              exact EoSmtVarEnv_eoListOfTerms_no_stuck hTail z hzTail

private theorem EoSmtVarEnvPerm_eoListOfTerms_no_stuck
    {env : List Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm (eoListOfTerms env) vars) :
    ∀ x, x ∈ env -> x ≠ Term.Stuck := by
  rcases hEnv with ⟨exactVars, hExact, _hEquiv⟩
  exact EoSmtVarEnv_eoListOfTerms_no_stuck hExact

private theorem EoSmtVarEnvPerm_eoListOfTerms_concat_rev
    {xs env : List Term} {binderVars vars : List SmtVarKey}
    (hVs : EoSmtVarEnv (eoListOfTerms xs) binderVars)
    (hEnv : EoSmtVarEnvPerm (eoListOfTerms env) vars) :
    EoSmtVarEnvPerm (eoListOfTerms (xs ++ env))
      (binderVars.reverse ++ vars) := by
  simpa [eoListOfTerms_concat] using
    EoSmtVarEnvPerm.concat_rev
      (vs := eoListOfTerms xs) (env := eoListOfTerms env)
      hVs hEnv

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

private theorem smtTermClosedIn_weaken_nil
    {vars : List SmtVarKey} {t : SmtTerm}
    (h : SmtTermClosedIn [] t) :
    SmtTermClosedIn vars t := by
  exact SmtTermClosedIn.mono
    (t := t) (vars := []) (vars' := vars)
    (by intro s T hMem; cases hMem)
    h

private theorem smtTermClosedIn_eo_to_smt_set_insert_native_using
    (root : Term)
    (hRec :
      ∀ {u : Term} {env' : List Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf root ->
          EoSmtVarEnvPerm (eoListOfTerms env') vars' ->
            native_eo_to_smt_closed_rec u env' = true ->
              NativeEoToSmtUOpIndicesSafe u ->
                SmtTermClosedIn vars' (__eo_to_smt u)) :
    ∀ {xs : Term} {base : SmtTerm} {env : List Term}
        {vars : List SmtVarKey},
      sizeOf xs < sizeOf root ->
        EoSmtVarEnvPerm (eoListOfTerms env) vars ->
          native_eo_to_smt_closed_rec xs env = true ->
            NativeEoToSmtUOpIndicesSafe xs ->
              SmtTermClosedIn vars base ->
                SmtTermClosedIn vars (__eo_to_smt_set_insert xs base)
  | Term.__eo_List_nil, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      hBase =>
      by
        simpa [__eo_to_smt_set_insert] using hBase
  | Term.Apply f tail, base, env, vars, hLt, hEnv, hClosed, hSafe, hBase =>
      by
        cases f <;> try trivial
        case Apply g head =>
          cases g <;> try trivial
          case __eo_List_cons =>
            have hOuter :
                native_and
                    (native_eo_to_smt_closed_rec
                      (Term.Apply Term.__eo_List_cons head) env)
                    (native_eo_to_smt_closed_rec tail env) =
                  true := by
              simpa [native_eo_to_smt_closed_rec] using hClosed
            have hInner :
                native_and
                    (native_eo_to_smt_closed_rec Term.__eo_List_cons env)
                    (native_eo_to_smt_closed_rec head env) =
                  true := by
              simpa [native_eo_to_smt_closed_rec] using
                native_and_left_eq_true hOuter
            have hHeadClosed :
                native_eo_to_smt_closed_rec head env = true :=
              native_and_right_eq_true hInner
            have hTailClosed :
                native_eo_to_smt_closed_rec tail env = true :=
              native_and_right_eq_true hOuter
            have hHeadSafe :
                NativeEoToSmtUOpIndicesSafe head :=
              uop_indices_safe_apply_right
                (uop_indices_safe_apply_left hSafe)
            have hTailSafe :
                NativeEoToSmtUOpIndicesSafe tail :=
              uop_indices_safe_apply_right hSafe
            have hHeadLt : sizeOf head < sizeOf root := by
              simp at hLt
              omega
            have hTailLt : sizeOf tail < sizeOf root := by
              simp at hLt
              omega
            change SmtTermClosedIn vars
              (SmtTerm.set_union
                (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail base))
            exact
              ⟨hRec hHeadLt hEnv hHeadClosed hHeadSafe,
                smtTermClosedIn_eo_to_smt_set_insert_native_using root hRec
                  hTailLt hEnv hTailClosed hTailSafe hBase⟩
  | Term.UOp _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.UOp1 _ _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.UOp2 _ _ _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.UOp3 _ _ _ _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.__eo_List, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.__eo_List_cons, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.Bool, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.Boolean _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.Numeral _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.Rational _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.String _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.Binary _ _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.Type, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.Stuck, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.FunType, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.Var _ _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.DatatypeType _ _, base, env, vars, _hLt, _hEnv, _hClosed,
      _hSafe, _hBase => by trivial
  | Term.DatatypeTypeRef _, base, env, vars, _hLt, _hEnv, _hClosed,
      _hSafe, _hBase => by trivial
  | Term.DtcAppType _ _, base, env, vars, _hLt, _hEnv, _hClosed,
      _hSafe, _hBase => by trivial
  | Term.DtCons _ _ _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.DtSel _ _ _ _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.USort _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial
  | Term.UConst _ _, base, env, vars, _hLt, _hEnv, _hClosed, _hSafe,
      _hBase => by trivial

private theorem smtTermClosedIn_eo_to_smt_set_insert_apply_native_using
    (root : Term)
    (hRec :
      ∀ {u : Term} {env' : List Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf root ->
          EoSmtVarEnvPerm (eoListOfTerms env') vars' ->
            native_eo_to_smt_closed_rec u env' = true ->
              NativeEoToSmtUOpIndicesSafe u ->
                SmtTermClosedIn vars' (__eo_to_smt u))
    {xs x : Term} {env : List Term} {vars : List SmtVarKey}
    (hXsLt : sizeOf xs < sizeOf root)
    (hEnv : EoSmtVarEnvPerm (eoListOfTerms env) vars)
    (hClosed : native_eo_to_smt_closed_rec xs env = true)
    (hSafe : NativeEoToSmtUOpIndicesSafe xs)
    (hBase : SmtTermClosedIn vars (__eo_to_smt x)) :
    SmtTermClosedIn vars
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x)) := by
  cases xs
  case __eo_List_nil =>
    trivial
  all_goals
    change SmtTermClosedIn vars
      (__eo_to_smt_set_insert _ (__eo_to_smt x))
    exact smtTermClosedIn_eo_to_smt_set_insert_native_using
      root hRec hXsLt hEnv hClosed hSafe hBase

private theorem smtTermClosedIn_eo_to_smt_distinct_pairs_native_using
    (root : Term)
    (hRec :
      ∀ {u : Term} {env' : List Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf root ->
          EoSmtVarEnvPerm (eoListOfTerms env') vars' ->
            native_eo_to_smt_closed_rec u env' = true ->
              NativeEoToSmtUOpIndicesSafe u ->
                SmtTermClosedIn vars' (__eo_to_smt u)) :
    ∀ {xs : Term} {s : SmtTerm} {env : List Term}
        {vars : List SmtVarKey},
      SmtTermClosedIn vars s ->
        sizeOf xs < sizeOf root ->
          EoSmtVarEnvPerm (eoListOfTerms env) vars ->
            native_eo_to_smt_closed_rec xs env = true ->
              NativeEoToSmtUOpIndicesSafe xs ->
                SmtTermClosedIn vars (__eo_to_smt_distinct_pairs s xs)
  | Term.Apply f tail, s, env, vars, hs, hLt, hEnv, hClosed, hSafe =>
      by
        cases f <;> try trivial
        case UOp op =>
          cases op <;> trivial
        case Apply g head =>
          cases g <;> try trivial
          case UOp op =>
            cases op <;> try trivial
            case _at__at_TypedList_cons =>
              have hOuter :
                  native_and
                      (native_eo_to_smt_closed_rec
                        (Term.Apply
                          (Term.UOp UserOp._at__at_TypedList_cons)
                          head)
                        env)
                      (native_eo_to_smt_closed_rec tail env) =
                    true := by
                simpa [native_eo_to_smt_closed_rec] using hClosed
              have hInner :
                  native_and
                      (native_eo_to_smt_closed_rec
                        (Term.UOp UserOp._at__at_TypedList_cons) env)
                      (native_eo_to_smt_closed_rec head env) =
                    true := by
                simpa [native_eo_to_smt_closed_rec] using
                  native_and_left_eq_true hOuter
              have hHeadClosed :
                  native_eo_to_smt_closed_rec head env = true :=
                native_and_right_eq_true hInner
              have hTailClosed :
                  native_eo_to_smt_closed_rec tail env = true :=
                native_and_right_eq_true hOuter
              have hHeadSafe :
                  NativeEoToSmtUOpIndicesSafe head :=
                uop_indices_safe_apply_right
                  (uop_indices_safe_apply_left hSafe)
              have hTailSafe :
                  NativeEoToSmtUOpIndicesSafe tail :=
                uop_indices_safe_apply_right hSafe
              have hHeadLt : sizeOf head < sizeOf root := by
                simp at hLt
                omega
              have hTailLt : sizeOf tail < sizeOf root := by
                simp at hLt
                omega
              change SmtTermClosedIn vars
                (SmtTerm.and
                  (SmtTerm.not (SmtTerm.eq s (__eo_to_smt head)))
                  (__eo_to_smt_distinct_pairs s tail))
              exact
                ⟨⟨hs, hRec hHeadLt hEnv hHeadClosed hHeadSafe⟩,
                  smtTermClosedIn_eo_to_smt_distinct_pairs_native_using
                    root hRec hs hTailLt hEnv hTailClosed hTailSafe⟩
  | Term.UOp _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.UOp1 _ _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.UOp2 _ _ _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.UOp3 _ _ _ _, s, env, vars, hs, _hLt, _hEnv, _hClosed,
      _hSafe => by
      trivial
  | Term.__eo_List, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.__eo_List_nil, s, env, vars, hs, _hLt, _hEnv, _hClosed,
      _hSafe => by
      trivial
  | Term.__eo_List_cons, s, env, vars, hs, _hLt, _hEnv, _hClosed,
      _hSafe => by
      trivial
  | Term.Bool, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.Boolean _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.Numeral _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.Rational _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.String _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.Binary _ _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.Type, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.Stuck, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.FunType, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.Var _ _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.DatatypeType _ _, s, env, vars, hs, _hLt, _hEnv, _hClosed,
      _hSafe => by
      trivial
  | Term.DatatypeTypeRef _, s, env, vars, hs, _hLt, _hEnv, _hClosed,
      _hSafe => by
      trivial
  | Term.DtcAppType _ _, s, env, vars, hs, _hLt, _hEnv, _hClosed,
      _hSafe => by
      trivial
  | Term.DtCons _ _ _, s, env, vars, hs, _hLt, _hEnv, _hClosed,
      _hSafe => by
      trivial
  | Term.DtSel _ _ _ _, s, env, vars, hs, _hLt, _hEnv, _hClosed,
      _hSafe => by
      trivial
  | Term.USort _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.UConst _ _, s, env, vars, hs, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial

private theorem smtTermClosedIn_eo_to_smt_distinct_native_using
    (root : Term)
    (hRec :
      ∀ {u : Term} {env' : List Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf root ->
          EoSmtVarEnvPerm (eoListOfTerms env') vars' ->
            native_eo_to_smt_closed_rec u env' = true ->
              NativeEoToSmtUOpIndicesSafe u ->
                SmtTermClosedIn vars' (__eo_to_smt u)) :
    ∀ {xs : Term} {env : List Term} {vars : List SmtVarKey},
      sizeOf xs < sizeOf root ->
        EoSmtVarEnvPerm (eoListOfTerms env) vars ->
          native_eo_to_smt_closed_rec xs env = true ->
            NativeEoToSmtUOpIndicesSafe xs ->
              SmtTermClosedIn vars (__eo_to_smt_distinct xs)
  | Term.Apply f tail, env, vars, hLt, hEnv, hClosed, hSafe =>
      by
        cases f <;> try trivial
        case UOp op =>
          cases op <;> trivial
        case Apply g head =>
          cases g <;> try trivial
          case UOp op =>
            cases op <;> try trivial
            case _at__at_TypedList_cons =>
              have hOuter :
                  native_and
                      (native_eo_to_smt_closed_rec
                        (Term.Apply
                          (Term.UOp UserOp._at__at_TypedList_cons)
                          head)
                        env)
                      (native_eo_to_smt_closed_rec tail env) =
                    true := by
                simpa [native_eo_to_smt_closed_rec] using hClosed
              have hInner :
                  native_and
                      (native_eo_to_smt_closed_rec
                        (Term.UOp UserOp._at__at_TypedList_cons) env)
                      (native_eo_to_smt_closed_rec head env) =
                    true := by
                simpa [native_eo_to_smt_closed_rec] using
                  native_and_left_eq_true hOuter
              have hHeadClosed :
                  native_eo_to_smt_closed_rec head env = true :=
                native_and_right_eq_true hInner
              have hTailClosed :
                  native_eo_to_smt_closed_rec tail env = true :=
                native_and_right_eq_true hOuter
              have hHeadSafe :
                  NativeEoToSmtUOpIndicesSafe head :=
                uop_indices_safe_apply_right
                  (uop_indices_safe_apply_left hSafe)
              have hTailSafe :
                  NativeEoToSmtUOpIndicesSafe tail :=
                uop_indices_safe_apply_right hSafe
              have hHeadLt : sizeOf head < sizeOf root := by
                simp at hLt
                omega
              have hTailLt : sizeOf tail < sizeOf root := by
                simp at hLt
                omega
              have hHead :
                  SmtTermClosedIn vars (__eo_to_smt head) :=
                hRec hHeadLt hEnv hHeadClosed hHeadSafe
              change SmtTermClosedIn vars
                (SmtTerm.and
                  (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail)
                  (__eo_to_smt_distinct tail))
              exact
                ⟨smtTermClosedIn_eo_to_smt_distinct_pairs_native_using
                    root hRec hHead hTailLt hEnv hTailClosed hTailSafe,
                  smtTermClosedIn_eo_to_smt_distinct_native_using
                    root hRec hTailLt hEnv hTailClosed hTailSafe⟩
  | Term.UOp _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by trivial
  | Term.UOp1 _ _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.UOp2 _ _ _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.UOp3 _ _ _ _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.__eo_List, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by trivial
  | Term.__eo_List_nil, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.__eo_List_cons, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.Bool, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by trivial
  | Term.Boolean _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.Numeral _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by trivial
  | Term.Rational _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.String _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by trivial
  | Term.Binary _ _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.Type, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by trivial
  | Term.Stuck, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by trivial
  | Term.FunType, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by trivial
  | Term.Var _ _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by trivial
  | Term.DatatypeType _ _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.DatatypeTypeRef _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.DtcAppType _ _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.DtCons _ _ _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.DtSel _ _ _ _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial
  | Term.USort _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by trivial
  | Term.UConst _ _, env, vars, _hLt, _hEnv, _hClosed, _hSafe => by
      trivial

private theorem smtTermClosedIn_eo_to_smt_distinct_apply_native_using
    (root : Term)
    (hRec :
      ∀ {u : Term} {env' : List Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf root ->
          EoSmtVarEnvPerm (eoListOfTerms env') vars' ->
            native_eo_to_smt_closed_rec u env' = true ->
              NativeEoToSmtUOpIndicesSafe u ->
                SmtTermClosedIn vars' (__eo_to_smt u))
    {xs : Term} {env : List Term} {vars : List SmtVarKey}
    (hXsLt : sizeOf xs < sizeOf root)
    (hEnv : EoSmtVarEnvPerm (eoListOfTerms env) vars)
    (hClosed : native_eo_to_smt_closed_rec xs env = true)
    (hSafe : NativeEoToSmtUOpIndicesSafe xs) :
    SmtTermClosedIn vars
      (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs)) := by
  change SmtTermClosedIn vars
    (native_ite
      (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs))
  cases native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None <;>
    try trivial
  simpa [native_ite] using
    smtTermClosedIn_eo_to_smt_distinct_native_using
      root hRec hXsLt hEnv hClosed hSafe

private theorem smtTermClosedIn_eo_to_smt_apply_generic_native_using
    (root : Term)
    (hRec :
      ∀ {u : Term} {env' : List Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf root ->
          EoSmtVarEnvPerm (eoListOfTerms env') vars' ->
            native_eo_to_smt_closed_rec u env' = true ->
              NativeEoToSmtUOpIndicesSafe u ->
                SmtTermClosedIn vars' (__eo_to_smt u))
    {f x : Term} {env : List Term} {vars : List SmtVarKey}
    (hFLt : sizeOf f < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (hEnv : EoSmtVarEnvPerm (eoListOfTerms env) vars)
    (hSplit :
      native_and
          (native_eo_to_smt_closed_rec f env)
          (native_eo_to_smt_closed_rec x env) =
        true)
    (hSafe : NativeEoToSmtUOpIndicesSafe (Term.Apply f x))
    (hSmt :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) :
    SmtTermClosedIn vars (__eo_to_smt (Term.Apply f x)) := by
  have hfClosed :
      native_eo_to_smt_closed_rec f env = true :=
    native_and_left_eq_true hSplit
  have hxClosed :
      native_eo_to_smt_closed_rec x env = true :=
    native_and_right_eq_true hSplit
  have hfSafe : NativeEoToSmtUOpIndicesSafe f :=
    uop_indices_safe_apply_left hSafe
  have hxSafe : NativeEoToSmtUOpIndicesSafe x :=
    uop_indices_safe_apply_right hSafe
  rw [hSmt]
  exact
    ⟨hRec hFLt hEnv hfClosed hfSafe,
      hRec hXLt hEnv hxClosed hxSafe⟩

private theorem smtTermClosedIn_eo_to_smt_apply_uop_native_using
    {op : UserOp} {x : Term} {env : List Term}
    {vars : List SmtVarKey}
    (hRec :
      ∀ {u : Term} {env' : List Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf (Term.Apply (Term.UOp op) x) ->
          EoSmtVarEnvPerm (eoListOfTerms env') vars' ->
            native_eo_to_smt_closed_rec u env' = true ->
              NativeEoToSmtUOpIndicesSafe u ->
                SmtTermClosedIn vars' (__eo_to_smt u))
    (hEnv : EoSmtVarEnvPerm (eoListOfTerms env) vars)
    (hClosed :
      native_eo_to_smt_closed_rec (Term.Apply (Term.UOp op) x) env =
        true)
    (hSafe : NativeEoToSmtUOpIndicesSafe (Term.Apply (Term.UOp op) x)) :
    SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp op) x)) := by
  have hSplit :
      native_and
          (native_eo_to_smt_closed_rec (Term.UOp op) env)
          (native_eo_to_smt_closed_rec x env) =
        true := by
    simpa [native_eo_to_smt_closed_rec] using hClosed
  have hxClosedNative :
      native_eo_to_smt_closed_rec x env = true :=
    native_and_right_eq_true hSplit
  have hxSafe : NativeEoToSmtUOpIndicesSafe x :=
    uop_indices_safe_apply_right hSafe
  have hxClosedSmt :
      SmtTermClosedIn vars (__eo_to_smt x) :=
    hRec (u := x) (by simp <;> try omega) hEnv hxClosedNative hxSafe
  cases op
  case not =>
    exact smtTermClosedIn_eo_to_smt_not hxClosedSmt
  case distinct =>
    exact
      smtTermClosedIn_eo_to_smt_distinct_apply_native_using
        (Term.Apply (Term.UOp UserOp.distinct) x)
        (fun {u} {env'} {vars'} hULt hEnv' hClosed' hSafe' =>
          hRec (u := u) hULt hEnv' hClosed' hSafe')
        (by simp <;> try omega) hEnv hxClosedNative hxSafe
  case to_real =>
    exact smtTermClosedIn_eo_to_smt_to_real hxClosedSmt
  case to_int =>
    exact smtTermClosedIn_eo_to_smt_to_int hxClosedSmt
  case is_int =>
    exact smtTermClosedIn_eo_to_smt_is_int hxClosedSmt
  case abs =>
    exact smtTermClosedIn_eo_to_smt_abs hxClosedSmt
  case __eoo_neg_2 =>
    exact smtTermClosedIn_eo_to_smt_uneg hxClosedSmt
  case int_pow2 =>
    exact smtTermClosedIn_eo_to_smt_int_pow2 hxClosedSmt
  case int_log2 =>
    exact smtTermClosedIn_eo_to_smt_int_log2 hxClosedSmt
  case int_ispow2 =>
    exact smtTermClosedIn_eo_to_smt_int_ispow2 hxClosedSmt
  case _at_int_div_by_zero =>
    exact smtTermClosedIn_eo_to_smt_int_div_by_zero hxClosedSmt
  case _at_mod_by_zero =>
    exact smtTermClosedIn_eo_to_smt_mod_by_zero hxClosedSmt
  case _at_bvsize =>
    exact smtTermClosedIn_eo_to_smt_bvsize vars x
  case bvnot =>
    exact smtTermClosedIn_eo_to_smt_bvnot hxClosedSmt
  case bvneg =>
    exact smtTermClosedIn_eo_to_smt_bvneg hxClosedSmt
  case bvnego =>
    exact smtTermClosedIn_eo_to_smt_bvnego hxClosedSmt
  case bvredand =>
    exact smtTermClosedIn_eo_to_smt_bvredand hxClosedSmt
  case bvredor =>
    exact smtTermClosedIn_eo_to_smt_bvredor hxClosedSmt
  case str_len =>
    exact smtTermClosedIn_eo_to_smt_str_len hxClosedSmt
  case str_rev =>
    exact smtTermClosedIn_eo_to_smt_str_rev hxClosedSmt
  case str_to_lower =>
    exact smtTermClosedIn_eo_to_smt_str_to_lower hxClosedSmt
  case str_to_upper =>
    exact smtTermClosedIn_eo_to_smt_str_to_upper hxClosedSmt
  case str_to_code =>
    exact smtTermClosedIn_eo_to_smt_str_to_code hxClosedSmt
  case str_from_code =>
    exact smtTermClosedIn_eo_to_smt_str_from_code hxClosedSmt
  case str_is_digit =>
    exact smtTermClosedIn_eo_to_smt_str_is_digit hxClosedSmt
  case str_to_int =>
    exact smtTermClosedIn_eo_to_smt_str_to_int hxClosedSmt
  case str_from_int =>
    exact smtTermClosedIn_eo_to_smt_str_from_int hxClosedSmt
  case str_to_re =>
    exact smtTermClosedIn_eo_to_smt_str_to_re hxClosedSmt
  case re_mult =>
    exact smtTermClosedIn_eo_to_smt_re_mult hxClosedSmt
  case re_plus =>
    exact smtTermClosedIn_eo_to_smt_re_plus hxClosedSmt
  case re_opt =>
    exact smtTermClosedIn_eo_to_smt_re_opt hxClosedSmt
  case re_comp =>
    exact smtTermClosedIn_eo_to_smt_re_comp hxClosedSmt
  case seq_unit =>
    exact smtTermClosedIn_eo_to_smt_seq_unit hxClosedSmt
  case set_singleton =>
    exact smtTermClosedIn_eo_to_smt_set_singleton hxClosedSmt
  case set_choose =>
    exact smtTermClosedIn_eo_to_smt_set_choose hxClosedSmt
  case set_is_empty =>
    exact smtTermClosedIn_eo_to_smt_set_is_empty hxClosedSmt
  case set_is_singleton =>
    exact smtTermClosedIn_eo_to_smt_set_is_singleton hxClosedSmt
  case _at_div_by_zero =>
    exact smtTermClosedIn_eo_to_smt_qdiv_by_zero hxClosedSmt
  case ubv_to_int =>
    exact smtTermClosedIn_eo_to_smt_ubv_to_int hxClosedSmt
  case sbv_to_int =>
    exact smtTermClosedIn_eo_to_smt_sbv_to_int hxClosedSmt
  all_goals
    exact
      smtTermClosedIn_eo_to_smt_apply_generic_native_using
        (Term.Apply (Term.UOp _) x)
        (fun {u} {env'} {vars'} hULt hEnv' hClosed' hSafe' =>
          hRec (u := u) hULt hEnv' hClosed' hSafe')
        (by simp <;> try omega) (by simp <;> try omega) hEnv
        (by simpa [native_eo_to_smt_closed_rec] using hClosed)
        hSafe (by rfl)

private theorem smtTermClosedIn_eo_to_smt_apply_uop1_native_using
    {op : UserOp1} {idx x : Term} {env : List Term}
    {vars : List SmtVarKey}
    (hRec :
      ∀ {u : Term} {env' : List Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf (Term.Apply (Term.UOp1 op idx) x) ->
          EoSmtVarEnvPerm (eoListOfTerms env') vars' ->
            native_eo_to_smt_closed_rec u env' = true ->
              NativeEoToSmtUOpIndicesSafe u ->
                SmtTermClosedIn vars' (__eo_to_smt u))
    (hEnv : EoSmtVarEnvPerm (eoListOfTerms env) vars)
    (hClosed :
      native_eo_to_smt_closed_rec (Term.Apply (Term.UOp1 op idx) x) env =
        true)
    (hSafe : NativeEoToSmtUOpIndicesSafe (Term.Apply (Term.UOp1 op idx) x)) :
    SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x)) := by
  have hSplit :
      native_and
          (native_eo_to_smt_closed_rec (Term.UOp1 op idx) env)
          (native_eo_to_smt_closed_rec x env) =
        true := by
    simpa [native_eo_to_smt_closed_rec] using hClosed
  have hxClosedNative :
      native_eo_to_smt_closed_rec x env = true :=
    native_and_right_eq_true hSplit
  have hIndexedSafe : NativeEoToSmtUOpIndicesSafe (Term.UOp1 op idx) :=
    uop_indices_safe_apply_left hSafe
  have hxSafe : NativeEoToSmtUOpIndicesSafe x :=
    uop_indices_safe_apply_right hSafe
  have hIdxClosed0 :
      SmtTermClosedIn [] (__eo_to_smt idx) :=
    hRec (u := idx) (env' := []) (vars' := [])
      (by simp <;> try omega)
      (by
        simpa [eoListOfTerms] using
          EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
      (by
        simpa [native_eo_to_smt_closed] using
          uop_indices_safe_uop1_closed hIndexedSafe)
      (uop_indices_safe_uop1_safe hIndexedSafe)
  have hIdxClosedSmt :
      SmtTermClosedIn vars (__eo_to_smt idx) :=
    smtTermClosedIn_weaken_nil hIdxClosed0
  have hxClosedSmt :
      SmtTermClosedIn vars (__eo_to_smt x) :=
    hRec (u := x) (by simp <;> try omega) hEnv hxClosedNative hxSafe
  cases op
  case «repeat» =>
    exact smtTermClosedIn_eo_to_smt_repeat hIdxClosedSmt hxClosedSmt
  case zero_extend =>
    exact smtTermClosedIn_eo_to_smt_zero_extend hIdxClosedSmt hxClosedSmt
  case sign_extend =>
    exact smtTermClosedIn_eo_to_smt_sign_extend hIdxClosedSmt hxClosedSmt
  case rotate_left =>
    exact smtTermClosedIn_eo_to_smt_rotate_left hIdxClosedSmt hxClosedSmt
  case rotate_right =>
    exact smtTermClosedIn_eo_to_smt_rotate_right hIdxClosedSmt hxClosedSmt
  case _at_bit =>
    exact smtTermClosedIn_eo_to_smt_at_bit hIdxClosedSmt hxClosedSmt
  case re_exp =>
    exact smtTermClosedIn_eo_to_smt_re_exp hIdxClosedSmt hxClosedSmt
  case _at_strings_stoi_result =>
    exact smtTermClosedIn_eo_to_smt_strings_stoi_result
      hIdxClosedSmt hxClosedSmt
  case _at_strings_itos_result =>
    exact smtTermClosedIn_eo_to_smt_strings_itos_result
      hIdxClosedSmt hxClosedSmt
  case «is» =>
    exact smtTermClosedIn_eo_to_smt_is hIdxClosedSmt hxClosedSmt
  case tuple_select =>
    exact smtTermClosedIn_eo_to_smt_tuple_select hIdxClosedSmt hxClosedSmt
  case int_to_bv =>
    exact smtTermClosedIn_eo_to_smt_int_to_bv hIdxClosedSmt hxClosedSmt
  all_goals
    exact
      smtTermClosedIn_eo_to_smt_apply_generic_native_using
        (Term.Apply (Term.UOp1 _ idx) x)
        (fun {u} {env'} {vars'} hULt hEnv' hClosed' hSafe' =>
          hRec (u := u) hULt hEnv' hClosed' hSafe')
        (by simp <;> try omega) (by simp <;> try omega) hEnv
        (by simpa [native_eo_to_smt_closed_rec] using hClosed)
        hSafe (by rfl)

private theorem smtTermClosedIn_eo_to_smt_apply_uop2_native_using
    {op : UserOp2} {idx1 idx2 x : Term} {env : List Term}
    {vars : List SmtVarKey}
    (hRec :
      ∀ {u : Term} {env' : List Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf (Term.Apply (Term.UOp2 op idx1 idx2) x) ->
          EoSmtVarEnvPerm (eoListOfTerms env') vars' ->
            native_eo_to_smt_closed_rec u env' = true ->
              NativeEoToSmtUOpIndicesSafe u ->
                SmtTermClosedIn vars' (__eo_to_smt u))
    (hEnv : EoSmtVarEnvPerm (eoListOfTerms env) vars)
    (hClosed :
      native_eo_to_smt_closed_rec
          (Term.Apply (Term.UOp2 op idx1 idx2) x) env =
        true)
    (hSafe :
      NativeEoToSmtUOpIndicesSafe
        (Term.Apply (Term.UOp2 op idx1 idx2) x)) :
    SmtTermClosedIn vars
      (__eo_to_smt (Term.Apply (Term.UOp2 op idx1 idx2) x)) := by
  have hSplit :
      native_and
          (native_eo_to_smt_closed_rec (Term.UOp2 op idx1 idx2) env)
          (native_eo_to_smt_closed_rec x env) =
        true := by
    simpa [native_eo_to_smt_closed_rec] using hClosed
  have hxClosedNative :
      native_eo_to_smt_closed_rec x env = true :=
    native_and_right_eq_true hSplit
  have hIndexedSafe :
      NativeEoToSmtUOpIndicesSafe (Term.UOp2 op idx1 idx2) :=
    uop_indices_safe_apply_left hSafe
  have hxSafe : NativeEoToSmtUOpIndicesSafe x :=
    uop_indices_safe_apply_right hSafe
  have hIdx1Closed0 :
      SmtTermClosedIn [] (__eo_to_smt idx1) :=
    hRec (u := idx1) (env' := []) (vars' := [])
      (by simp <;> try omega)
      (by
        simpa [eoListOfTerms] using
          EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
      (by
        simpa [native_eo_to_smt_closed] using
          uop_indices_safe_uop2_closed_left hIndexedSafe)
      (uop_indices_safe_uop2_safe_left hIndexedSafe)
  have hIdx2Closed0 :
      SmtTermClosedIn [] (__eo_to_smt idx2) :=
    hRec (u := idx2) (env' := []) (vars' := [])
      (by simp <;> try omega)
      (by
        simpa [eoListOfTerms] using
          EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
      (by
        simpa [native_eo_to_smt_closed] using
          uop_indices_safe_uop2_closed_right hIndexedSafe)
      (uop_indices_safe_uop2_safe_right hIndexedSafe)
  have hIdx1ClosedSmt :
      SmtTermClosedIn vars (__eo_to_smt idx1) :=
    smtTermClosedIn_weaken_nil hIdx1Closed0
  have hIdx2ClosedSmt :
      SmtTermClosedIn vars (__eo_to_smt idx2) :=
    smtTermClosedIn_weaken_nil hIdx2Closed0
  have hxClosedSmt :
      SmtTermClosedIn vars (__eo_to_smt x) :=
    hRec (u := x) (by simp <;> try omega) hEnv hxClosedNative hxSafe
  cases op
  case extract =>
    exact smtTermClosedIn_eo_to_smt_extract
      hIdx1ClosedSmt hIdx2ClosedSmt hxClosedSmt
  case re_loop =>
    exact smtTermClosedIn_eo_to_smt_re_loop
      hIdx1ClosedSmt hIdx2ClosedSmt hxClosedSmt
  all_goals
    exact
      smtTermClosedIn_eo_to_smt_apply_generic_native_using
        (Term.Apply (Term.UOp2 _ idx1 idx2) x)
        (fun {u} {env'} {vars'} hULt hEnv' hClosed' hSafe' =>
          hRec (u := u) hULt hEnv' hClosed' hSafe')
        (by simp <;> try omega) (by simp <;> try omega) hEnv
        (by simpa [native_eo_to_smt_closed_rec] using hClosed)
        hSafe (by rfl)

private theorem native_eo_to_smt_closed_rec_apply_apply_uop_split
    {op : UserOp} {z y : Term} {env : List Term}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hClosed :
      native_eo_to_smt_closed_rec
          (Term.Apply (Term.Apply (Term.UOp op) z) y) env =
        true) :
    native_and
        (native_eo_to_smt_closed_rec (Term.Apply (Term.UOp op) z) env)
        (native_eo_to_smt_closed_rec y env) =
      true := by
  cases op <;> simp [native_eo_to_smt_closed_rec] at hClosed hNotForall hNotExists ⊢ <;> assumption

private theorem smtTermClosedIn_of_native_eo_to_smt_closed_rec_safe_lt
    (n : Nat) {t : Term} {env : List Term} {vars : List SmtVarKey}
    (hLt : sizeOf t < n)
    (hEnv : EoSmtVarEnvPerm (eoListOfTerms env) vars)
    (hClosed : native_eo_to_smt_closed_rec t env = true)
    (hSafe : NativeEoToSmtUOpIndicesSafe t) :
    SmtTermClosedIn vars (__eo_to_smt t) := by
  cases n with
  | zero =>
      omega
  | succ n =>
      let hRec :
          ∀ {u : Term} {env' : List Term} {vars' : List SmtVarKey},
            sizeOf u < sizeOf t ->
              EoSmtVarEnvPerm (eoListOfTerms env') vars' ->
                native_eo_to_smt_closed_rec u env' = true ->
                  NativeEoToSmtUOpIndicesSafe u ->
                    SmtTermClosedIn vars' (__eo_to_smt u) :=
        fun {u} {env'} {vars'} hULt hEnv' hClosed' hSafe' =>
          smtTermClosedIn_of_native_eo_to_smt_closed_rec_safe_lt
            n (t := u) (env := env') (vars := vars')
            (by omega) hEnv' hClosed' hSafe'
      cases t
      case Stuck =>
        simp [native_eo_to_smt_closed_rec] at hClosed
      case Var name T =>
        cases name <;> try trivial
        case String s =>
          have hNoStuck :=
            EoSmtVarEnvPerm_eoListOfTerms_no_stuck hEnv
          have hEoClosed :
              __eo_is_closed_rec (Term.Var (Term.String s) T)
                  (eoListOfTerms env) =
                Term.Boolean true :=
            eo_is_closed_rec_var_eoListOfTerms_of_mem hNoStuck
              (by simpa [native_eo_to_smt_closed_rec] using hClosed)
          exact smtTermClosedIn_eo_to_smt_var_of_closed_rec_perm
            hEnv hEoClosed
      case UOp op =>
        exact smtTermClosedIn_eo_to_smt_uop vars op
      case UOp1 op x =>
        have hxClosed0 :
            SmtTermClosedIn [] (__eo_to_smt x) :=
          hRec (u := x) (env' := []) (vars' := [])
            (by simp; omega)
            (by
              simpa [eoListOfTerms] using
                EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
            (by
              simpa [native_eo_to_smt_closed] using
                uop_indices_safe_uop1_closed hSafe)
            (uop_indices_safe_uop1_safe hSafe)
        have hxClosed : SmtTermClosedIn vars (__eo_to_smt x) :=
          smtTermClosedIn_weaken_nil hxClosed0
        cases op <;> try trivial
        case _at_purify =>
          exact smtTermClosedIn_eo_to_smt_purify hxClosed
        case seq_empty =>
          exact smtTermClosedIn_eo_to_smt_seq_empty vars x
        case _at_strings_stoi_non_digit =>
          exact smtTermClosedIn_eo_to_smt_strings_stoi_non_digit hxClosed
        case set_empty =>
          exact smtTermClosedIn_eo_to_smt_set_empty vars x
      case UOp2 op x y =>
        have hxClosed0 :
            SmtTermClosedIn [] (__eo_to_smt x) :=
          hRec (u := x) (env' := []) (vars' := [])
            (by simp; omega)
            (by
              simpa [eoListOfTerms] using
                EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
            (by
              simpa [native_eo_to_smt_closed] using
                uop_indices_safe_uop2_closed_left hSafe)
            (uop_indices_safe_uop2_safe_left hSafe)
        have hyClosed0 :
            SmtTermClosedIn [] (__eo_to_smt y) :=
          hRec (u := y) (env' := []) (vars' := [])
            (by simp; omega)
            (by
              simpa [eoListOfTerms] using
                EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
            (by
              simpa [native_eo_to_smt_closed] using
                uop_indices_safe_uop2_closed_right hSafe)
            (uop_indices_safe_uop2_safe_right hSafe)
        have hxClosed : SmtTermClosedIn vars (__eo_to_smt x) :=
          smtTermClosedIn_weaken_nil hxClosed0
        have hyClosed : SmtTermClosedIn vars (__eo_to_smt y) :=
          smtTermClosedIn_weaken_nil hyClosed0
        cases op <;> try trivial
        case _at_array_deq_diff =>
          exact smtTermClosedIn_eo_to_smt_array_deq_diff hxClosed hyClosed
        case _at_bv =>
          exact smtTermClosedIn_eo_to_smt_at_bv vars x y
        case _at_strings_deq_diff =>
          exact smtTermClosedIn_eo_to_smt_strings_deq_diff hxClosed hyClosed
        case _at_sets_deq_diff =>
          exact smtTermClosedIn_eo_to_smt_sets_deq_diff hxClosed hyClosed
        case _at_quantifiers_skolemize =>
          cases x <;> try trivial
          case Apply f body =>
            cases f <;> try trivial
            case Apply g xs =>
              cases g <;> try trivial
              case UOp q =>
                cases q <;> try trivial
                case «forall» =>
                  exact
                    smtTermClosedIn_eo_to_smt_quantifiers_skolemize_forall
                      hxClosed
      case UOp3 op x y z =>
        have hxClosed0 :
            SmtTermClosedIn [] (__eo_to_smt x) :=
          hRec (u := x) (env' := []) (vars' := [])
            (by simp; omega)
            (by
              simpa [eoListOfTerms] using
                EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
            (by
              simpa [native_eo_to_smt_closed] using
                uop_indices_safe_uop3_closed_left hSafe)
            (uop_indices_safe_uop3_safe_left hSafe)
        have hyClosed0 :
            SmtTermClosedIn [] (__eo_to_smt y) :=
          hRec (u := y) (env' := []) (vars' := [])
            (by simp; omega)
            (by
              simpa [eoListOfTerms] using
                EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
            (by
              simpa [native_eo_to_smt_closed] using
                uop_indices_safe_uop3_closed_middle hSafe)
            (uop_indices_safe_uop3_safe_middle hSafe)
        have hzClosed0 :
            SmtTermClosedIn [] (__eo_to_smt z) :=
          hRec (u := z) (env' := []) (vars' := [])
            (by simp; omega)
            (by
              simpa [eoListOfTerms] using
                EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
            (by
              simpa [native_eo_to_smt_closed] using
                uop_indices_safe_uop3_closed_right hSafe)
            (uop_indices_safe_uop3_safe_right hSafe)
        have hxClosed : SmtTermClosedIn vars (__eo_to_smt x) :=
          smtTermClosedIn_weaken_nil hxClosed0
        have hyClosed : SmtTermClosedIn vars (__eo_to_smt y) :=
          smtTermClosedIn_weaken_nil hyClosed0
        have hzClosed : SmtTermClosedIn vars (__eo_to_smt z) :=
          smtTermClosedIn_weaken_nil hzClosed0
        cases op
        case _at_re_unfold_pos_component =>
          apply SmtTermClosedIn.guard_closed (x := x)
          apply SmtTermClosedIn.guard_closed (x := y)
          change SmtTermClosedIn vars
            (native_ite (__eo_to_smt_nat_is_valid z)
              (__eo_to_smt_re_unfold_pos_component
                (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt_nat z))
              SmtTerm.None)
          cases __eo_to_smt_nat_is_valid z
          · simp [native_ite, SmtTermClosedIn]
          · simpa [native_ite] using
              smtTermClosedIn_eo_to_smt_re_unfold_pos_component
                hxClosed hyClosed (__eo_to_smt_nat z)
        case _at_witness_string_length =>
          exact smtTermClosedIn_eo_to_smt_witness_string_length hyClosed
      case Apply f x =>
        cases f
        case Apply g y =>
          cases g
          case UOp op =>
            by_cases hForall : op = UserOp.forall
            · subst op
              cases hList : native_eo_to_smt_term_list y with
              | none =>
                  simp [native_eo_to_smt_closed_rec, hList] at hClosed
              | some xs =>
                  have hyEq :
                      y = eoListOfTerms xs :=
                    native_eo_to_smt_term_list_eq_eoListOfTerms hList
                  subst y
                  exact smtTermClosedIn_eo_to_smt_forall_term_of_env_or_none
                    (vs := eoListOfTerms xs) (body := x) (vars := vars)
                    (by
                      intro binderVars hVs
                      exact hRec (u := x) (env' := xs ++ env)
                        (by simp; omega)
                        (EoSmtVarEnvPerm_eoListOfTerms_concat_rev
                          hVs hEnv)
                        (by
                          simpa [native_eo_to_smt_closed_rec, hList]
                            using hClosed)
                        (uop_indices_safe_apply_right hSafe))
            · by_cases hExists : op = UserOp.exists
              · subst op
                cases hList : native_eo_to_smt_term_list y with
                | none =>
                    simp [native_eo_to_smt_closed_rec, hList] at hClosed
                | some xs =>
                    have hyEq :
                        y = eoListOfTerms xs :=
                      native_eo_to_smt_term_list_eq_eoListOfTerms hList
                    subst y
                    exact smtTermClosedIn_eo_to_smt_exists_term_of_env_or_none
                      (vs := eoListOfTerms xs) (body := x) (vars := vars)
                      (by
                        intro binderVars hVs
                        exact hRec (u := x) (env' := xs ++ env)
                          (by simp; omega)
                          (EoSmtVarEnvPerm_eoListOfTerms_concat_rev
                            hVs hEnv)
                          (by
                            simpa [native_eo_to_smt_closed_rec, hList]
                              using hClosed)
                          (uop_indices_safe_apply_right hSafe))
              ·
                have hClosedSplit :
                    native_and
                        (native_eo_to_smt_closed_rec
                          (Term.Apply (Term.UOp op) y) env)
                        (native_eo_to_smt_closed_rec x env) =
                      true := by
                  cases op <;>
                    simp [native_eo_to_smt_closed_rec] at hClosed hForall hExists ⊢ <;>
                      assumption
                have hfClosedNative :
                    native_eo_to_smt_closed_rec
                      (Term.Apply (Term.UOp op) y) env =
                      true :=
                  native_and_left_eq_true hClosedSplit
                have hxClosedNative :
                    native_eo_to_smt_closed_rec x env = true :=
                  native_and_right_eq_true hClosedSplit
                have hInnerSplit :
                    native_and
                        (native_eo_to_smt_closed_rec (Term.UOp op) env)
                        (native_eo_to_smt_closed_rec y env) =
                      true := by
                  simpa [native_eo_to_smt_closed_rec] using hfClosedNative
                have hyClosedNative :
                    native_eo_to_smt_closed_rec y env = true :=
                  native_and_right_eq_true hInnerSplit
                have hfSafe :
                    NativeEoToSmtUOpIndicesSafe
                      (Term.Apply (Term.UOp op) y) :=
                  uop_indices_safe_apply_left hSafe
                have hySafe : NativeEoToSmtUOpIndicesSafe y :=
                  uop_indices_safe_apply_right hfSafe
                have hxSafe : NativeEoToSmtUOpIndicesSafe x :=
                  uop_indices_safe_apply_right hSafe
                have hfClosedSmt :
                    SmtTermClosedIn vars
                      (__eo_to_smt (Term.Apply (Term.UOp op) y)) :=
                  hRec (u := Term.Apply (Term.UOp op) y)
                    (by simp; omega) hEnv hfClosedNative hfSafe
                have hyClosedSmt :
                    SmtTermClosedIn vars (__eo_to_smt y) :=
                  hRec (u := y) (by simp; omega) hEnv
                    hyClosedNative hySafe
                have hxClosedSmt :
                    SmtTermClosedIn vars (__eo_to_smt x) :=
                  hRec (u := x) (by simp; omega) hEnv
                    hxClosedNative hxSafe
                cases op <;>
                  first
                  | contradiction
                  | exact smtTermClosedIn_eo_to_smt_or
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_and
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_imp
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_xor
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_eq
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_plus
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_neg
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_mult
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_lt
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_leq
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_gt
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_geq
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_div
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_mod
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_multmult
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_divisible
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_div_total
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_mod_total
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_multmult_total
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_select
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_concat
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvand
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvor
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvnand
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvnor
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvxor
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvxnor
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvcomp
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvadd
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvmul
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvudiv
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvurem
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsub
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsdiv
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsrem
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsmod
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvult
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvule
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvugt
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvuge
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvslt
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsle
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsgt
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsge
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvshl
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvlshr
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvashr
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvuaddo
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsaddo
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvumulo
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsmulo
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvusubo
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvssubo
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsdivo
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvultbv
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_bvsltbv
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_from_bools
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_str_concat
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_str_contains
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_str_at
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_str_prefixof
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_str_suffixof
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_str_lt
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_str_leq
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_re_range
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_re_concat
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_re_inter
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_re_union
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_re_diff
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_str_in_re
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_seq_nth
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_strings_num_occur
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_tuple
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_set_union
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_set_inter
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_set_minus
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_set_member
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_set_subset
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_qdiv
                      hyClosedSmt hxClosedSmt
                  | exact smtTermClosedIn_eo_to_smt_qdiv_total
                      hyClosedSmt hxClosedSmt
                  | exact
                      smtTermClosedIn_eo_to_smt_set_insert_apply_native_using
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.set_insert) y)
                          x)
                        (fun {u} {env'} {vars'} hULt hEnv' hClosed'
                            hSafe' =>
                          hRec (u := u) hULt hEnv' hClosed' hSafe')
                        (by simp; omega) hEnv hyClosedNative hySafe
                        hxClosedSmt
                  | (
                      change SmtTermClosedIn vars
                        (SmtTerm.Apply
                          (__eo_to_smt (Term.Apply (Term.UOp _) y))
                          (__eo_to_smt x))
                      exact ⟨hfClosedSmt, hxClosedSmt⟩)
          case UOp1 op a =>
            have hClosedSplit :
                native_and
                    (native_eo_to_smt_closed_rec
                      (Term.Apply (Term.UOp1 op a) y) env)
                    (native_eo_to_smt_closed_rec x env) =
                  true := by
              simpa [native_eo_to_smt_closed_rec] using hClosed
            have hfClosedNative :
                native_eo_to_smt_closed_rec
                  (Term.Apply (Term.UOp1 op a) y) env =
                  true :=
              native_and_left_eq_true hClosedSplit
            have hxClosedNative :
                native_eo_to_smt_closed_rec x env = true :=
              native_and_right_eq_true hClosedSplit
            have hInnerSplit :
                native_and
                    (native_eo_to_smt_closed_rec (Term.UOp1 op a) env)
                    (native_eo_to_smt_closed_rec y env) =
                  true := by
              simpa [native_eo_to_smt_closed_rec] using hfClosedNative
            have hyClosedNative :
                native_eo_to_smt_closed_rec y env = true :=
              native_and_right_eq_true hInnerSplit
            have hIndexedSafe :
                NativeEoToSmtUOpIndicesSafe (Term.UOp1 op a) :=
              uop_indices_safe_apply_left
                (uop_indices_safe_apply_left hSafe)
            have hySafe : NativeEoToSmtUOpIndicesSafe y :=
              uop_indices_safe_apply_right
                (uop_indices_safe_apply_left hSafe)
            have hxSafe : NativeEoToSmtUOpIndicesSafe x :=
              uop_indices_safe_apply_right hSafe
            have haClosed0 :
                SmtTermClosedIn [] (__eo_to_smt a) :=
              hRec (u := a) (env' := []) (vars' := [])
                (by simp; omega)
                (by
                  simpa [eoListOfTerms] using
                    EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
                (by
                  simpa [native_eo_to_smt_closed] using
                    uop_indices_safe_uop1_closed hIndexedSafe)
                (uop_indices_safe_uop1_safe hIndexedSafe)
            have haClosedSmt :
                SmtTermClosedIn vars (__eo_to_smt a) :=
              smtTermClosedIn_weaken_nil haClosed0
            have hyClosedSmt :
                SmtTermClosedIn vars (__eo_to_smt y) :=
              hRec (u := y) (by simp; omega) hEnv
                hyClosedNative hySafe
            have hxClosedSmt :
                SmtTermClosedIn vars (__eo_to_smt x) :=
              hRec (u := x) (by simp; omega) hEnv
                hxClosedNative hxSafe
            cases op
            case update =>
              exact smtTermClosedIn_eo_to_smt_update
                haClosedSmt hyClosedSmt hxClosedSmt
            case tuple_update =>
              exact smtTermClosedIn_eo_to_smt_tuple_update
                haClosedSmt hyClosedSmt hxClosedSmt
            all_goals
              exact
                smtTermClosedIn_eo_to_smt_apply_generic_native_using
                  (Term.Apply
                    (Term.Apply (Term.UOp1 _ a) y) x)
                  (fun {u} {env'} {vars'} hULt hEnv' hClosed'
                      hSafe' =>
                    hRec (u := u) hULt hEnv' hClosed' hSafe')
                  (by simp; omega) (by simp; omega) hEnv
                  (by
                    simpa [native_eo_to_smt_closed_rec] using hClosed)
                  hSafe (by rfl)
          case Apply h z =>
            cases h
            case UOp op =>
              have hClosedSplit :
                  native_and
                      (native_eo_to_smt_closed_rec
                        (Term.Apply
                          (Term.Apply (Term.UOp op) z) y)
                        env)
                      (native_eo_to_smt_closed_rec x env) =
                    true := by
                simpa [native_eo_to_smt_closed_rec] using hClosed
              have hfClosedNative :
                  native_eo_to_smt_closed_rec
                    (Term.Apply
                      (Term.Apply (Term.UOp op) z) y)
                    env =
                    true :=
                native_and_left_eq_true hClosedSplit
              have hxClosedNative :
                  native_eo_to_smt_closed_rec x env = true :=
                native_and_right_eq_true hClosedSplit
              have hxSafe : NativeEoToSmtUOpIndicesSafe x :=
                uop_indices_safe_apply_right hSafe
              have hfSafe :
                  NativeEoToSmtUOpIndicesSafe
                    (Term.Apply
                      (Term.Apply (Term.UOp op) z) y) :=
                uop_indices_safe_apply_left hSafe
              have hfClosedSmt :
                  SmtTermClosedIn vars
                    (__eo_to_smt
                      (Term.Apply
                        (Term.Apply (Term.UOp op) z) y)) :=
                hRec
                  (u := Term.Apply
                    (Term.Apply (Term.UOp op) z) y)
                  (by simp; omega) hEnv hfClosedNative hfSafe
              have hxClosedSmt :
                  SmtTermClosedIn vars (__eo_to_smt x) :=
                hRec (u := x) (by simp; omega) hEnv
                  hxClosedNative hxSafe
              let direct
                  (hNotForall : op ≠ UserOp.forall)
                  (hNotExists : op ≠ UserOp.exists)
                  (hBuilder :
                    SmtTermClosedIn vars (__eo_to_smt z) ->
                      SmtTermClosedIn vars (__eo_to_smt y) ->
                        SmtTermClosedIn vars (__eo_to_smt x) ->
                          SmtTermClosedIn vars
                            (__eo_to_smt
                              (Term.Apply
                                (Term.Apply
                                  (Term.Apply (Term.UOp op) z) y)
                                x))) :
                  SmtTermClosedIn vars
                    (__eo_to_smt
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp op) z) y)
                        x)) := by
                have hMiddleSplit :
                    native_and
                        (native_eo_to_smt_closed_rec
                          (Term.Apply (Term.UOp op) z) env)
                        (native_eo_to_smt_closed_rec y env) =
                      true := by
                  exact
                    native_eo_to_smt_closed_rec_apply_apply_uop_split
                      hNotForall hNotExists hfClosedNative
                have hInnerClosedNative :
                    native_eo_to_smt_closed_rec
                      (Term.Apply (Term.UOp op) z) env =
                      true :=
                  native_and_left_eq_true hMiddleSplit
                have hyClosedNative :
                    native_eo_to_smt_closed_rec y env = true :=
                  native_and_right_eq_true hMiddleSplit
                have hInnerSplit :
                    native_and
                        (native_eo_to_smt_closed_rec (Term.UOp op) env)
                        (native_eo_to_smt_closed_rec z env) =
                      true := by
                  simpa [native_eo_to_smt_closed_rec] using
                    hInnerClosedNative
                have hzClosedNative :
                    native_eo_to_smt_closed_rec z env = true :=
                  native_and_right_eq_true hInnerSplit
                have hzSafe : NativeEoToSmtUOpIndicesSafe z :=
                  uop_indices_safe_apply_right
                    (uop_indices_safe_apply_left
                      (uop_indices_safe_apply_left hSafe))
                have hySafe : NativeEoToSmtUOpIndicesSafe y :=
                  uop_indices_safe_apply_right
                    (uop_indices_safe_apply_left hSafe)
                have hzClosedSmt :
                    SmtTermClosedIn vars (__eo_to_smt z) :=
                  hRec (u := z) (by simp; omega) hEnv
                    hzClosedNative hzSafe
                have hyClosedSmt :
                    SmtTermClosedIn vars (__eo_to_smt y) :=
                  hRec (u := y) (by simp; omega) hEnv
                    hyClosedNative hySafe
                exact hBuilder hzClosedSmt hyClosedSmt hxClosedSmt
              cases op
              case ite =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_ite hz hy hx)
              case store =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_store hz hy hx)
              case bvite =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_bvite hz hy hx)
              case str_substr =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_str_substr hz hy hx)
              case str_replace =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_str_replace hz hy hx)
              case str_indexof =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_str_indexof hz hy hx)
              case str_update =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_str_update hz hy hx)
              case str_replace_all =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_str_replace_all hz hy hx)
              case str_replace_re =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_str_replace_re hz hy hx)
              case str_replace_re_all =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_str_replace_re_all hz hy hx)
              case str_indexof_re =>
                exact direct (by decide) (by decide)
                  (fun hz hy hx =>
                    smtTermClosedIn_eo_to_smt_str_indexof_re hz hy hx)
              all_goals
                change SmtTermClosedIn vars
                  (SmtTerm.Apply
                    (__eo_to_smt
                      (Term.Apply
                        (Term.Apply (Term.UOp _) z) y))
                    (__eo_to_smt x))
                exact ⟨hfClosedSmt, hxClosedSmt⟩
            all_goals
              exact
                smtTermClosedIn_eo_to_smt_apply_generic_native_using
                  (Term.Apply (Term.Apply (Term.Apply _ z) y) x)
                  (fun {u} {env'} {vars'} hULt hEnv' hClosed'
                      hSafe' =>
                    hRec (u := u) hULt hEnv' hClosed' hSafe')
                  (by simp; omega) (by simp; omega) hEnv
                  (by
                    simpa [native_eo_to_smt_closed_rec] using hClosed)
                  hSafe (by rfl)
          all_goals
            exact
              smtTermClosedIn_eo_to_smt_apply_generic_native_using
                (Term.Apply (Term.Apply _ y) x)
                (fun {u} {env'} {vars'} hULt hEnv' hClosed'
                    hSafe' =>
                  hRec (u := u) hULt hEnv' hClosed' hSafe')
                (by simp; omega) (by simp; omega) hEnv
                (by
                  simpa [native_eo_to_smt_closed_rec] using hClosed)
                hSafe (by rfl)
        case UOp op =>
          exact
            smtTermClosedIn_eo_to_smt_apply_uop_native_using
              (fun {u} {env'} {vars'} hULt hEnv' hClosed' hSafe' =>
                hRec (u := u) hULt hEnv' hClosed' hSafe')
              hEnv hClosed hSafe
        case UOp1 op idx =>
          exact
            smtTermClosedIn_eo_to_smt_apply_uop1_native_using
              (fun {u} {env'} {vars'} hULt hEnv' hClosed' hSafe' =>
                hRec (u := u) hULt hEnv' hClosed' hSafe')
              hEnv hClosed hSafe
        case UOp2 op idx1 idx2 =>
          exact
            smtTermClosedIn_eo_to_smt_apply_uop2_native_using
              (fun {u} {env'} {vars'} hULt hEnv' hClosed' hSafe' =>
                hRec (u := u) hULt hEnv' hClosed' hSafe')
              hEnv hClosed hSafe
        all_goals
          exact
            smtTermClosedIn_eo_to_smt_apply_generic_native_using
              (Term.Apply _ x)
              (fun {u} {env'} {vars'} hULt hEnv' hClosed' hSafe' =>
                hRec (u := u) hULt hEnv' hClosed' hSafe')
              (by simp <;> try omega) (by simp <;> try omega) hEnv
              (by
                simpa [native_eo_to_smt_closed_rec] using hClosed)
              hSafe (by rfl)
      case DtCons s d i =>
        exact smtTermClosedIn_eo_to_smt_dtcons vars s d i
      case DtSel s d i j =>
        exact smtTermClosedIn_eo_to_smt_dtsel vars s d i j
      case UConst i T =>
        exact smtTermClosedIn_eo_to_smt_uconst vars i T
      all_goals
        change True
        trivial
termination_by n
decreasing_by
  all_goals omega

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
  exact smtTermClosedIn_of_native_eo_to_smt_closed_rec_safe_lt
    (sizeOf t + 1) (t := t) (env := []) (vars := [])
    (by omega)
    (by
      simpa [eoListOfTerms] using
        EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
    (by simpa [native_eo_to_smt_closed] using hClosed)
    hSafe

private theorem smtTermAvoidsVar_of_closedIn_not_mem
    {t : SmtTerm} {vars : List SmtVarKey}
    {s0 : native_String} {T0 : SmtType}
    (hClosed : SmtTermClosedIn vars t)
    (hNotMem : (s0, T0) ∉ vars) :
    SmtTermAvoidsVar s0 T0 t := by
  let rec go (t : SmtTerm) {vars : List SmtVarKey}
      (hClosed : SmtTermClosedIn vars t)
      (hNotMem : (s0, T0) ∉ vars) :
      SmtTermAvoidsVar s0 T0 t := by
    cases t <;> simp [SmtTermClosedIn, SmtTermAvoidsVar] at hClosed ⊢
    case Var s T =>
      intro hs hT
      apply hNotMem
      cases hs
      cases hT
      exact hClosed
    case «exists» s T body =>
      by_cases hShadow : (s, T) = (s0, T0)
      · left
        injection hShadow with hs hT
        exact ⟨hs, hT⟩
      · right
        exact go body hClosed (by
          intro hMem
          cases hMem with
          | head =>
              exact hShadow rfl
          | tail _ hTail =>
              exact hNotMem hTail)
    case «forall» s T body =>
      by_cases hShadow : (s, T) = (s0, T0)
      · left
        injection hShadow with hs hT
        exact ⟨hs, hT⟩
      · right
        exact go body hClosed (by
          intro hMem
          cases hMem with
          | head =>
              exact hShadow rfl
          | tail _ hTail =>
              exact hNotMem hTail)
    case choice_nth s T body k =>
      by_cases hShadow : (s, T) = (s0, T0)
      · left
        injection hShadow with hs hT
        exact ⟨hs, hT⟩
      · right
        exact go body hClosed (by
          intro hMem
          cases hMem with
          | head =>
              exact hShadow rfl
          | tail _ hTail =>
              exact hNotMem hTail)
    all_goals try exact go _ hClosed hNotMem
    all_goals try exact ⟨go _ hClosed.1 hNotMem,
      go _ hClosed.2 hNotMem⟩
    all_goals try exact ⟨go _ hClosed.1 hNotMem,
      go _ hClosed.2.1 hNotMem,
      go _ hClosed.2.2 hNotMem⟩
  exact go t hClosed hNotMem

private theorem smtTermAvoidsVar_of_native_eo_to_smt_closed_safe
    (t : Term) (s0 : native_String) (T0 : SmtType)
    (hClosed : native_eo_to_smt_closed t = true)
    (hSafe : NativeEoToSmtUOpIndicesSafe t) :
    SmtTermAvoidsVar s0 T0 (__eo_to_smt t) := by
  exact smtTermAvoidsVar_of_closedIn_not_mem
    (smtTermClosedIn_of_native_eo_to_smt_closed_safe t hClosed hSafe)
    (by intro h; cases h)

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

private theorem contains_atomic_term_apply_false_parts
    {f a x : Term}
    (hx : x ≠ Term.Stuck)
    (h :
      __contains_atomic_term (Term.Apply f a) x =
        Term.Boolean false) :
    __contains_atomic_term f x = Term.Boolean false ∧
      __contains_atomic_term a x = Term.Boolean false := by
  rw [__contains_atomic_term.eq_3 x f a hx] at h
  cases hf : __contains_atomic_term f x <;>
    simp [__eo_ite, hf, native_ite, native_teq] at h
  case Boolean b =>
    cases b
    · simp at h ⊢
      exact h
    · simp at h

private def appTreeVars : Term -> List Term
  | Term.Var (Term.String s) T => [Term.Var (Term.String s) T]
  | Term.Apply f a => appTreeVars f ++ appTreeVars a
  | _ => []

private def appTreeSmtVars : Term -> List SmtVarKey
  | Term.Var (Term.String s) T => [(s, __eo_to_smt_type T)]
  | Term.Apply f a => appTreeSmtVars f ++ appTreeSmtVars a
  | _ => []

private theorem EoSmtVarEnv_appTreeVars_lt
    (n : Nat) :
    ∀ t : Term,
      sizeOf t < n ->
        EoSmtVarEnv (eoListOfTerms (appTreeVars t)) (appTreeSmtVars t) := by
  cases n with
  | zero =>
      intro t hLt
      omega
  | succ n =>
      intro t hLt
      cases t
      case Apply f a =>
        change EoSmtVarEnv
          (eoListOfTerms (appTreeVars f ++ appTreeVars a))
          (appTreeSmtVars f ++ appTreeSmtVars a)
        rw [← eoListOfTerms_concat]
        exact EoSmtVarEnv.concat
          (EoSmtVarEnv_appTreeVars_lt n f (by simp at hLt; omega))
          (EoSmtVarEnv_appTreeVars_lt n a (by simp at hLt; omega))
      case Var name T =>
        cases name
        case String s =>
          simp [appTreeVars, appTreeSmtVars, eoListOfTerms]
          exact EoSmtVarEnv.cons EoSmtVarEnv.nil
        all_goals
          simp [appTreeVars, appTreeSmtVars, eoListOfTerms]
          exact EoSmtVarEnv.nil
      all_goals
        simp [appTreeVars, appTreeSmtVars, eoListOfTerms]
        exact EoSmtVarEnv.nil

private theorem EoSmtVarEnv_appTreeVars
    (t : Term) :
    EoSmtVarEnv (eoListOfTerms (appTreeVars t)) (appTreeSmtVars t) := by
  exact EoSmtVarEnv_appTreeVars_lt (sizeOf t + 1) t (by omega)

private theorem native_eo_to_smt_term_mem_of_mem :
    ∀ {x : Term} {env : List Term},
      x ∈ env -> native_eo_to_smt_term_mem x env = true
  | _, [], h => by
      simp at h
  | x, y :: ys, h => by
      cases h with
      | head =>
          simp [native_eo_to_smt_term_mem, native_or]
      | tail _ hTail =>
          by_cases hxy : x = y
          · simp [native_eo_to_smt_term_mem, hxy, native_or]
          · simp [native_eo_to_smt_term_mem, hxy, native_or,
              native_eo_to_smt_term_mem_of_mem hTail]

private theorem smtTermClosedIn_of_native_eo_to_smt_closed_safe_any
    (vars : List SmtVarKey) (t : Term)
    (hClosed : native_eo_to_smt_closed t = true)
    (hSafe : NativeEoToSmtUOpIndicesSafe t) :
    SmtTermClosedIn vars (__eo_to_smt t) :=
  smtTermClosedIn_weaken_nil
    (smtTermClosedIn_of_native_eo_to_smt_closed_safe t hClosed hSafe)

private theorem smtTermClosedIn_eo_to_smt_set_insert_appTree_using
    (root : Term)
    (hRec :
      ∀ {u : Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf root ->
          NativeEoToSmtUOpIndicesSafe u ->
            (∀ key, key ∈ appTreeSmtVars u -> key ∈ vars') ->
              SmtTermClosedIn vars' (__eo_to_smt u)) :
    ∀ {xs : Term} {base : SmtTerm} {vars : List SmtVarKey},
      sizeOf xs < sizeOf root ->
        NativeEoToSmtUOpIndicesSafe xs ->
          (∀ key, key ∈ appTreeSmtVars xs -> key ∈ vars) ->
            SmtTermClosedIn vars base ->
              SmtTermClosedIn vars (__eo_to_smt_set_insert xs base)
  | Term.__eo_List_nil, base, vars, _hLt, _hSafe, _hSub, hBase => by
      simpa [__eo_to_smt_set_insert] using hBase
  | Term.Apply f tail, base, vars, hLt, hSafe, hSub, hBase => by
      cases f <;> try trivial
      case Apply g head =>
        cases g <;> try trivial
        case __eo_List_cons =>
          have hHeadLt : sizeOf head < sizeOf root := by
            simp at hLt
            omega
          have hTailLt : sizeOf tail < sizeOf root := by
            simp at hLt
            omega
          have hHeadSafe : NativeEoToSmtUOpIndicesSafe head :=
            uop_indices_safe_apply_right
              (uop_indices_safe_apply_left hSafe)
          have hTailSafe : NativeEoToSmtUOpIndicesSafe tail :=
            uop_indices_safe_apply_right hSafe
          have hHeadClosed :
              SmtTermClosedIn vars (__eo_to_smt head) :=
            hRec hHeadLt hHeadSafe (by
              intro key hMem
              apply hSub
              simp [appTreeSmtVars, hMem])
          have hTailClosed :
              SmtTermClosedIn vars
                (__eo_to_smt_set_insert tail base) :=
            smtTermClosedIn_eo_to_smt_set_insert_appTree_using
              root hRec hTailLt hTailSafe
              (by
                intro key hMem
                apply hSub
                simp [appTreeSmtVars, hMem])
              hBase
          change SmtTermClosedIn vars
            (SmtTerm.set_union
              (SmtTerm.set_singleton (__eo_to_smt head))
              (__eo_to_smt_set_insert tail base))
          exact ⟨hHeadClosed, hTailClosed⟩
  | Term.UOp _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.UOp1 _ _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.UOp2 _ _ _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.UOp3 _ _ _ _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.__eo_List, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.__eo_List_cons, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.Bool, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.Boolean _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.Numeral _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.Rational _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.String _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.Binary _ _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.Type, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.Stuck, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.FunType, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.Var _ _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.DatatypeType _ _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.DatatypeTypeRef _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.DtcAppType _ _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.DtCons _ _ _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.DtSel _ _ _ _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.USort _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial
  | Term.UConst _ _, base, vars, _hLt, _hSafe, _hSub, _hBase => by trivial

private theorem smtTermClosedIn_eo_to_smt_distinct_pairs_appTree_using
    (root : Term)
    (hRec :
      ∀ {u : Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf root ->
          NativeEoToSmtUOpIndicesSafe u ->
            (∀ key, key ∈ appTreeSmtVars u -> key ∈ vars') ->
              SmtTermClosedIn vars' (__eo_to_smt u)) :
    ∀ {xs : Term} {s : SmtTerm} {vars : List SmtVarKey},
      sizeOf xs < sizeOf root ->
        SmtTermClosedIn vars s ->
          NativeEoToSmtUOpIndicesSafe xs ->
            (∀ key, key ∈ appTreeSmtVars xs -> key ∈ vars) ->
              SmtTermClosedIn vars (__eo_to_smt_distinct_pairs s xs)
  | Term.Apply f tail, s, vars, hLt, hs, hSafe, hSub => by
      cases f <;> try trivial
      case UOp op =>
        cases op <;> trivial
      case Apply g head =>
        cases g <;> try trivial
        case UOp op =>
          cases op <;> try trivial
          case _at__at_TypedList_cons =>
            have hHeadLt : sizeOf head < sizeOf root := by
              simp at hLt
              omega
            have hTailLt : sizeOf tail < sizeOf root := by
              simp at hLt
              omega
            have hHeadSafe : NativeEoToSmtUOpIndicesSafe head :=
              uop_indices_safe_apply_right
                (uop_indices_safe_apply_left hSafe)
            have hTailSafe : NativeEoToSmtUOpIndicesSafe tail :=
              uop_indices_safe_apply_right hSafe
            have hHeadClosed :
                SmtTermClosedIn vars (__eo_to_smt head) :=
              hRec hHeadLt hHeadSafe (by
                intro key hMem
                apply hSub
                simp [appTreeSmtVars, hMem])
            have hTailClosed :
                SmtTermClosedIn vars
                  (__eo_to_smt_distinct_pairs s tail) :=
              smtTermClosedIn_eo_to_smt_distinct_pairs_appTree_using
                root hRec hTailLt hs hTailSafe
                (by
                  intro key hMem
                  apply hSub
                  simp [appTreeSmtVars, hMem])
            change SmtTermClosedIn vars
              (SmtTerm.and
                (SmtTerm.not (SmtTerm.eq s (__eo_to_smt head)))
                (__eo_to_smt_distinct_pairs s tail))
            exact ⟨⟨hs, hHeadClosed⟩, hTailClosed⟩
  | Term.UOp _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.UOp1 _ _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.UOp2 _ _ _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.UOp3 _ _ _ _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.__eo_List, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.__eo_List_nil, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.__eo_List_cons, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.Bool, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.Boolean _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.Numeral _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.Rational _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.String _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.Binary _ _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.Type, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.Stuck, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.FunType, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.Var _ _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.DatatypeType _ _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.DatatypeTypeRef _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.DtcAppType _ _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.DtCons _ _ _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.DtSel _ _ _ _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.USort _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial
  | Term.UConst _ _, s, vars, _hLt, _hs, _hSafe, _hSub => by trivial

private theorem smtTermClosedIn_eo_to_smt_distinct_appTree_using
    (root : Term)
    (hRec :
      ∀ {u : Term} {vars' : List SmtVarKey},
        sizeOf u < sizeOf root ->
          NativeEoToSmtUOpIndicesSafe u ->
            (∀ key, key ∈ appTreeSmtVars u -> key ∈ vars') ->
              SmtTermClosedIn vars' (__eo_to_smt u)) :
    ∀ {xs : Term} {vars : List SmtVarKey},
      sizeOf xs < sizeOf root ->
        NativeEoToSmtUOpIndicesSafe xs ->
          (∀ key, key ∈ appTreeSmtVars xs -> key ∈ vars) ->
            SmtTermClosedIn vars (__eo_to_smt_distinct xs)
  | Term.Apply f tail, vars, hLt, hSafe, hSub => by
      cases f <;> try trivial
      case UOp op =>
        cases op <;> trivial
      case Apply g head =>
        cases g <;> try trivial
        case UOp op =>
          cases op <;> try trivial
          case _at__at_TypedList_cons =>
            have hHeadLt : sizeOf head < sizeOf root := by
              simp at hLt
              omega
            have hTailLt : sizeOf tail < sizeOf root := by
              simp at hLt
              omega
            have hHeadSafe : NativeEoToSmtUOpIndicesSafe head :=
              uop_indices_safe_apply_right
                (uop_indices_safe_apply_left hSafe)
            have hTailSafe : NativeEoToSmtUOpIndicesSafe tail :=
              uop_indices_safe_apply_right hSafe
            have hHeadClosed :
                SmtTermClosedIn vars (__eo_to_smt head) :=
              hRec hHeadLt hHeadSafe (by
                intro key hMem
                apply hSub
                simp [appTreeSmtVars, hMem])
            have hPairsClosed :
                SmtTermClosedIn vars
                  (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail) :=
              smtTermClosedIn_eo_to_smt_distinct_pairs_appTree_using
                root hRec hTailLt hHeadClosed hTailSafe
                (by
                  intro key hMem
                  apply hSub
                  simp [appTreeSmtVars, hMem])
            have hTailClosed :
                SmtTermClosedIn vars (__eo_to_smt_distinct tail) :=
              smtTermClosedIn_eo_to_smt_distinct_appTree_using
                root hRec hTailLt hTailSafe
                (by
                  intro key hMem
                  apply hSub
                  simp [appTreeSmtVars, hMem])
            change SmtTermClosedIn vars
              (SmtTerm.and
                (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail)
                (__eo_to_smt_distinct tail))
            exact ⟨hPairsClosed, hTailClosed⟩
  | Term.UOp _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.UOp1 _ _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.UOp2 _ _ _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.UOp3 _ _ _ _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.__eo_List, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.__eo_List_nil, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.__eo_List_cons, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.Bool, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.Boolean _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.Numeral _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.Rational _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.String _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.Binary _ _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.Type, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.Stuck, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.FunType, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.Var _ _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.DatatypeType _ _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.DatatypeTypeRef _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.DtcAppType _ _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.DtCons _ _ _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.DtSel _ _ _ _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.USort _, vars, _hLt, _hSafe, _hSub => by trivial
  | Term.UConst _ _, vars, _hLt, _hSafe, _hSub => by trivial

private theorem appTreeSmtVars_not_mem_of_contains_atomic_term_false_lt
    (n : Nat) :
    ∀ (F : Term) (s : native_String) (T : Term),
      sizeOf F < n ->
        eo_type_valid T ->
        __contains_atomic_term F (Term.Var (Term.String s) T) =
          Term.Boolean false ->
          (s, __eo_to_smt_type T) ∉ appTreeSmtVars F := by
  cases n with
  | zero =>
      intro F s T hLt _hTValid _hNoOccur
      omega
  | succ n =>
      intro F s T hLt hTValid hNoOccur
      cases F
      case Var name U =>
        cases name
        case String s' =>
          intro hMem
          simp [appTreeSmtVars] at hMem
          rcases hMem with ⟨hs, hTy⟩
          have hTermTy : T = U :=
            eo_to_smt_type_eq_of_top_valid_local hTValid (by simpa [hTy])
          subst s'
          subst U
          have hImpossible :
              Term.Boolean true = Term.Boolean false := by
            simpa [__contains_atomic_term, __eo_eq, native_teq]
              using hNoOccur
          cases hImpossible
        all_goals
          simp [appTreeSmtVars]
      case Apply f a =>
        have hx :
            Term.Var (Term.String s) T ≠ Term.Stuck :=
          quantVarTerm_ne_stuck (by simp [IsQuantVarTerm])
        rcases contains_atomic_term_apply_false_parts hx hNoOccur with
          ⟨hfNo, haNo⟩
        intro hMem
        have hMem' :
            (s, __eo_to_smt_type T) ∈
              appTreeSmtVars f ++ appTreeSmtVars a := by
          simpa [appTreeSmtVars] using hMem
        rcases List.mem_append.1 hMem' with hMem | hMem
        · exact appTreeSmtVars_not_mem_of_contains_atomic_term_false_lt
            n f s T (by simp at hLt; omega) hTValid hfNo hMem
        · exact appTreeSmtVars_not_mem_of_contains_atomic_term_false_lt
            n a s T (by simp at hLt; omega) hTValid haNo hMem
      all_goals
        simp [appTreeSmtVars]

private theorem appTreeSmtVars_not_mem_of_contains_atomic_term_false
    (F : Term) (s : native_String) (T : Term)
    (hTValid : eo_type_valid T)
    (hNoOccur :
      __contains_atomic_term F (Term.Var (Term.String s) T) =
        Term.Boolean false) :
    (s, __eo_to_smt_type T) ∉ appTreeSmtVars F := by
  exact appTreeSmtVars_not_mem_of_contains_atomic_term_false_lt
    (sizeOf F + 1) F s T (by omega) hTValid hNoOccur

private theorem smtTermClosedIn_appTreeVars_of_uop_indices_safe_lt
    (n : Nat) :
    ∀ (F : Term) {vars : List SmtVarKey},
      sizeOf F < n ->
        NativeEoToSmtUOpIndicesSafe F ->
          (∀ key, key ∈ appTreeSmtVars F -> key ∈ vars) ->
            SmtTermClosedIn vars (__eo_to_smt F) := by
  cases n with
  | zero =>
      intro F vars hLt _hSafe _hSub
      omega
  | succ n =>
      intro F vars hLt hSafe hSub
      let hRec :
          ∀ {u : Term} {vars' : List SmtVarKey},
            sizeOf u < sizeOf F ->
              NativeEoToSmtUOpIndicesSafe u ->
                (∀ key, key ∈ appTreeSmtVars u -> key ∈ vars') ->
                  SmtTermClosedIn vars' (__eo_to_smt u) :=
        fun {u} {vars'} hULt hSafe' hSub' =>
          smtTermClosedIn_appTreeVars_of_uop_indices_safe_lt
            n u (vars := vars') (by omega) hSafe' hSub'
      cases F
      case Stuck =>
        trivial
      case Var name T =>
        cases name
        case String s =>
          change (s, __eo_to_smt_type T) ∈ vars
          exact hSub (s, __eo_to_smt_type T) (by simp [appTreeSmtVars])
        all_goals
          trivial
      case Apply f x =>
        have hfSafe : NativeEoToSmtUOpIndicesSafe f :=
          uop_indices_safe_apply_left hSafe
        have hxSafe : NativeEoToSmtUOpIndicesSafe x :=
          uop_indices_safe_apply_right hSafe
        have hfClosed : SmtTermClosedIn vars (__eo_to_smt f) :=
          hRec (u := f) (by simp; omega) hfSafe (by
            intro key hMem
            apply hSub
            simp [appTreeSmtVars, hMem])
        have hxClosed : SmtTermClosedIn vars (__eo_to_smt x) :=
          hRec (u := x) (by simp; omega) hxSafe (by
            intro key hMem
            apply hSub
            simp [appTreeSmtVars, hMem])
        cases f
        case UOp op =>
          cases op
          case not =>
            exact smtTermClosedIn_eo_to_smt_not hxClosed
          case distinct =>
            change SmtTermClosedIn vars
              (native_ite
                (native_Teq (__eo_to_smt_typed_list_elem_type x)
                  SmtType.None)
                SmtTerm.None (__eo_to_smt_distinct x))
            cases hElem :
                native_Teq (__eo_to_smt_typed_list_elem_type x)
                  SmtType.None
            · simpa [native_ite, hElem] using
                smtTermClosedIn_eo_to_smt_distinct_appTree_using
                  (Term.Apply (Term.UOp UserOp.distinct) x)
                  (fun {u} {vars'} hULt hSafe' hSub' =>
                    hRec (u := u) hULt hSafe' hSub')
                  (by simp) hxSafe
                  (by
                    intro key hMem
                    apply hSub
                    simp [appTreeSmtVars, hMem])
            · trivial
          case to_real =>
            exact smtTermClosedIn_eo_to_smt_to_real hxClosed
          case to_int =>
            exact smtTermClosedIn_eo_to_smt_to_int hxClosed
          case is_int =>
            exact smtTermClosedIn_eo_to_smt_is_int hxClosed
          case abs =>
            exact smtTermClosedIn_eo_to_smt_abs hxClosed
          case __eoo_neg_2 =>
            exact smtTermClosedIn_eo_to_smt_uneg hxClosed
          case int_pow2 =>
            exact smtTermClosedIn_eo_to_smt_int_pow2 hxClosed
          case int_log2 =>
            exact smtTermClosedIn_eo_to_smt_int_log2 hxClosed
          case int_ispow2 =>
            exact smtTermClosedIn_eo_to_smt_int_ispow2 hxClosed
          case _at_int_div_by_zero =>
            exact smtTermClosedIn_eo_to_smt_int_div_by_zero hxClosed
          case _at_mod_by_zero =>
            exact smtTermClosedIn_eo_to_smt_mod_by_zero hxClosed
          case _at_bvsize =>
            exact smtTermClosedIn_eo_to_smt_bvsize vars x
          case bvnot =>
            exact smtTermClosedIn_eo_to_smt_bvnot hxClosed
          case bvneg =>
            exact smtTermClosedIn_eo_to_smt_bvneg hxClosed
          case bvnego =>
            exact smtTermClosedIn_eo_to_smt_bvnego hxClosed
          case bvredand =>
            exact smtTermClosedIn_eo_to_smt_bvredand hxClosed
          case bvredor =>
            exact smtTermClosedIn_eo_to_smt_bvredor hxClosed
          case str_len =>
            exact smtTermClosedIn_eo_to_smt_str_len hxClosed
          case str_rev =>
            exact smtTermClosedIn_eo_to_smt_str_rev hxClosed
          case str_to_lower =>
            exact smtTermClosedIn_eo_to_smt_str_to_lower hxClosed
          case str_to_upper =>
            exact smtTermClosedIn_eo_to_smt_str_to_upper hxClosed
          case str_to_code =>
            exact smtTermClosedIn_eo_to_smt_str_to_code hxClosed
          case str_from_code =>
            exact smtTermClosedIn_eo_to_smt_str_from_code hxClosed
          case str_is_digit =>
            exact smtTermClosedIn_eo_to_smt_str_is_digit hxClosed
          case str_to_int =>
            exact smtTermClosedIn_eo_to_smt_str_to_int hxClosed
          case str_from_int =>
            exact smtTermClosedIn_eo_to_smt_str_from_int hxClosed
          case str_to_re =>
            exact smtTermClosedIn_eo_to_smt_str_to_re hxClosed
          case re_mult =>
            exact smtTermClosedIn_eo_to_smt_re_mult hxClosed
          case re_plus =>
            exact smtTermClosedIn_eo_to_smt_re_plus hxClosed
          case re_opt =>
            exact smtTermClosedIn_eo_to_smt_re_opt hxClosed
          case re_comp =>
            exact smtTermClosedIn_eo_to_smt_re_comp hxClosed
          case seq_unit =>
            exact smtTermClosedIn_eo_to_smt_seq_unit hxClosed
          case set_singleton =>
            exact smtTermClosedIn_eo_to_smt_set_singleton hxClosed
          case set_choose =>
            exact smtTermClosedIn_eo_to_smt_set_choose hxClosed
          case set_is_empty =>
            exact smtTermClosedIn_eo_to_smt_set_is_empty hxClosed
          case set_is_singleton =>
            exact smtTermClosedIn_eo_to_smt_set_is_singleton hxClosed
          case _at_div_by_zero =>
            exact smtTermClosedIn_eo_to_smt_qdiv_by_zero hxClosed
          case ubv_to_int =>
            exact smtTermClosedIn_eo_to_smt_ubv_to_int hxClosed
          case sbv_to_int =>
            exact smtTermClosedIn_eo_to_smt_sbv_to_int hxClosed
          all_goals
            change SmtTermClosedIn vars
              (SmtTerm.Apply (__eo_to_smt (Term.UOp _)) (__eo_to_smt x))
            exact ⟨hfClosed, hxClosed⟩
        case UOp1 op idx =>
          have hIndexedSafe : NativeEoToSmtUOpIndicesSafe (Term.UOp1 op idx) :=
            hfSafe
          have hIdxClosed : SmtTermClosedIn vars (__eo_to_smt idx) :=
            smtTermClosedIn_of_native_eo_to_smt_closed_safe_any vars idx
              (uop_indices_safe_uop1_closed hIndexedSafe)
              (uop_indices_safe_uop1_safe hIndexedSafe)
          cases op
          case «repeat» =>
            exact smtTermClosedIn_eo_to_smt_repeat hIdxClosed hxClosed
          case zero_extend =>
            exact smtTermClosedIn_eo_to_smt_zero_extend hIdxClosed hxClosed
          case sign_extend =>
            exact smtTermClosedIn_eo_to_smt_sign_extend hIdxClosed hxClosed
          case rotate_left =>
            exact smtTermClosedIn_eo_to_smt_rotate_left hIdxClosed hxClosed
          case rotate_right =>
            exact smtTermClosedIn_eo_to_smt_rotate_right hIdxClosed hxClosed
          case _at_bit =>
            exact smtTermClosedIn_eo_to_smt_at_bit hIdxClosed hxClosed
          case re_exp =>
            exact smtTermClosedIn_eo_to_smt_re_exp hIdxClosed hxClosed
          case _at_strings_stoi_result =>
            exact smtTermClosedIn_eo_to_smt_strings_stoi_result
              hIdxClosed hxClosed
          case _at_strings_itos_result =>
            exact smtTermClosedIn_eo_to_smt_strings_itos_result
              hIdxClosed hxClosed
          case «is» =>
            exact smtTermClosedIn_eo_to_smt_is hIdxClosed hxClosed
          case tuple_select =>
            exact smtTermClosedIn_eo_to_smt_tuple_select hIdxClosed hxClosed
          case int_to_bv =>
            exact smtTermClosedIn_eo_to_smt_int_to_bv hIdxClosed hxClosed
          all_goals
            change SmtTermClosedIn vars
              (SmtTerm.Apply (__eo_to_smt (Term.UOp1 _ idx))
                (__eo_to_smt x))
            exact ⟨hfClosed, hxClosed⟩
        case UOp2 op idx1 idx2 =>
          have hIndexedSafe :
              NativeEoToSmtUOpIndicesSafe (Term.UOp2 op idx1 idx2) :=
            hfSafe
          have hIdx1Closed : SmtTermClosedIn vars (__eo_to_smt idx1) :=
            smtTermClosedIn_of_native_eo_to_smt_closed_safe_any vars idx1
              (uop_indices_safe_uop2_closed_left hIndexedSafe)
              (uop_indices_safe_uop2_safe_left hIndexedSafe)
          have hIdx2Closed : SmtTermClosedIn vars (__eo_to_smt idx2) :=
            smtTermClosedIn_of_native_eo_to_smt_closed_safe_any vars idx2
              (uop_indices_safe_uop2_closed_right hIndexedSafe)
              (uop_indices_safe_uop2_safe_right hIndexedSafe)
          cases op
          case extract =>
            exact smtTermClosedIn_eo_to_smt_extract
              hIdx1Closed hIdx2Closed hxClosed
          case re_loop =>
            exact smtTermClosedIn_eo_to_smt_re_loop
              hIdx1Closed hIdx2Closed hxClosed
          all_goals
            change SmtTermClosedIn vars
              (SmtTerm.Apply (__eo_to_smt (Term.UOp2 _ idx1 idx2))
                (__eo_to_smt x))
            exact ⟨hfClosed, hxClosed⟩
        case Apply g y =>
          have hgSafe : NativeEoToSmtUOpIndicesSafe g :=
            uop_indices_safe_apply_left hfSafe
          have hySafe : NativeEoToSmtUOpIndicesSafe y :=
            uop_indices_safe_apply_right hfSafe
          have hgClosed : SmtTermClosedIn vars (__eo_to_smt g) :=
            hRec (u := g) (by simp; omega) hgSafe (by
              intro key hMem
              apply hSub
              simp [appTreeSmtVars, hMem])
          have hyClosed : SmtTermClosedIn vars (__eo_to_smt y) :=
            hRec (u := y) (by simp; omega) hySafe (by
              intro key hMem
              apply hSub
              simp [appTreeSmtVars, hMem])
          cases g
          case UOp op =>
            cases op
            case «or» =>
              exact smtTermClosedIn_eo_to_smt_or hyClosed hxClosed
            case «and» =>
              exact smtTermClosedIn_eo_to_smt_and hyClosed hxClosed
            case imp =>
              exact smtTermClosedIn_eo_to_smt_imp hyClosed hxClosed
            case xor =>
              exact smtTermClosedIn_eo_to_smt_xor hyClosed hxClosed
            case eq =>
              exact smtTermClosedIn_eo_to_smt_eq hyClosed hxClosed
            case plus =>
              exact smtTermClosedIn_eo_to_smt_plus hyClosed hxClosed
            case neg =>
              exact smtTermClosedIn_eo_to_smt_neg hyClosed hxClosed
            case mult =>
              exact smtTermClosedIn_eo_to_smt_mult hyClosed hxClosed
            case lt =>
              exact smtTermClosedIn_eo_to_smt_lt hyClosed hxClosed
            case leq =>
              exact smtTermClosedIn_eo_to_smt_leq hyClosed hxClosed
            case gt =>
              exact smtTermClosedIn_eo_to_smt_gt hyClosed hxClosed
            case geq =>
              exact smtTermClosedIn_eo_to_smt_geq hyClosed hxClosed
            case div =>
              exact smtTermClosedIn_eo_to_smt_div hyClosed hxClosed
            case mod =>
              exact smtTermClosedIn_eo_to_smt_mod hyClosed hxClosed
            case multmult =>
              exact smtTermClosedIn_eo_to_smt_multmult hyClosed hxClosed
            case divisible =>
              exact smtTermClosedIn_eo_to_smt_divisible hyClosed hxClosed
            case div_total =>
              exact smtTermClosedIn_eo_to_smt_div_total hyClosed hxClosed
            case mod_total =>
              exact smtTermClosedIn_eo_to_smt_mod_total hyClosed hxClosed
            case multmult_total =>
              exact smtTermClosedIn_eo_to_smt_multmult_total hyClosed hxClosed
            case select =>
              exact smtTermClosedIn_eo_to_smt_select hyClosed hxClosed
            case concat =>
              exact smtTermClosedIn_eo_to_smt_concat hyClosed hxClosed
            case bvand =>
              exact smtTermClosedIn_eo_to_smt_bvand hyClosed hxClosed
            case bvor =>
              exact smtTermClosedIn_eo_to_smt_bvor hyClosed hxClosed
            case bvnand =>
              exact smtTermClosedIn_eo_to_smt_bvnand hyClosed hxClosed
            case bvnor =>
              exact smtTermClosedIn_eo_to_smt_bvnor hyClosed hxClosed
            case bvxor =>
              exact smtTermClosedIn_eo_to_smt_bvxor hyClosed hxClosed
            case bvxnor =>
              exact smtTermClosedIn_eo_to_smt_bvxnor hyClosed hxClosed
            case bvcomp =>
              exact smtTermClosedIn_eo_to_smt_bvcomp hyClosed hxClosed
            case bvadd =>
              exact smtTermClosedIn_eo_to_smt_bvadd hyClosed hxClosed
            case bvmul =>
              exact smtTermClosedIn_eo_to_smt_bvmul hyClosed hxClosed
            case bvudiv =>
              exact smtTermClosedIn_eo_to_smt_bvudiv hyClosed hxClosed
            case bvurem =>
              exact smtTermClosedIn_eo_to_smt_bvurem hyClosed hxClosed
            case bvsub =>
              exact smtTermClosedIn_eo_to_smt_bvsub hyClosed hxClosed
            case bvsdiv =>
              exact smtTermClosedIn_eo_to_smt_bvsdiv hyClosed hxClosed
            case bvsrem =>
              exact smtTermClosedIn_eo_to_smt_bvsrem hyClosed hxClosed
            case bvsmod =>
              exact smtTermClosedIn_eo_to_smt_bvsmod hyClosed hxClosed
            case bvult =>
              exact smtTermClosedIn_eo_to_smt_bvult hyClosed hxClosed
            case bvule =>
              exact smtTermClosedIn_eo_to_smt_bvule hyClosed hxClosed
            case bvugt =>
              exact smtTermClosedIn_eo_to_smt_bvugt hyClosed hxClosed
            case bvuge =>
              exact smtTermClosedIn_eo_to_smt_bvuge hyClosed hxClosed
            case bvslt =>
              exact smtTermClosedIn_eo_to_smt_bvslt hyClosed hxClosed
            case bvsle =>
              exact smtTermClosedIn_eo_to_smt_bvsle hyClosed hxClosed
            case bvsgt =>
              exact smtTermClosedIn_eo_to_smt_bvsgt hyClosed hxClosed
            case bvsge =>
              exact smtTermClosedIn_eo_to_smt_bvsge hyClosed hxClosed
            case bvshl =>
              exact smtTermClosedIn_eo_to_smt_bvshl hyClosed hxClosed
            case bvlshr =>
              exact smtTermClosedIn_eo_to_smt_bvlshr hyClosed hxClosed
            case bvashr =>
              exact smtTermClosedIn_eo_to_smt_bvashr hyClosed hxClosed
            case bvuaddo =>
              exact smtTermClosedIn_eo_to_smt_bvuaddo hyClosed hxClosed
            case bvsaddo =>
              exact smtTermClosedIn_eo_to_smt_bvsaddo hyClosed hxClosed
            case bvumulo =>
              exact smtTermClosedIn_eo_to_smt_bvumulo hyClosed hxClosed
            case bvsmulo =>
              exact smtTermClosedIn_eo_to_smt_bvsmulo hyClosed hxClosed
            case bvusubo =>
              exact smtTermClosedIn_eo_to_smt_bvusubo hyClosed hxClosed
            case bvssubo =>
              exact smtTermClosedIn_eo_to_smt_bvssubo hyClosed hxClosed
            case bvsdivo =>
              exact smtTermClosedIn_eo_to_smt_bvsdivo hyClosed hxClosed
            case bvultbv =>
              exact smtTermClosedIn_eo_to_smt_bvultbv hyClosed hxClosed
            case bvsltbv =>
              exact smtTermClosedIn_eo_to_smt_bvsltbv hyClosed hxClosed
            case _at_from_bools =>
              exact smtTermClosedIn_eo_to_smt_from_bools hyClosed hxClosed
            case str_concat =>
              exact smtTermClosedIn_eo_to_smt_str_concat hyClosed hxClosed
            case str_contains =>
              exact smtTermClosedIn_eo_to_smt_str_contains hyClosed hxClosed
            case str_at =>
              exact smtTermClosedIn_eo_to_smt_str_at hyClosed hxClosed
            case str_prefixof =>
              exact smtTermClosedIn_eo_to_smt_str_prefixof hyClosed hxClosed
            case str_suffixof =>
              exact smtTermClosedIn_eo_to_smt_str_suffixof hyClosed hxClosed
            case str_lt =>
              exact smtTermClosedIn_eo_to_smt_str_lt hyClosed hxClosed
            case str_leq =>
              exact smtTermClosedIn_eo_to_smt_str_leq hyClosed hxClosed
            case re_range =>
              exact smtTermClosedIn_eo_to_smt_re_range hyClosed hxClosed
            case re_concat =>
              exact smtTermClosedIn_eo_to_smt_re_concat hyClosed hxClosed
            case re_inter =>
              exact smtTermClosedIn_eo_to_smt_re_inter hyClosed hxClosed
            case re_union =>
              exact smtTermClosedIn_eo_to_smt_re_union hyClosed hxClosed
            case re_diff =>
              exact smtTermClosedIn_eo_to_smt_re_diff hyClosed hxClosed
            case str_in_re =>
              exact smtTermClosedIn_eo_to_smt_str_in_re hyClosed hxClosed
            case seq_nth =>
              exact smtTermClosedIn_eo_to_smt_seq_nth hyClosed hxClosed
            case _at_strings_num_occur =>
              exact smtTermClosedIn_eo_to_smt_strings_num_occur
                hyClosed hxClosed
            case tuple =>
              exact smtTermClosedIn_eo_to_smt_tuple hyClosed hxClosed
            case set_union =>
              exact smtTermClosedIn_eo_to_smt_set_union hyClosed hxClosed
            case set_inter =>
              exact smtTermClosedIn_eo_to_smt_set_inter hyClosed hxClosed
            case set_minus =>
              exact smtTermClosedIn_eo_to_smt_set_minus hyClosed hxClosed
            case set_member =>
              exact smtTermClosedIn_eo_to_smt_set_member hyClosed hxClosed
            case set_subset =>
              exact smtTermClosedIn_eo_to_smt_set_subset hyClosed hxClosed
            case set_insert =>
              by_cases hyNil : y = Term.__eo_List_nil
              · subst y
                trivial
              have hSetTranslate :
                  __eo_to_smt
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.set_insert) y) x) =
                    __eo_to_smt_set_insert y (__eo_to_smt x) := by
                cases y <;> try rfl
                case __eo_List_nil =>
                  contradiction
              rw [hSetTranslate]
              exact smtTermClosedIn_eo_to_smt_set_insert_appTree_using
                (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)
                (fun {u} {vars'} hULt hSafe' hSub' =>
                  hRec (u := u) hULt hSafe' hSub')
                (by simp; omega) hySafe
                (by
                  intro key hMem
                  apply hSub
                  simp [appTreeSmtVars, hMem])
                hxClosed
            case qdiv =>
              exact smtTermClosedIn_eo_to_smt_qdiv hyClosed hxClosed
            case qdiv_total =>
              exact smtTermClosedIn_eo_to_smt_qdiv_total hyClosed hxClosed
            case «forall» =>
              exact smtTermClosedIn_eo_to_smt_forall_term_of_env_or_none
                (vs := y) (body := x) (vars := vars)
                (by
                  intro binderVars hVs
                  exact SmtTermClosedIn.mono
                    (t := __eo_to_smt x)
                    (vars := vars)
                    (vars' := binderVars.reverse ++ vars)
                    (by
                      intro s T hMem
                      exact List.mem_append.2 (Or.inr hMem))
                    hxClosed)
            case «exists» =>
              exact smtTermClosedIn_eo_to_smt_exists_term_of_env_or_none
                (vs := y) (body := x) (vars := vars)
                (by
                  intro binderVars hVs
                  exact SmtTermClosedIn.mono
                    (t := __eo_to_smt x)
                    (vars := vars)
                    (vars' := binderVars.reverse ++ vars)
                    (by
                      intro s T hMem
                      exact List.mem_append.2 (Or.inr hMem))
                    hxClosed)
            all_goals
              change SmtTermClosedIn vars
                (SmtTerm.Apply
                  (__eo_to_smt (Term.Apply (Term.UOp _) y))
                  (__eo_to_smt x))
              exact ⟨hfClosed, hxClosed⟩
          case UOp1 op idx =>
            have hIndexedSafe :
                NativeEoToSmtUOpIndicesSafe (Term.UOp1 op idx) :=
              hgSafe
            have hIdxClosed : SmtTermClosedIn vars (__eo_to_smt idx) :=
              smtTermClosedIn_of_native_eo_to_smt_closed_safe_any vars idx
                (uop_indices_safe_uop1_closed hIndexedSafe)
                (uop_indices_safe_uop1_safe hIndexedSafe)
            cases op
            case update =>
              exact smtTermClosedIn_eo_to_smt_update
                hIdxClosed hyClosed hxClosed
            case tuple_update =>
              exact smtTermClosedIn_eo_to_smt_tuple_update
                hIdxClosed hyClosed hxClosed
            all_goals
              change SmtTermClosedIn vars
                (SmtTerm.Apply
                  (__eo_to_smt (Term.Apply (Term.UOp1 _ idx) y))
                  (__eo_to_smt x))
              exact ⟨hfClosed, hxClosed⟩
          case Apply h z =>
            have hhSafe : NativeEoToSmtUOpIndicesSafe h :=
              uop_indices_safe_apply_left hgSafe
            have hzSafe : NativeEoToSmtUOpIndicesSafe z :=
              uop_indices_safe_apply_right hgSafe
            have hzClosed : SmtTermClosedIn vars (__eo_to_smt z) :=
              hRec (u := z) (by simp; omega) hzSafe (by
                intro key hMem
                apply hSub
                simp [appTreeSmtVars, hMem])
            cases h
            case UOp op =>
              cases op
              case ite =>
                exact smtTermClosedIn_eo_to_smt_ite
                  hzClosed hyClosed hxClosed
              case store =>
                exact smtTermClosedIn_eo_to_smt_store
                  hzClosed hyClosed hxClosed
              case bvite =>
                exact smtTermClosedIn_eo_to_smt_bvite
                  hzClosed hyClosed hxClosed
              case str_substr =>
                exact smtTermClosedIn_eo_to_smt_str_substr
                  hzClosed hyClosed hxClosed
              case str_replace =>
                exact smtTermClosedIn_eo_to_smt_str_replace
                  hzClosed hyClosed hxClosed
              case str_indexof =>
                exact smtTermClosedIn_eo_to_smt_str_indexof
                  hzClosed hyClosed hxClosed
              case str_update =>
                exact smtTermClosedIn_eo_to_smt_str_update
                  hzClosed hyClosed hxClosed
              case str_replace_all =>
                exact smtTermClosedIn_eo_to_smt_str_replace_all
                  hzClosed hyClosed hxClosed
              case str_replace_re =>
                exact smtTermClosedIn_eo_to_smt_str_replace_re
                  hzClosed hyClosed hxClosed
              case str_replace_re_all =>
                exact smtTermClosedIn_eo_to_smt_str_replace_re_all
                  hzClosed hyClosed hxClosed
              case str_indexof_re =>
                exact smtTermClosedIn_eo_to_smt_str_indexof_re
                  hzClosed hyClosed hxClosed
              all_goals
                change SmtTermClosedIn vars
                  (SmtTerm.Apply
                    (__eo_to_smt
                      (Term.Apply (Term.Apply (Term.UOp _) z) y))
                    (__eo_to_smt x))
                exact ⟨hfClosed, hxClosed⟩
            all_goals
              change SmtTermClosedIn vars
                (SmtTerm.Apply
                  (__eo_to_smt (Term.Apply (Term.Apply _ z) y))
                  (__eo_to_smt x))
              exact ⟨hfClosed, hxClosed⟩
          all_goals
            change SmtTermClosedIn vars
              (SmtTerm.Apply (__eo_to_smt (Term.Apply _ y))
                (__eo_to_smt x))
            exact ⟨hfClosed, hxClosed⟩
        all_goals
          change SmtTermClosedIn vars
            (SmtTerm.Apply (__eo_to_smt _) (__eo_to_smt x))
          exact ⟨hfClosed, hxClosed⟩
      case UOp op =>
        exact smtTermClosedIn_eo_to_smt_uop vars op
      case UOp1 op idx =>
        exact smtTermClosedIn_of_native_eo_to_smt_closed_safe_any vars
          (Term.UOp1 op idx) (by rfl) hSafe
      case UOp2 op idx1 idx2 =>
        exact smtTermClosedIn_of_native_eo_to_smt_closed_safe_any vars
          (Term.UOp2 op idx1 idx2) (by rfl) hSafe
      case UOp3 op idx1 idx2 idx3 =>
        exact smtTermClosedIn_of_native_eo_to_smt_closed_safe_any vars
          (Term.UOp3 op idx1 idx2 idx3) (by rfl) hSafe
      all_goals
        exact smtTermClosedIn_of_native_eo_to_smt_closed_safe_any vars
          _ (by rfl) hSafe
termination_by n
decreasing_by
  all_goals omega

private theorem smtTermClosedIn_appTreeVars_of_uop_indices_safe
    (F : Term)
    (hSafe : NativeEoToSmtUOpIndicesSafe F) :
    SmtTermClosedIn (appTreeSmtVars F) (__eo_to_smt F) := by
  exact smtTermClosedIn_appTreeVars_of_uop_indices_safe_lt
    (sizeOf F + 1) F (by omega) hSafe (by
      intro key hMem
      exact hMem)

private theorem smtTermAvoidsVar_of_contains_atomic_term_false
    (F : Term) (s : native_String) (T : Term)
    (hTValid : eo_type_valid T)
    (hNoOccur :
      __contains_atomic_term F (Term.Var (Term.String s) T) =
        Term.Boolean false)
    (hSafe : NativeEoToSmtUOpIndicesSafe F) :
    SmtTermAvoidsVar s (__eo_to_smt_type T) (__eo_to_smt F) := by
  exact smtTermAvoidsVar_of_closedIn_not_mem
    (smtTermClosedIn_appTreeVars_of_uop_indices_safe F hSafe)
    (appTreeSmtVars_not_mem_of_contains_atomic_term_false
      F s T hTValid hNoOccur)

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
    (hTValid : eo_type_valid T)
    (hNoOccur :
      __contains_atomic_term F (Term.Var (Term.String s) T) =
        Term.Boolean false)
    (hSafe : NativeEoToSmtUOpIndicesSafe F) :
    __smtx_model_eval
        (native_model_push M s (__eo_to_smt_type T) v)
        (__eo_to_smt F) =
      __smtx_model_eval M (__eo_to_smt F) := by
  exact smtx_model_eval_eq_push_of_avoids
    (smtTermAvoidsVar_of_contains_atomic_term_false
      F s T hTValid hNoOccur hSafe)

private theorem contains_atomic_term_apply_bool_left
    {f a x : Term}
    (hx : x ≠ Term.Stuck)
    (hf : __contains_atomic_term f x = Term.Boolean true) :
    __contains_atomic_term (Term.Apply f a) x = Term.Boolean true := by
  rw [__contains_atomic_term.eq_3 x f a hx]
  simp [__eo_ite, hf, native_ite, native_teq]

private theorem contains_atomic_term_apply_bool_right
    {f a x : Term}
    (hx : x ≠ Term.Stuck)
    (hf : __contains_atomic_term f x = Term.Boolean false)
    (ha : __contains_atomic_term a x = Term.Boolean true) :
    __contains_atomic_term (Term.Apply f a) x = Term.Boolean true := by
  rw [__contains_atomic_term.eq_3 x f a hx]
  simp [__eo_ite, hf, ha, native_ite, native_teq]

private theorem contains_atomic_term_apply_bool_false
    {f a x : Term}
    (hx : x ≠ Term.Stuck)
    (hf : __contains_atomic_term f x = Term.Boolean false)
    (ha : __contains_atomic_term a x = Term.Boolean false) :
    __contains_atomic_term (Term.Apply f a) x = Term.Boolean false := by
  rw [__contains_atomic_term.eq_3 x f a hx]
  simp [__eo_ite, hf, ha, native_ite, native_teq]

private theorem contains_atomic_term_nonapply_quant_var_bool
    {F x : Term}
    (hFNe : F ≠ Term.Stuck)
    (hFNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hx : IsQuantVarTerm x) :
    __contains_atomic_term F x = Term.Boolean true ∨
      __contains_atomic_term F x = Term.Boolean false := by
  have hxNe : x ≠ Term.Stuck := quantVarTerm_ne_stuck hx
  rw [__contains_atomic_term.eq_4 F x hFNe hFNotApply hxNe]
  by_cases hEq : F = x
  · exact Or.inl (eo_eq_eq_true_of_eq_local hEq hFNe hxNe)
  · exact Or.inr (eo_eq_eq_false_of_ne_local hEq hFNe hxNe)

private theorem contains_atomic_term_quant_var_bool_total
    (F x : Term)
    (hx : IsQuantVarTerm x) :
    __contains_atomic_term F x = Term.Boolean true ∨
      __contains_atomic_term F x = Term.Boolean false := by
  cases F
  case Stuck =>
      right
      change Term.Boolean false = Term.Boolean false
      rfl
  case Apply f a =>
      have hxNe : x ≠ Term.Stuck := quantVarTerm_ne_stuck hx
      have hf :=
        contains_atomic_term_quant_var_bool_total f x hx
      have ha :=
        contains_atomic_term_quant_var_bool_total a x hx
      rcases hf with hf | hf
      · exact Or.inl (contains_atomic_term_apply_bool_left hxNe hf)
      · rcases ha with ha | ha
        · exact Or.inl (contains_atomic_term_apply_bool_right hxNe hf ha)
        · exact Or.inr (contains_atomic_term_apply_bool_false hxNe hf ha)
  all_goals
    exact contains_atomic_term_nonapply_quant_var_bool
      (by intro h; cases h)
      (by intro f a h; cases h)
      hx
termination_by sizeOf F

private theorem contains_atomic_term_quant_var_bool
    (F x : Term)
    (hBodyBool : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (hx : IsQuantVarTerm x)
    (hSafe : NativeEoToSmtUOpIndicesSafe F) :
    __contains_atomic_term F x = Term.Boolean true ∨
      __contains_atomic_term F x = Term.Boolean false := by
  exact contains_atomic_term_quant_var_bool_total F x hx

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
    have hInnerBindersBool :
        __smtx_typeof
            (smtExistsOfBinders (xs.map quantTermBinder)
              (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool := by
      rw [← eo_to_smt_exists_eoListOfTerms_binders xs
        (SmtTerm.not (__eo_to_smt F)) hxsAll]
      exact hInnerBool
    have hContains :
        ∀ t ∈ xs,
          __contains_atomic_term F t = Term.Boolean true ∨
            __contains_atomic_term F t = Term.Boolean false := by
      intro t ht
      exact contains_atomic_term_quant_var_bool F t hBodyBool
        (hxsAll t ht) hSafeF
    have hMkRec :
        __mk_quant_unused_vars_rec (eoListOfTerms xs) F =
          eoListOfTerms (quantUnusedVarsList xs F) :=
      mk_quant_unused_vars_rec_eoListOfTerms_eq hFNeStuck
        hxsNonStuck hContains
    have hUnusedAll :
        ∀ t ∈ quantUnusedVarsList xs F, IsQuantVarTerm t :=
      quantUnusedVarsList_all hxsAll
    have hxNonNil : eoListOfTerms xs ≠ Term.__eo_List_nil := by
      intro hNil
      cases xs with
      | nil =>
          exact hxsNonempty rfl
      | cons x xs =>
          simp [eoListOfTerms] at hNil
    have hOrigEq :
        __eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.forall) (eoListOfTerms xs)) F) =
          SmtTerm.not
            (smtExistsOfBinders (xs.map quantTermBinder)
              (SmtTerm.not (__eo_to_smt F))) := by
      rw [eo_to_smt_forall_eq (eoListOfTerms xs) F hxNonNil]
      rw [eo_to_smt_exists_eoListOfTerms_binders xs
        (SmtTerm.not (__eo_to_smt F)) hxsAll]
    have hInvForall :
        ∀ (M0 : SmtModel) (t : Term) (v : SmtValue),
          t ∈ xs ->
          IsQuantVarTerm t ->
          __contains_atomic_term F t = Term.Boolean false ->
          __smtx_model_eval
              (native_model_push M0 (quantTermBinder t).1
                (quantTermBinder t).2 v)
              (SmtTerm.not (__eo_to_smt F)) =
            __smtx_model_eval M0 (SmtTerm.not (__eo_to_smt F)) := by
      intro M0 t v ht hQt hNo
      have hWF :
          __smtx_type_wf (quantTermBinder t).2 = true :=
        smtExistsOfBinders_quantTermBinder_wf_of_mem
          (xs := xs) (body := SmtTerm.not (__eo_to_smt F))
          ht hInnerBindersBool
      cases t <;> simp [IsQuantVarTerm] at hQt
      case Var name T =>
        cases name <;> simp at hQt
        case String s =>
          have hValid : eo_type_valid T :=
            eo_type_valid_of_smt_wf T (by
              simpa [quantTermBinder] using hWF)
          have hInvF :=
            smtx_model_eval_eq_push_of_contains_atomic_term_false
              M0 F s T v hValid (by simpa using hNo) hSafeF
          exact smtx_model_eval_not_congr
            (native_model_push M0 s (__eo_to_smt_type T) v)
            M0 (__eo_to_smt F) hInvF
    have hListEval :=
      smtExistsOfBinders_quantUnusedVarsList_eval xs M hM F
        (SmtTerm.not (__eo_to_smt F)) hxsAll hInnerBindersBool
        hContains hInvForall
    have hOuterEval :
        __smtx_model_eval M
            (SmtTerm.not
              (smtExistsOfBinders (xs.map quantTermBinder)
                (SmtTerm.not (__eo_to_smt F)))) =
          __smtx_model_eval M
            (SmtTerm.not
              (smtExistsOfBinders
                ((quantUnusedVarsList xs F).map quantTermBinder)
                (SmtTerm.not (__eo_to_smt F)))) :=
      smtx_model_eval_not_congr_term M
        (smtExistsOfBinders (xs.map quantTermBinder)
          (SmtTerm.not (__eo_to_smt F)))
        (smtExistsOfBinders
          ((quantUnusedVarsList xs F).map quantTermBinder)
          (SmtTerm.not (__eo_to_smt F)))
        hListEval
    have hMkEval :=
      smtx_model_eval_mk_quant_forall_eoListOfTerms M hM F hFNeStuck hBodyBool
        (quantUnusedVarsList xs F) hUnusedAll
    calc
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.forall) (eoListOfTerms xs)) F)) =
        __smtx_model_eval M
          (SmtTerm.not
            (smtExistsOfBinders (xs.map quantTermBinder)
              (SmtTerm.not (__eo_to_smt F)))) := by
          rw [hOrigEq]
      _ =
        __smtx_model_eval M
          (SmtTerm.not
            (smtExistsOfBinders
              ((quantUnusedVarsList xs F).map quantTermBinder)
              (SmtTerm.not (__eo_to_smt F)))) :=
          hOuterEval
      _ =
        __smtx_model_eval M
          (__eo_to_smt
            (__mk_quant (Term.UOp UserOp.forall)
              (eoListOfTerms (quantUnusedVarsList xs F)) F)) :=
          hMkEval.symm
      _ =
        __smtx_model_eval M
          (__eo_to_smt
            (__mk_quant (Term.UOp UserOp.forall)
              (__mk_quant_unused_vars_rec (eoListOfTerms xs) F) F)) := by
          rw [hMkRec]
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
    have hInnerBindersBool :
        __smtx_typeof
            (smtExistsOfBinders (xs.map quantTermBinder) (__eo_to_smt F)) =
          SmtType.Bool := by
      rw [← eo_to_smt_exists_eoListOfTerms_binders xs
        (__eo_to_smt F) hxsAll]
      exact hInnerBool
    have hContains :
        ∀ t ∈ xs,
          __contains_atomic_term F t = Term.Boolean true ∨
            __contains_atomic_term F t = Term.Boolean false := by
      intro t ht
      exact contains_atomic_term_quant_var_bool F t hBodyBool
        (hxsAll t ht) hSafeF
    have hMkRec :
        __mk_quant_unused_vars_rec (eoListOfTerms xs) F =
          eoListOfTerms (quantUnusedVarsList xs F) :=
      mk_quant_unused_vars_rec_eoListOfTerms_eq hFNeStuck
        hxsNonStuck hContains
    have hUnusedAll :
        ∀ t ∈ quantUnusedVarsList xs F, IsQuantVarTerm t :=
      quantUnusedVarsList_all hxsAll
    have hxNonNil : eoListOfTerms xs ≠ Term.__eo_List_nil := by
      intro hNil
      cases xs with
      | nil =>
          exact hxsNonempty rfl
      | cons x xs =>
          simp [eoListOfTerms] at hNil
    have hOrigEq :
        __eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.exists) (eoListOfTerms xs)) F) =
          smtExistsOfBinders (xs.map quantTermBinder) (__eo_to_smt F) := by
      rw [eo_to_smt_exists_quant_eq (eoListOfTerms xs) F hxNonNil]
      rw [eo_to_smt_exists_eoListOfTerms_binders xs
        (__eo_to_smt F) hxsAll]
    have hInvExists :
        ∀ (M0 : SmtModel) (t : Term) (v : SmtValue),
          t ∈ xs ->
          IsQuantVarTerm t ->
          __contains_atomic_term F t = Term.Boolean false ->
          __smtx_model_eval
              (native_model_push M0 (quantTermBinder t).1
                (quantTermBinder t).2 v)
              (__eo_to_smt F) =
            __smtx_model_eval M0 (__eo_to_smt F) := by
      intro M0 t v ht hQt hNo
      have hWF :
          __smtx_type_wf (quantTermBinder t).2 = true :=
        smtExistsOfBinders_quantTermBinder_wf_of_mem
          (xs := xs) (body := __eo_to_smt F) ht hInnerBindersBool
      cases t <;> simp [IsQuantVarTerm] at hQt
      case Var name T =>
        cases name <;> simp at hQt
        case String s =>
          have hValid : eo_type_valid T :=
            eo_type_valid_of_smt_wf T (by
              simpa [quantTermBinder] using hWF)
          exact
            smtx_model_eval_eq_push_of_contains_atomic_term_false
              M0 F s T v hValid (by simpa using hNo) hSafeF
    have hListEval :=
      smtExistsOfBinders_quantUnusedVarsList_eval xs M hM F
        (__eo_to_smt F) hxsAll hInnerBindersBool hContains hInvExists
    calc
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.exists) (eoListOfTerms xs)) F)) =
        __smtx_model_eval M
          (smtExistsOfBinders (xs.map quantTermBinder) (__eo_to_smt F)) := by
          rw [hOrigEq]
      _ =
        __smtx_model_eval M
          (smtExistsOfBinders
            ((quantUnusedVarsList xs F).map quantTermBinder)
            (__eo_to_smt F)) :=
          hListEval
      _ =
        __smtx_model_eval M
          (__eo_to_smt
            (__mk_quant (Term.UOp UserOp.exists)
              (eoListOfTerms (quantUnusedVarsList xs F)) F)) := by
          rw [eo_to_smt_mk_quant_exists_eoListOfTerms
            (quantUnusedVarsList xs F) F hFNeStuck hUnusedAll]
      _ =
        __smtx_model_eval M
          (__eo_to_smt
            (__mk_quant (Term.UOp UserOp.exists)
              (__mk_quant_unused_vars_rec (eoListOfTerms xs) F) F)) := by
          rw [hMkRec]
