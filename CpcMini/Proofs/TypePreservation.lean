import CpcMini.Proofs.TypePreservation.CoreArith
import CpcMini.Proofs.TypePreservation.Datatypes

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

private theorem type_default_typed_canonical_of_map_domain_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.Map A B) = true) :
    __smtx_typeof_value (__smtx_type_default A) = A ∧
      __smtx_value_canonical (__smtx_type_default A) := by
  have hAll :
      native_inhabited_type (SmtType.Map A B) = true ∧
        native_inhabited_type A = true ∧
          __smtx_type_wf_rec A native_reflist_nil = true ∧
            native_inhabited_type B = true ∧
              __smtx_type_wf_rec B native_reflist_nil = true := by
    simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
  exact type_default_typed_canonical_of_inhabited_wf_rec A hAll.2.1 hAll.2.2.1

private theorem type_default_typed_canonical_of_fun_domain_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_typeof_value (__smtx_type_default A) = A ∧
      __smtx_value_canonical (__smtx_type_default A) := by
  have hAll :
      native_inhabited_type A = true ∧
        __smtx_type_wf_rec A native_reflist_nil = true ∧
          native_inhabited_type B = true ∧
            __smtx_type_wf_rec B native_reflist_nil = true := by
    simpa [__smtx_type_wf, native_and] using h
  exact type_default_typed_canonical_of_inhabited_wf_rec A hAll.1 hAll.2.1

private theorem type_default_typed_canonical_of_set_element_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Set A) = true) :
    __smtx_typeof_value (__smtx_type_default A) = A ∧
      __smtx_value_canonical (__smtx_type_default A) := by
  have hAll :
      native_inhabited_type (SmtType.Set A) = true ∧
        native_inhabited_type A = true ∧
          __smtx_type_wf_rec A native_reflist_nil = true := by
    simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
  exact type_default_typed_canonical_of_inhabited_wf_rec A hAll.2.1 hAll.2.2

private theorem map_diff_default_typed_canonical_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.map_diff t1 t2)) :
    ∀ {A : SmtType},
      __smtx_typeof (SmtTerm.map_diff t1 t2) = A ->
        __smtx_typeof_value (__smtx_type_default A) = A ∧
          __smtx_value_canonical (__smtx_type_default A) := by
  intro A hA
  rcases map_diff_args_of_non_none ht with hMap | hSet
  · rcases hMap with ⟨D, R, h1, h2, hRes⟩
    have hMapWf := smt_map_wf_of_non_none_type t1 D R h1
    have hDA : D = A := hRes.symm.trans hA
    rw [← hDA]
    exact type_default_typed_canonical_of_map_domain_wf hMapWf
  · rcases hSet with ⟨D, h1, h2, hRes⟩
    have hSetWf := smt_set_wf_of_non_none_type t1 D h1
    have hDA : D = A := hRes.symm.trans hA
    rw [← hDA]
    exact type_default_typed_canonical_of_set_element_wf hSetWf

/-- Induction lemma proving type preservation for supported SMT terms in total typed models. -/
private theorem supported_type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hs : supported_preservation_term t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  cases hs with
  | boolean b =>
      exact typeof_value_model_eval_boolean M b
  | numeral n =>
      exact typeof_value_model_eval_numeral M n
  | rational q =>
      exact typeof_value_model_eval_rational M q
  | string s =>
      exact typeof_value_model_eval_string M s
  | binary w n =>
      exact typeof_value_model_eval_binary M w n ht
  | var s T hT =>
      exact typeof_value_model_eval_var M hM s T hT ht
  | uconst s T hT =>
      exact typeof_value_model_eval_uconst M hM s T hT ht
  | ite htc hsc ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_ite M _ _ _ ht
        (supported_type_preservation M hM _ htc hsc)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «exists» s T body =>
      exact typeof_value_model_eval_exists M s T body ht
  | «forall» s T body =>
      exact typeof_value_model_eval_forall M s T body ht
  | choice_nth s T body n =>
      exact typeof_value_model_eval_choice_nth M hM M s T body n ht
  | map_diff ht1 hs1 ht2 hs2 hDefault =>
      exact typeof_value_model_eval_map_diff M _ _ ht
        (fun {A} hA => (hDefault (A := A) hA).1)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «not» ht1 hs1 =>
      exact typeof_value_model_eval_not M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | «or» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_or M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «and» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_and M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «imp» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_imp M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | eq t1 t2 =>
      exact typeof_value_model_eval_eq M t1 t2 ht
  | dt_cons s d i =>
      exact typeof_value_model_eval_dt_cons M s d i ht
  | dt_sel ht1 hT hWrongMapWF htx hsx =>
      exact typeof_value_model_eval_dt_sel M hM _ _ _ _ _ ht1 hWrongMapWF hT
        (supported_type_preservation M hM _ htx hsx)
  | dt_tester s d i x =>
      exact typeof_value_model_eval_dt_tester M s d i x ht
  | @apply f x hTy hEval htf hsf htx hsx =>
      have hTy' :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTy']
        exact hNone
      rw [hEval M, hTy']
      exact typeof_value_model_eval_apply_generic M hM f x hNN
        (supported_type_preservation M hM f htf hsf)
        (supported_type_preservation M hM x htx hsx)

theorem generic_apply_subterms_non_none
    {f x : SmtTerm}
    (hTy : generic_apply_type f x)
    (ht : term_has_non_none_type (SmtTerm.Apply f x)) :
    term_has_non_none_type f ∧ term_has_non_none_type x := by
  have hApply : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    unfold generic_apply_type at hTy
    unfold term_has_non_none_type at ht
    rw [hTy] at ht
    exact ht
  rcases typeof_apply_non_none_cases hApply with ⟨A, B, hF, hX, hA, hB⟩
  constructor
  · unfold term_has_non_none_type
    cases hF with
    | inl hF =>
        rw [hF]
        simp
    | inr hF =>
        rw [hF]
        simp
  · unfold term_has_non_none_type
    rw [hX]
    exact hA

/-- Derives inhabitedness of the selector result type from a non-`None` selector term. -/
theorem dt_sel_term_inhabited_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) := by
  have hResTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) =
        __smtx_ret_typeof_sel s d i j :=
    dt_sel_term_typeof_of_non_none ht
  have hGuardNN :
      __smtx_typeof_guard_wf
          (__smtx_ret_typeof_sel s d i j)
          (__smtx_typeof_apply
            (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))
            (__smtx_typeof x)) ≠
        SmtType.None := by
    simpa [term_has_non_none_type, __smtx_typeof] using ht
  have hResInh : type_inhabited (__smtx_ret_typeof_sel s d i j) :=
    smtx_typeof_guard_wf_inhabited_of_non_none
      (__smtx_ret_typeof_sel s d i j)
      (__smtx_typeof_apply
        (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))
        (__smtx_typeof x))
      hGuardNN
  rwa [hResTy]

/-- Packages the generic-application constructor once the recursive support facts are available. -/
theorem supported_generic_apply_of_non_none
    {f x : SmtTerm}
    (hTy : generic_apply_type f x)
    (hEval : generic_apply_eval f x)
    (ht : term_has_non_none_type (SmtTerm.Apply f x))
    (hsf : supported_preservation_term f)
    (hsx : supported_preservation_term x) :
    supported_preservation_term (SmtTerm.Apply f x) := by
  have hArgs := generic_apply_subterms_non_none hTy ht
  exact supported_preservation_term.apply hTy hEval hArgs.1 hsf hArgs.2 hsx

/-- Generic application facts for heads other than datatype selectors/testers. -/
theorem generic_apply_facts_of_not_special
    {f x : SmtTerm}
    (hNoSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hNoTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x ∧ generic_apply_eval f x := by
  constructor
  · unfold generic_apply_type
    cases f <;> simp [__smtx_typeof]
    · exact False.elim (hNoSel _ _ _ _ rfl)
    · exact False.elim (hNoTester _ _ _ rfl)
  · intro M
    cases f with
    | DtSel s d i j =>
        exact False.elim (hNoSel s d i j rfl)
    | DtTester s d i =>
        exact False.elim (hNoTester s d i rfl)
    | _ =>
        simp [__smtx_model_eval]

/-- Every non-`None` SMT term lies in the supported preservation fragment. -/
theorem supported_preservation_term_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t -> supported_preservation_term t := by
  let rec go (t : SmtTerm) (ht : term_has_non_none_type t) : supported_preservation_term t := by
    match t with
    | SmtTerm.None =>
        have hNone : __smtx_typeof SmtTerm.None = SmtType.None := by
          rw [__smtx_typeof.eq_def]
        exact False.elim (ht hNone)
    | SmtTerm.Boolean b =>
        exact supported_preservation_term.boolean b
    | SmtTerm.Numeral n =>
        exact supported_preservation_term.numeral n
    | SmtTerm.Rational q =>
        exact supported_preservation_term.rational q
    | SmtTerm.String s =>
        exact supported_preservation_term.string s
    | SmtTerm.Binary w n =>
        exact supported_preservation_term.binary w n
    | SmtTerm.Var s T =>
        have hTNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
          intro hNone
          apply ht
          simpa [__smtx_typeof] using hNone
        exact supported_preservation_term.var s T
          (smtx_typeof_guard_wf_inhabited_of_non_none T T hTNN)
    | SmtTerm.ite c t1 t2 =>
        rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
        have htc : term_has_non_none_type c := by
          unfold term_has_non_none_type
          rw [hc]
          simp
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [h1]
          exact hT
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [h2]
          exact hT
        exact supported_preservation_term.ite
          htc (go c htc) ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.eq t1 t2 =>
        exact supported_preservation_term.eq t1 t2
    | SmtTerm.exists s T body =>
        exact supported_preservation_term.exists s T body
    | SmtTerm.forall s T body =>
        exact supported_preservation_term.forall s T body
    | SmtTerm.choice_nth s T body n =>
        exact supported_preservation_term.choice_nth s T body n
    | SmtTerm.map_diff t1 t2 =>
        rcases map_diff_args_of_non_none ht with hMap | hSet
        · rcases hMap with ⟨A, B, h1, h2, hTy⟩
          have ht1 : term_has_non_none_type t1 := by
            unfold term_has_non_none_type
            rw [h1]
            simp
          have ht2 : term_has_non_none_type t2 := by
            unfold term_has_non_none_type
            rw [h2]
            simp
          exact supported_preservation_term.map_diff
            ht1 (go t1 ht1) ht2 (go t2 ht2)
            (map_diff_default_typed_canonical_of_non_none ht)
        · rcases hSet with ⟨A, h1, h2, hTy⟩
          have ht1 : term_has_non_none_type t1 := by
            unfold term_has_non_none_type
            rw [h1]
            simp
          have ht2 : term_has_non_none_type t2 := by
            unfold term_has_non_none_type
            rw [h2]
            simp
          exact supported_preservation_term.map_diff
            ht1 (go t1 ht1) ht2 (go t2 ht2)
            (map_diff_default_typed_canonical_of_non_none ht)
    | SmtTerm.DtCons s d i =>
        exact supported_preservation_term.dt_cons s d i
    | SmtTerm.DtSel s d i j =>
        have hNone : __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := by
          rw [__smtx_typeof.eq_def]
        exact False.elim (ht hNone)
    | SmtTerm.DtTester s d i =>
        have hNone : __smtx_typeof (SmtTerm.DtTester s d i) = SmtType.None := by
          rw [__smtx_typeof.eq_def]
        exact False.elim (ht hNone)
    | SmtTerm.UConst s T =>
        have hTNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
          intro hNone
          apply ht
          simpa [__smtx_typeof] using hNone
        exact supported_preservation_term.uconst s T
          (smtx_typeof_guard_wf_inhabited_of_non_none T T hTNN)
    | SmtTerm.not t =>
        have hArg : __smtx_typeof t = SmtType.Bool := by
          unfold term_has_non_none_type at ht
          rw [typeof_not_eq] at ht
          cases h : __smtx_typeof t <;>
            simp [native_ite, native_Teq, h] at ht
          rfl
        have hArgNN : term_has_non_none_type t := by
          unfold term_has_non_none_type
          rw [hArg]
          simp
        exact supported_preservation_term.not hArgNN (go t hArgNN)
    | SmtTerm.or t1 t2 =>
        have hArgs :=
          bool_binop_args_bool_of_non_none (op := SmtTerm.or) (typeof_or_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [hArgs.1]
          simp
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [hArgs.2]
          simp
        exact supported_preservation_term.or ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.and t1 t2 =>
        have hArgs :=
          bool_binop_args_bool_of_non_none (op := SmtTerm.and) (typeof_and_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [hArgs.1]
          simp
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [hArgs.2]
          simp
        exact supported_preservation_term.and ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.imp t1 t2 =>
        have hArgs :=
          bool_binop_args_bool_of_non_none (op := SmtTerm.imp) (typeof_imp_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [hArgs.1]
          simp
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [hArgs.2]
          simp
        exact supported_preservation_term.imp ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.Apply f x =>
        cases f with
        | «exists» s T body =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.exists s T body) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.exists s T body) hArgs.1)
              (go x hArgs.2)
        | «forall» s T body =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.forall s T body) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.forall s T body) hArgs.1)
              (go x hArgs.2)
        | choice_nth s T body n =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.choice_nth s T body n) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.choice_nth s T body n) hArgs.1)
              (go x hArgs.2)
        | map_diff t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.map_diff t1 t2) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.map_diff t1 t2) hArgs.1)
              (go x hArgs.2)
        | DtSel s d i j =>
            have htx : term_has_non_none_type x := by
              have hx : __smtx_typeof x = SmtType.Datatype s d :=
                dt_sel_arg_datatype_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht
              unfold term_has_non_none_type
              rw [hx]
              simp
            exact supported_preservation_term.dt_sel
              ht
              (dt_sel_term_inhabited_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht)
              (dt_sel_wrong_map_type_wf_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht)
              htx
              (go x htx)
        | DtTester s d i =>
            exact supported_preservation_term.dt_tester s d i x
        | None =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.None) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go SmtTerm.None hArgs.1)
              (go x hArgs.2)
        | Boolean b =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Boolean b) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Boolean b) hArgs.1)
              (go x hArgs.2)
        | Numeral n =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Numeral n) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Numeral n) hArgs.1)
              (go x hArgs.2)
        | Rational q =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Rational q) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Rational q) hArgs.1)
              (go x hArgs.2)
        | String s =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.String s) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.String s) hArgs.1)
              (go x hArgs.2)
        | Binary w n =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Binary w n) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Binary w n) hArgs.1)
              (go x hArgs.2)
        | Apply f1 x1 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Apply f1 x1) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Apply f1 x1) hArgs.1)
              (go x hArgs.2)
        | Var s T =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Var s T) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Var s T) hArgs.1)
              (go x hArgs.2)
        | ite c t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.ite c t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.ite c t1 t2) hArgs.1)
              (go x hArgs.2)
        | eq t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.eq t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.eq t1 t2) hArgs.1)
              (go x hArgs.2)
        | DtCons s d i =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.DtCons s d i) (x := x)
              (by intro s' d' i' j hEq; cases hEq)
              (by intro s' d' i' hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.DtCons s d i) hArgs.1)
              (go x hArgs.2)
        | UConst s T =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.UConst s T) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.UConst s T) hArgs.1)
              (go x hArgs.2)
        | not t =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.not t) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.not t) hArgs.1)
              (go x hArgs.2)
        | or t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.or t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.or t1 t2) hArgs.1)
              (go x hArgs.2)
        | and t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.and t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.and t1 t2) hArgs.1)
              (go x hArgs.2)
        | imp t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.imp t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.imp t1 t2) hArgs.1)
              (go x hArgs.2)
  exact go

/-- Main type-preservation theorem for evaluation of non-`None` SMT terms in total typed models. -/
theorem type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  exact supported_type_preservation M hM t ht
    (supported_preservation_term_of_non_none t ht)

/-- Backwards-compatible wrapper for `type_preservation`. -/
theorem smt_model_eval_preserves_type_of_non_none
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
    term_has_non_none_type t ->
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  intro ht
  exact type_preservation M hM t ht

/-- States that evaluating a Boolean-typed SMT term yields a Boolean value. -/
theorem smt_model_eval_bool_is_boolean
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
  __smtx_typeof t = SmtType.Bool ->
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  intro hTy
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact bool_value_canonical hPres

/-- Derives SMT evaluation type preservation for terms in the supported fragment. -/
theorem smt_model_eval_preserves_type_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (T : SmtType)
    (hTy : __smtx_typeof t = T)
    (hNonNone : T ≠ SmtType.None)
    (_hs : supported_preservation_term t) :
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact hNonNone
  simpa [hTy] using
    type_preservation M hM t hNN

/-- Derives Boolean-value evaluation for supported Boolean-typed SMT terms. -/
theorem smt_model_eval_bool_is_boolean_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool)
    (hs : supported_preservation_term t) :
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool :=
    smt_model_eval_preserves_type_of_supported M hM t SmtType.Bool hTy (by simp) hs
  exact bool_value_canonical hPres


end Smtm
