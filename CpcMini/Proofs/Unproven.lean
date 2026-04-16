import CpcMini.Spec
import CpcMini.Proofs.SmtModelLemmas
import CpcMini.Proofs.TypePreservation

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Extracts non-`None` typing of the head and argument from a generic application. -/
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
    simpa [__smtx_typeof] using ht
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

/-- Every non-`None` SMT term lies in the supported preservation fragment. -/
theorem supported_preservation_term_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t -> supported_preservation_term t := by
  let rec go (t : SmtTerm) :
      term_has_non_none_type t -> supported_preservation_term t := by
    cases t <;> intro ht
    case None =>
      exfalso
      exact ht rfl
    case Boolean b =>
      exact supported_preservation_term.boolean b
    case Numeral n =>
      exact supported_preservation_term.numeral n
    case Rational q =>
      exact supported_preservation_term.rational q
    case String s =>
      exact supported_preservation_term.string s
    case Binary w n =>
      exact supported_preservation_term.binary w n
    case Var s T =>
      have hT : type_inhabited T :=
        smtx_typeof_guard_wf_inhabited_of_non_none T T (by
          simpa [term_has_non_none_type, __smtx_typeof] using ht)
      exact supported_preservation_term.var s T hT
    case ite c t1 t2 =>
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
    case eq t1 t2 =>
      exact supported_preservation_term.eq t1 t2
    case «exists» s T =>
      exfalso
      exact ht rfl
    case «forall» s T =>
      exfalso
      exact ht rfl
    case choice s T =>
      exfalso
      exact ht rfl
    case DtCons s d i =>
      exact supported_preservation_term.dt_cons s d i
    case DtSel s d i j =>
      exfalso
      exact ht rfl
    case DtTester s d i =>
      exfalso
      exact ht rfl
    case UConst s T =>
      have hT : type_inhabited T :=
        smtx_typeof_guard_wf_inhabited_of_non_none T T (by
          simpa [term_has_non_none_type, __smtx_typeof] using ht)
      exact supported_preservation_term.uconst s T hT
    case not t =>
      have hArg : __smtx_typeof t = SmtType.Bool := by
        unfold term_has_non_none_type at ht
        cases h : __smtx_typeof t <;>
          simp [__smtx_typeof, native_ite, native_Teq, h] at ht
        simp
      have hArgNN : term_has_non_none_type t := by
        unfold term_has_non_none_type
        rw [hArg]
        simp
      exact supported_preservation_term.not hArgNN (go t hArgNN)
    case or t1 t2 =>
      have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl ht
      have ht1 : term_has_non_none_type t1 := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        simp
      have ht2 : term_has_non_none_type t2 := by
        unfold term_has_non_none_type
        rw [hArgs.2]
        simp
      exact supported_preservation_term.or ht1 (go t1 ht1) ht2 (go t2 ht2)
    case and t1 t2 =>
      have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl ht
      have ht1 : term_has_non_none_type t1 := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        simp
      have ht2 : term_has_non_none_type t2 := by
        unfold term_has_non_none_type
        rw [hArgs.2]
        simp
      exact supported_preservation_term.and ht1 (go t1 ht1) ht2 (go t2 ht2)
    case imp t1 t2 =>
      have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl ht
      have ht1 : term_has_non_none_type t1 := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        simp
      have ht2 : term_has_non_none_type t2 := by
        unfold term_has_non_none_type
        rw [hArgs.2]
        simp
      exact supported_preservation_term.imp ht1 (go t1 ht1) ht2 (go t2 ht2)
    case Apply f x =>
      cases f
      case «exists» s T =>
        exact supported_preservation_term.exists s T x
      case «forall» s T =>
        exact supported_preservation_term.forall s T x
      case choice s T =>
        exact supported_preservation_term.choice s T x
      case DtSel s d i j =>
        have htx : term_has_non_none_type x := by
          have hx : __smtx_typeof x = SmtType.Datatype s d :=
            dt_sel_arg_datatype_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht
          unfold term_has_non_none_type
          rw [hx]
          simp
        exact supported_preservation_term.dt_sel
          ht
          (dt_sel_term_inhabited_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht)
          htx
          (go x htx)
      case DtTester s d i =>
        exact supported_preservation_term.dt_tester s d i x
      case None =>
        have hTy : generic_apply_type SmtTerm.None x := rfl
        have hEval : generic_apply_eval SmtTerm.None x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go SmtTerm.None hArgs.1)
          (go x hArgs.2)
      case Boolean b =>
        have hTy : generic_apply_type (SmtTerm.Boolean b) x := rfl
        have hEval : generic_apply_eval (SmtTerm.Boolean b) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.Boolean b) hArgs.1)
          (go x hArgs.2)
      case Numeral n =>
        have hTy : generic_apply_type (SmtTerm.Numeral n) x := rfl
        have hEval : generic_apply_eval (SmtTerm.Numeral n) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.Numeral n) hArgs.1)
          (go x hArgs.2)
      case Rational q =>
        have hTy : generic_apply_type (SmtTerm.Rational q) x := rfl
        have hEval : generic_apply_eval (SmtTerm.Rational q) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.Rational q) hArgs.1)
          (go x hArgs.2)
      case String s =>
        have hTy : generic_apply_type (SmtTerm.String s) x := rfl
        have hEval : generic_apply_eval (SmtTerm.String s) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.String s) hArgs.1)
          (go x hArgs.2)
      case Binary w n =>
        have hTy : generic_apply_type (SmtTerm.Binary w n) x := rfl
        have hEval : generic_apply_eval (SmtTerm.Binary w n) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.Binary w n) hArgs.1)
          (go x hArgs.2)
      case Apply f1 x1 =>
        have hTy : generic_apply_type (SmtTerm.Apply f1 x1) x := rfl
        have hEval : generic_apply_eval (SmtTerm.Apply f1 x1) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.Apply f1 x1) hArgs.1)
          (go x hArgs.2)
      case Var s T =>
        have hTy : generic_apply_type (SmtTerm.Var s T) x := rfl
        have hEval : generic_apply_eval (SmtTerm.Var s T) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.Var s T) hArgs.1)
          (go x hArgs.2)
      case ite c t1 t2 =>
        have hTy : generic_apply_type (SmtTerm.ite c t1 t2) x := rfl
        have hEval : generic_apply_eval (SmtTerm.ite c t1 t2) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.ite c t1 t2) hArgs.1)
          (go x hArgs.2)
      case eq t1 t2 =>
        have hTy : generic_apply_type (SmtTerm.eq t1 t2) x := rfl
        have hEval : generic_apply_eval (SmtTerm.eq t1 t2) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.eq t1 t2) hArgs.1)
          (go x hArgs.2)
      case DtCons s d i =>
        have hTy : generic_apply_type (SmtTerm.DtCons s d i) x := rfl
        have hEval : generic_apply_eval (SmtTerm.DtCons s d i) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.DtCons s d i) hArgs.1)
          (go x hArgs.2)
      case UConst s T =>
        have hTy : generic_apply_type (SmtTerm.UConst s T) x := rfl
        have hEval : generic_apply_eval (SmtTerm.UConst s T) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.UConst s T) hArgs.1)
          (go x hArgs.2)
      case not t =>
        have hTy : generic_apply_type (SmtTerm.not t) x := rfl
        have hEval : generic_apply_eval (SmtTerm.not t) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.not t) hArgs.1)
          (go x hArgs.2)
      case or t1 t2 =>
        have hTy : generic_apply_type (SmtTerm.or t1 t2) x := rfl
        have hEval : generic_apply_eval (SmtTerm.or t1 t2) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.or t1 t2) hArgs.1)
          (go x hArgs.2)
      case and t1 t2 =>
        have hTy : generic_apply_type (SmtTerm.and t1 t2) x := rfl
        have hEval : generic_apply_eval (SmtTerm.and t1 t2) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.and t1 t2) hArgs.1)
          (go x hArgs.2)
      case imp t1 t2 =>
        have hTy : generic_apply_type (SmtTerm.imp t1 t2) x := rfl
        have hEval : generic_apply_eval (SmtTerm.imp t1 t2) x := by intro M; rfl
        have hArgs := generic_apply_subterms_non_none hTy ht
        exact supported_generic_apply_of_non_none hTy hEval ht
          (go (SmtTerm.imp t1 t2) hArgs.1)
          (go x hArgs.2)
  exact go

/-- Type preservation for non-`None` SMT terms in total typed models. -/
theorem smt_model_eval_preserves_type_of_non_none
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
    term_has_non_none_type t ->
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  intro ht
  exact supported_type_preservation M hM t ht
    (supported_preservation_term_of_non_none t ht)

/-- States that SMT evaluation preserves any non-`None` expected type in total typed models. -/
theorem smt_model_eval_preserves_type
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (T : SmtType) :
  __smtx_typeof t = T ->
  T ≠ SmtType.None ->
  smt_type_inhabited T ->
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  intro hTy hNonNone _hInh
  simpa [hTy] using
    smt_model_eval_preserves_type_of_non_none M hM t (by
      unfold term_has_non_none_type
      rw [hTy]
      exact hNonNone)

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
    (hInh : smt_type_inhabited T)
    (hs : supported_preservation_term t) :
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact hNonNone
  have hTermInh : term_has_inhabited_type t := by
    unfold term_has_inhabited_type type_inhabited
    rw [hTy]
    simpa [smt_type_inhabited] using hInh
  simpa [hTy] using
    supported_type_preservation_of_inhabited_type M hM t hNN hTermInh hs

/-- Derives Boolean-value evaluation for supported Boolean-typed SMT terms. -/
theorem smt_model_eval_bool_is_boolean_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool)
    (hs : supported_preservation_term t) :
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool :=
    smt_model_eval_preserves_type_of_supported M hM t SmtType.Bool hTy (by simp)
      smt_type_inhabited_bool hs
  exact bool_value_canonical hPres

namespace RuleProofs

/-- Transfers EO typing information to the translated SMT term when the translation is defined. -/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = T ->
  __smtx_typeof s = __eo_to_smt_type T := by
  sorry

end RuleProofs
