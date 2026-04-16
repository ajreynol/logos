import CpcMini.Spec
import CpcMini.Proofs.SmtModelLemmas
import CpcMini.Proofs.TypePreservation
import CpcMini.Proofs.Translation

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

/-- Derives `eo_typeof_eq_self` from `not_stuck`. -/
private theorem eo_typeof_eq_self_of_not_stuck
    (A : Term)
    (hA : A ≠ Term.Stuck) :
    __eo_typeof_eq A A = Term.Bool := by
  cases A <;>
    try simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_teq, native_ite, native_not,
      SmtEval.native_not]
  exact False.elim (hA rfl)

/-- A translated sequence type is never SMT `Bool`. -/
private theorem smtx_typeof_guard_seq_ne_bool
    (T : SmtType) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.Bool := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never SMT `Bool`. -/
private theorem smtx_typeof_guard_fun_ne_bool
    (T U : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠ SmtType.Bool := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never SMT `Bool`. -/
private theorem smtx_typeof_guard_dtc_app_ne_bool
    (T U : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠ SmtType.Bool := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT function type. -/
private theorem smtx_typeof_guard_dtc_app_ne_fun
    (T U A B : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠ SmtType.FunType A B := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT constructor-application type. -/
private theorem smtx_typeof_guard_fun_ne_dtc_app
    (T U A B : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠ SmtType.DtcAppType A B := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated sequence type is never an SMT constructor-application type. -/
private theorem smtx_typeof_guard_seq_ne_dtc_app
    (T A B : SmtType) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.DtcAppType A B := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated sequence type is never an SMT bit-vector type. -/
private theorem smtx_typeof_guard_seq_ne_bitvec
    (T : SmtType) (w : native_Nat) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.BitVec w := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT bit-vector type. -/
private theorem smtx_typeof_guard_fun_ne_bitvec
    (T U : SmtType) (w : native_Nat) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠ SmtType.BitVec w := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT bit-vector type. -/
private theorem smtx_typeof_guard_dtc_app_ne_bitvec
    (T U : SmtType) (w : native_Nat) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠ SmtType.BitVec w := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- Derives `eo_typeof_bool` from `smt_bool`. -/
private theorem eo_to_smt_type_eq_bool
    {T : Term} :
    __eo_to_smt_type T = SmtType.Bool ->
    T = Term.Bool := by
  cases T with
  | Apply f x =>
      cases f with
      | BitVec =>
          cases x with
          | Numeral n =>
              by_cases hz : native_zleq 0 n = true <;>
                simp [__eo_to_smt_type, native_ite, hz]
          | _ =>
              simp [__eo_to_smt_type]
      | Seq =>
          intro h
          exact False.elim ((smtx_typeof_guard_seq_ne_bool (__eo_to_smt_type x))
            (by simpa [__eo_to_smt_type] using h))
      | Apply g y =>
          cases g <;> try simp [__eo_to_smt_type]
          case FunType =>
            intro h
            exact False.elim ((smtx_typeof_guard_fun_ne_bool (__eo_to_smt_type y) (__eo_to_smt_type x))
              (by simpa [__eo_to_smt_type] using h))
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      intro h
      exact False.elim ((smtx_typeof_guard_dtc_app_ne_bool (__eo_to_smt_type T) (__eo_to_smt_type U))
        (by simpa [__eo_to_smt_type] using h))
  | _ =>
      simp [__eo_to_smt_type]

/-- Derives `eo_typeof_bool` from `smt_bool`. -/
private theorem eo_typeof_bool_of_smt_bool
    {t : Term}
    (hRec : __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (hBool : __smtx_typeof (__eo_to_smt t) = SmtType.Bool) :
    __eo_typeof t = Term.Bool := by
  have hTy : __eo_to_smt_type (__eo_typeof t) = SmtType.Bool := by
    rw [← hRec, hBool]
  exact eo_to_smt_type_eq_bool hTy

/-- Characterizes `__smtx_typeof_guard` producing a function type. -/
private theorem smtx_typeof_guard_eq_fun_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.FunType A B ↔
      T ≠ SmtType.None ∧ U = SmtType.FunType A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, native_ite, native_Teq]
  · simp [hT, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT function type. -/
private theorem eo_to_smt_type_eq_fun_iff
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T = SmtType.FunType A B ↔
      ∃ T1 T2,
        T = Term.Apply (Term.Apply Term.FunType T1) T2 ∧
        __eo_to_smt_type T1 = A ∧
        __eo_to_smt_type T2 = B ∧
        __eo_to_smt_type T1 ≠ SmtType.None ∧
        __eo_to_smt_type T2 ≠ SmtType.None := by
  constructor
  · intro h
    cases T with
    | Apply f x =>
        cases f with
        | Apply g y =>
            cases g with
            | FunType =>
                have hOuter :
                    __smtx_typeof_guard (__eo_to_smt_type y)
                      (__smtx_typeof_guard (__eo_to_smt_type x)
                        (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))) =
                      SmtType.FunType A B := by
                  simpa [__eo_to_smt_type] using h
                rcases smtx_typeof_guard_eq_fun_iff.mp hOuter with ⟨hyNN, hInner⟩
                rcases smtx_typeof_guard_eq_fun_iff.mp hInner with ⟨hxNN, hFun⟩
                injection hFun with hA hB
                exact ⟨y, x, rfl, hA, hB, hyNN, hxNN⟩
            | _ =>
                simp [__eo_to_smt_type] at h
        | BitVec =>
            cases x with
            | Numeral n =>
                by_cases hz : native_zleq 0 n = true <;>
                  simp [__eo_to_smt_type, native_ite, hz] at h
            | _ =>
                simp [__eo_to_smt_type] at h
        | Seq =>
            by_cases hx : __eo_to_smt_type x = SmtType.None
            · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, native_ite, native_Teq] at h
            · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, native_ite, native_Teq] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | DtcAppType T1 T2 =>
        exact False.elim
          ((smtx_typeof_guard_dtc_app_ne_fun
              (__eo_to_smt_type T1) (__eo_to_smt_type T2) A B)
            (by simpa [__eo_to_smt_type] using h))
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨T1, T2, rfl, hT1, hT2, hT1NN, hT2NN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hT1]
    have hBNN : B ≠ SmtType.None := by
      rwa [← hT2]
    simp [__eo_to_smt_type, hT1, hT2, hANN, hBNN,
      __smtx_typeof_guard, native_ite, native_Teq]

/-- Characterizes `__smtx_typeof_guard` producing a constructor-application type. -/
private theorem smtx_typeof_guard_eq_dtc_app_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.DtcAppType A B ↔
      T ≠ SmtType.None ∧ U = SmtType.DtcAppType A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, native_ite, native_Teq]
  · simp [hT, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT constructor-application type. -/
private theorem eo_to_smt_type_eq_dtc_app_iff
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T = SmtType.DtcAppType A B ↔
      ∃ T1 T2,
        T = Term.DtcAppType T1 T2 ∧
        __eo_to_smt_type T1 = A ∧
        __eo_to_smt_type T2 = B ∧
        __eo_to_smt_type T1 ≠ SmtType.None ∧
        __eo_to_smt_type T2 ≠ SmtType.None := by
  constructor
  · intro h
    cases T with
    | DtcAppType T1 T2 =>
        have hOuter :
            __smtx_typeof_guard (__eo_to_smt_type T1)
              (__smtx_typeof_guard (__eo_to_smt_type T2)
                (SmtType.DtcAppType (__eo_to_smt_type T1) (__eo_to_smt_type T2))) =
              SmtType.DtcAppType A B := by
          simpa [__eo_to_smt_type] using h
        rcases smtx_typeof_guard_eq_dtc_app_iff.mp hOuter with ⟨hT1NN, hInner⟩
        rcases smtx_typeof_guard_eq_dtc_app_iff.mp hInner with ⟨hT2NN, hDtc⟩
        injection hDtc with hA hB
        exact ⟨T1, T2, rfl, hA, hB, hT1NN, hT2NN⟩
    | Apply f x =>
        cases f with
        | Apply g y =>
            cases g with
            | FunType =>
                exact False.elim
                  ((smtx_typeof_guard_fun_ne_dtc_app
                      (__eo_to_smt_type y) (__eo_to_smt_type x) A B)
                    (by simpa [__eo_to_smt_type] using h))
            | _ =>
                simp [__eo_to_smt_type] at h
        | BitVec =>
            cases x with
            | Numeral n =>
                by_cases hz : native_zleq 0 n = true <;>
                  simp [__eo_to_smt_type, native_ite, hz] at h
            | _ =>
                simp [__eo_to_smt_type] at h
        | Seq =>
            exact False.elim
              ((smtx_typeof_guard_seq_ne_dtc_app (__eo_to_smt_type x) A B)
                (by simpa [__eo_to_smt_type] using h))
        | _ =>
            simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨T1, T2, rfl, hT1, hT2, hT1NN, hT2NN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hT1]
    have hBNN : B ≠ SmtType.None := by
      rwa [← hT2]
    simp [__eo_to_smt_type, hT1, hT2, hANN, hBNN,
      __smtx_typeof_guard, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT datatype. -/
private theorem eo_to_smt_type_eq_datatype_iff
    {T : Term} {s : native_String} {d : SmtDatatype} :
    __eo_to_smt_type T = SmtType.Datatype s d ↔
      ∃ d0,
        T = Term.DatatypeType s d0 ∧
        __eo_to_smt_datatype d0 = d := by
  constructor
  · intro h
    cases T with
    | DatatypeType s0 d0 =>
        injection h with hs hd
        subst hs
        exact ⟨d0, rfl, hd⟩
    | Apply f x =>
        exact False.elim (TranslationProofs.eo_to_smt_type_apply_ne_datatype f x s d h)
    | DtcAppType T1 T2 =>
        exact False.elim (TranslationProofs.eo_to_smt_type_dtc_app_ne_datatype T1 T2 s d h)
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨d0, rfl, hd⟩
    simp [__eo_to_smt_type, hd]

/-- Characterizes translated EO types equal to an SMT type reference. -/
private theorem eo_to_smt_type_eq_typeref_iff
    {T : Term} {s : native_String} :
    __eo_to_smt_type T = SmtType.TypeRef s ↔
      T = Term.DatatypeTypeRef s := by
  constructor
  · intro h
    cases T with
    | DatatypeTypeRef s0 =>
        simpa [__eo_to_smt_type] using h
    | Apply f x =>
        exact False.elim (TranslationProofs.eo_to_smt_type_apply_ne_typeref f x s h)
    | DtcAppType T1 T2 =>
        exact False.elim
          ((TranslationProofs.smtx_typeof_guard_dtc_app_ne_typeref
              (__eo_to_smt_type T1) (__eo_to_smt_type T2) s)
            (by simpa [__eo_to_smt_type] using h))
    | _ =>
        simp [__eo_to_smt_type] at h
  · intro h
    simpa [h, __eo_to_smt_type]

/-- Characterizes translated EO types equal to an SMT bit-vector type. -/
private theorem eo_to_smt_type_eq_bitvec_iff
    {T : Term} {w : native_Nat} :
    __eo_to_smt_type T = SmtType.BitVec w ↔
      ∃ n : native_Int,
        T = Term.Apply Term.BitVec (Term.Numeral n) ∧
        native_zleq 0 n = true ∧
        native_int_to_nat n = w := by
  constructor
  · intro h
    cases T with
    | Apply f x =>
        cases f with
        | BitVec =>
            cases x with
            | Numeral n =>
                by_cases hz : native_zleq 0 n = true
                · simp [__eo_to_smt_type, native_ite, hz] at h
                  exact ⟨n, rfl, hz, h⟩
                · simp [__eo_to_smt_type, native_ite, hz] at h
            | _ =>
                simp [__eo_to_smt_type] at h
        | Apply g y =>
            cases g with
            | FunType =>
                exact False.elim
                  ((smtx_typeof_guard_fun_ne_bitvec
                      (__eo_to_smt_type y) (__eo_to_smt_type x) w)
                    (by simpa [__eo_to_smt_type] using h))
            | _ =>
                simp [__eo_to_smt_type] at h
        | Seq =>
            exact False.elim
              ((smtx_typeof_guard_seq_ne_bitvec (__eo_to_smt_type x) w)
                (by simpa [__eo_to_smt_type] using h))
        | _ =>
            simp [__eo_to_smt_type] at h
    | DtcAppType T1 T2 =>
        exact False.elim
          ((smtx_typeof_guard_dtc_app_ne_bitvec (__eo_to_smt_type T1) (__eo_to_smt_type T2) w)
            (by simpa [__eo_to_smt_type] using h))
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨n, rfl, hz, hw⟩
    simp [__eo_to_smt_type, native_ite, hz, hw]

/-- Extracts operand SMT typing information from a non-`None` equality term. -/
private theorem smtx_typeof_eq_operands_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.eq t1 t2)) :
    __smtx_typeof t1 = __smtx_typeof t2 ∧
      __smtx_typeof t1 ≠ SmtType.None := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard,
      native_ite, native_Teq, h1, h2] at ht
  all_goals
    refine ⟨?_, ?_⟩
    · simpa [h1, h2] using ht
    · simp [h1]

/-- Computes EO typing for generic double applications. -/
private theorem eo_typeof_double_apply_generic
    (g y x : Term)
    (hFun : g ≠ Term.FunType)
    (hOr : g ≠ Term.or)
    (hAnd : g ≠ Term.and)
    (hImp : g ≠ Term.imp)
    (hEq : g ≠ Term.eq) :
    __eo_typeof (Term.Apply (Term.Apply g y) x) =
      __eo_typeof_apply (__eo_typeof (Term.Apply g y)) (__eo_typeof x) := by
  cases g <;> try rfl
  case FunType =>
      exact False.elim (hFun rfl)
  case or =>
      exact False.elim (hOr rfl)
  case and =>
      exact False.elim (hAnd rfl)
  case imp =>
      exact False.elim (hImp rfl)
  case eq =>
      exact False.elim (hEq rfl)

/-- Computes EO typing for generic single applications. -/
private theorem eo_typeof_single_apply_generic
    (f x : Term)
    (hApply : ∀ g y, f ≠ Term.Apply g y)
    (hBitVec : f ≠ Term.BitVec)
    (hSeq : f ≠ Term.Seq)
    (hListCons : f ≠ Term.__eo_List_cons)
    (hNot : f ≠ Term.not) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  cases f <;> try rfl
  case Apply g y =>
      exact False.elim (hApply g y rfl)
  case BitVec =>
      exact False.elim (hBitVec rfl)
  case Seq =>
      exact False.elim (hSeq rfl)
  case __eo_List_cons =>
      exact False.elim (hListCons rfl)
  case not =>
      exact False.elim (hNot rfl)

/-- Computes SMT translation for generic double EO applications. -/
private theorem eo_to_smt_double_apply_generic
    (g y x : Term)
    (hOr : g ≠ Term.or)
    (hAnd : g ≠ Term.and)
    (hImp : g ≠ Term.imp)
    (hEq : g ≠ Term.eq) :
    __eo_to_smt (Term.Apply (Term.Apply g y) x) =
      SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x) := by
  cases g <;> try rfl
  case or =>
      exact False.elim (hOr rfl)
  case and =>
      exact False.elim (hAnd rfl)
  case imp =>
      exact False.elim (hImp rfl)
  case eq =>
      exact False.elim (hEq rfl)

/-- Computes SMT translation for generic single EO applications. -/
private theorem eo_to_smt_single_apply_generic
    (f x : Term)
    (hApply : ∀ g y, f ≠ Term.Apply g y)
    (hNot : f ≠ Term.not) :
    __eo_to_smt (Term.Apply f x) =
      SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x) := by
  cases f <;> try rfl
  case Apply g y =>
      exact False.elim (hApply g y rfl)
  case not =>
      exact False.elim (hNot rfl)

/-- Shows that translated SMT terms carry the type predicted by EO typing when the translation is defined. -/
private theorem eo_to_smt_typeof_matches_translation :
    ∀ (t : Term),
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t)
  | Term.__eo_pf p, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Int, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Real, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.BitVec, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Char, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Seq, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.__eo_List, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.__eo_List_nil, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.__eo_List_cons, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Bool, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Boolean b, _ => by
      simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof]
  | Term.Numeral n, _ => by
      simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof, __eo_lit_type_Numeral,
        __eo_to_smt_type]
  | Term.Rational r, _ => by
      simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof, __eo_lit_type_Rational,
        __eo_to_smt_type]
  | Term.String s, _ => by
      simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof, __eo_lit_type_String,
        __eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq]
  | Term.Binary w n, hNN => by
      have hWidth : native_zleq 0 w = true := by
        by_cases hw : native_zleq 0 w = true
        · exact hw
        · exfalso
          apply hNN
          simp [__eo_to_smt.eq_def, __smtx_typeof, native_ite, SmtEval.native_and, hw]
      have hSmt := TranslationProofs.smtx_typeof_binary_of_non_none w n
        (by simpa [__eo_to_smt.eq_def] using hNN)
      have hEo :
          __eo_to_smt_type (__eo_typeof (Term.Binary w n)) =
            SmtType.BitVec (native_int_to_nat w) := by
        simp [__eo_typeof, __eo_lit_type_Binary, __eo_mk_apply, __eo_len, __eo_to_smt_type,
          native_ite, hWidth]
      simpa [__eo_to_smt.eq_def] using hSmt.trans hEo.symm
  | Term.Type, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Stuck, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.FunType, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Var name T, hNN => by
      cases name with
      | String s =>
          simpa [__eo_to_smt.eq_def, __eo_typeof] using
            TranslationProofs.smtx_typeof_var_of_non_none s (__eo_to_smt_type T) hNN
      | _ =>
          exact False.elim (hNN (by simp [__eo_to_smt.eq_def, __smtx_typeof]))
  | Term.DatatypeType s d, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.DatatypeTypeRef s, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.DtcAppType T U, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.DtCons s d i, hNN => by
      sorry
  | Term.DtSel s d i j, hNN => by
      have hNone : __smtx_typeof (__eo_to_smt (Term.DtSel s d i j)) = SmtType.None := by
        simp [__eo_to_smt.eq_def, __smtx_typeof]
      exact (hNN hNone).elim
  | Term.USort i, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.UConst i T, hNN => by
      simpa [__eo_to_smt.eq_def, __eo_typeof] using
        TranslationProofs.smtx_typeof_uconst_of_non_none (native_uconst_id i) (__eo_to_smt_type T) hNN
  | Term.not, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.or, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.and, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.imp, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.eq, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Apply f x, hNN => by
      by_cases hApply : ∃ g y, f = Term.Apply g y
      · rcases hApply with ⟨g, y, rfl⟩
        by_cases hFun : g = Term.FunType
        · subst hFun
          have hTranslate :
              __eo_to_smt (Term.Apply (Term.Apply Term.FunType y) x) =
                SmtTerm.Apply (__eo_to_smt (Term.Apply Term.FunType y)) (__eo_to_smt x) := by
            rfl
          have hHeadTranslate :
              __eo_to_smt (Term.Apply Term.FunType y) =
                SmtTerm.Apply (__eo_to_smt Term.FunType) (__eo_to_smt y) := by
            exact eo_to_smt_single_apply_generic Term.FunType y
              (by intro g z h; cases h)
              (by intro h; cases h)
          have hHeadNone : __eo_to_smt Term.FunType = SmtTerm.None := by
            rw [__eo_to_smt.eq_def]
          have hNN' := hNN
          rw [hTranslate, hHeadTranslate, hHeadNone] at hNN'
          simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
        · by_cases hOr : g = Term.or
          · subst hOr
            have hTranslate :
                __eo_to_smt (Term.Apply (Term.Apply Term.or y) x) =
                  SmtTerm.or (__eo_to_smt y) (__eo_to_smt x) := by
              rw [__eo_to_smt.eq_def]
            have hApplyNN :
                term_has_non_none_type
                  (SmtTerm.or (__eo_to_smt y) (__eo_to_smt x)) := by
              unfold term_has_non_none_type
              simpa [hTranslate] using hNN
            have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl hApplyNN
            have h1NN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
              rw [hArgs.1]
              simp
            have h2NN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
              rw [hArgs.2]
              simp
            have hIy := eo_to_smt_typeof_matches_translation y h1NN
            have hIx := eo_to_smt_typeof_matches_translation x h2NN
            have hTyY : __eo_typeof y = Term.Bool :=
              eo_typeof_bool_of_smt_bool hIy hArgs.1
            have hTyX : __eo_typeof x = Term.Bool :=
              eo_typeof_bool_of_smt_bool hIx hArgs.2
            have hTy :
                __eo_typeof (Term.Apply (Term.Apply Term.or y) x) = Term.Bool := by
              simp [__eo_typeof, __eo_typeof_or, hTyY, hTyX]
            rw [hTy]
            exact TranslationProofs.smtx_typeof_translation_or_of_non_none y x hNN
          · by_cases hAnd : g = Term.and
            · subst hAnd
              have hTranslate :
                  __eo_to_smt (Term.Apply (Term.Apply Term.and y) x) =
                    SmtTerm.and (__eo_to_smt y) (__eo_to_smt x) := by
                rw [__eo_to_smt.eq_def]
              have hApplyNN :
                  term_has_non_none_type
                    (SmtTerm.and (__eo_to_smt y) (__eo_to_smt x)) := by
                unfold term_has_non_none_type
                simpa [hTranslate] using hNN
              have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl hApplyNN
              have h1NN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
                rw [hArgs.1]
                simp
              have h2NN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                rw [hArgs.2]
                simp
              have hIy := eo_to_smt_typeof_matches_translation y h1NN
              have hIx := eo_to_smt_typeof_matches_translation x h2NN
              have hTyY : __eo_typeof y = Term.Bool :=
                eo_typeof_bool_of_smt_bool hIy hArgs.1
              have hTyX : __eo_typeof x = Term.Bool :=
                eo_typeof_bool_of_smt_bool hIx hArgs.2
              have hTy :
                  __eo_typeof (Term.Apply (Term.Apply Term.and y) x) = Term.Bool := by
                simp [__eo_typeof, __eo_typeof_or, hTyY, hTyX]
              rw [hTy]
              exact TranslationProofs.smtx_typeof_translation_and_of_non_none y x hNN
            · by_cases hImp : g = Term.imp
              · subst hImp
                have hTranslate :
                    __eo_to_smt (Term.Apply (Term.Apply Term.imp y) x) =
                      SmtTerm.imp (__eo_to_smt y) (__eo_to_smt x) := by
                  rw [__eo_to_smt.eq_def]
                have hApplyNN :
                    term_has_non_none_type
                      (SmtTerm.imp (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  simpa [hTranslate] using hNN
                have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl hApplyNN
                have h1NN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
                  rw [hArgs.1]
                  simp
                have h2NN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                  rw [hArgs.2]
                  simp
                have hIy := eo_to_smt_typeof_matches_translation y h1NN
                have hIx := eo_to_smt_typeof_matches_translation x h2NN
                have hTyY : __eo_typeof y = Term.Bool :=
                  eo_typeof_bool_of_smt_bool hIy hArgs.1
                have hTyX : __eo_typeof x = Term.Bool :=
                  eo_typeof_bool_of_smt_bool hIx hArgs.2
                have hTy :
                    __eo_typeof (Term.Apply (Term.Apply Term.imp y) x) = Term.Bool := by
                  simp [__eo_typeof, __eo_typeof_or, hTyY, hTyX]
                rw [hTy]
                exact TranslationProofs.smtx_typeof_translation_imp_of_non_none y x hNN
              · by_cases hEq : g = Term.eq
                · subst hEq
                  sorry
                · sorry
      · by_cases hBitVec : f = Term.BitVec
        · subst hBitVec
          have hTranslate :
              __eo_to_smt (Term.Apply Term.BitVec x) =
                SmtTerm.Apply (__eo_to_smt Term.BitVec) (__eo_to_smt x) := by
            exact eo_to_smt_single_apply_generic Term.BitVec x
              (by intro g y h; cases h)
              (by intro h; cases h)
          have hHeadNone : __eo_to_smt Term.BitVec = SmtTerm.None := by
            rw [__eo_to_smt.eq_def]
          have hNN' := hNN
          rw [hTranslate, hHeadNone] at hNN'
          simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
        · by_cases hSeq : f = Term.Seq
          · subst hSeq
            have hTranslate :
                __eo_to_smt (Term.Apply Term.Seq x) =
                  SmtTerm.Apply (__eo_to_smt Term.Seq) (__eo_to_smt x) := by
              exact eo_to_smt_single_apply_generic Term.Seq x
                (by intro g y h; cases h)
                (by intro h; cases h)
            have hHeadNone : __eo_to_smt Term.Seq = SmtTerm.None := by
              rw [__eo_to_smt.eq_def]
            have hNN' := hNN
            rw [hTranslate, hHeadNone] at hNN'
            simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
          · by_cases hListCons : f = Term.__eo_List_cons
            · subst hListCons
              have hTranslate :
                  __eo_to_smt (Term.Apply Term.__eo_List_cons x) =
                    SmtTerm.Apply (__eo_to_smt Term.__eo_List_cons) (__eo_to_smt x) := by
                exact eo_to_smt_single_apply_generic Term.__eo_List_cons x
                  (by intro g y h; cases h)
                  (by intro h; cases h)
              have hHeadNone : __eo_to_smt Term.__eo_List_cons = SmtTerm.None := by
                rw [__eo_to_smt.eq_def]
              have hNN' := hNN
              rw [hTranslate, hHeadNone] at hNN'
              simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
            · by_cases hNot : f = Term.not
              · subst hNot
                have hTranslate :
                    __eo_to_smt (Term.Apply Term.not x) =
                      SmtTerm.not (__eo_to_smt x) := by
                  rw [__eo_to_smt.eq_def]
                have hArgSmtTy : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
                  have hNN' := hNN
                  rw [hTranslate] at hNN'
                  cases h : __smtx_typeof (__eo_to_smt x) <;>
                    simp [__smtx_typeof, native_ite, native_Teq, h] at hNN'
                  simp
                have hArgNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                  rw [hArgSmtTy]
                  simp
                have hIx := eo_to_smt_typeof_matches_translation x hArgNN
                have hTyX : __eo_typeof x = Term.Bool :=
                  eo_typeof_bool_of_smt_bool hIx hArgSmtTy
                have hTy :
                    __eo_typeof (Term.Apply Term.not x) = Term.Bool := by
                  simp [__eo_typeof, __eo_typeof_not, hTyX]
                rw [hTy]
                exact TranslationProofs.smtx_typeof_translation_not_of_non_none x hNN
              · by_cases hDtSel : ∃ s d i j, f = Term.DtSel s d i j
                · rcases hDtSel with ⟨s, d, i, j, rfl⟩
                  sorry
                · sorry
termination_by t _ => sizeOf t
decreasing_by
  all_goals
    subst_vars
    simp_wf
  all_goals
    omega

/-- Transfers EO typing information to the translated SMT term when the translation is defined. -/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = T ->
  __smtx_typeof s = __eo_to_smt_type T := by
  intro hs hNN hTy
  subst s T
  exact eo_to_smt_typeof_matches_translation t hNN

end RuleProofs
