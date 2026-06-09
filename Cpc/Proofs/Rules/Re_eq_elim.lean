import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Canonical.Seq

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev reEqName : native_String :=
  native_string_lit "@var.re_eq"

private abbrev reEqType : Term :=
  Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)

private abbrev reEqSmtType : SmtType :=
  SmtType.Seq SmtType.Char

private abbrev reEqVar : Term :=
  Term.Var (Term.String reEqName) reEqType

private abbrev reEqVarList : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons reEqVar) Term.__eo_List_nil

private abbrev reEqIn (x r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) r

private abbrev reEqBody (r1 r2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (reEqIn reEqVar r1)) (reEqIn reEqVar r2)

private abbrev reEqForall (r1 r2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) reEqVarList) (reEqBody r1 r2)

private abbrev reEqInner (r1 r2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) r1) r2

private abbrev reEqConclusion (r1 r2 Q : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (reEqInner r1 r2)) Q

private abbrev reEqSmtVar : SmtTerm :=
  SmtTerm.Var reEqName reEqSmtType

private abbrev reEqSmtBody (r1 r2 : Term) : SmtTerm :=
  SmtTerm.eq
    (SmtTerm.str_in_re reEqSmtVar (__eo_to_smt r1))
    (SmtTerm.str_in_re reEqSmtVar (__eo_to_smt r2))

private abbrev reEqSmtForall (r1 r2 : Term) : SmtTerm :=
  SmtTerm.not (SmtTerm.exists reEqName reEqSmtType (SmtTerm.not (reEqSmtBody r1 r2)))

private theorem eo_to_smt_reEqVar :
    __eo_to_smt reEqVar = reEqSmtVar := by
  rfl

private theorem eo_to_smt_reEqForall (r1 r2 : Term) :
    __eo_to_smt (reEqForall r1 r2) = reEqSmtForall r1 r2 := by
  rfl

private theorem re_eq_elim_prog_success
    {r1 r2 Q : Term}
    (hProg : __eo_prog_re_eq_elim (reEqConclusion r1 r2 Q) ≠ Term.Stuck) :
    Q = reEqForall r1 r2 ∧
      __eo_prog_re_eq_elim (reEqConclusion r1 r2 Q) =
        reEqConclusion r1 r2 Q := by
  by_cases hQF : native_teq Q (reEqForall r1 r2) = true
  · have hQ : Q = reEqForall r1 r2 := by
      simpa [native_teq] using hQF
    subst Q
    constructor
    · rfl
    · simp [reEqConclusion, reEqInner, reEqForall, reEqBody, reEqIn,
        reEqVarList, reEqVar, reEqType, reEqName, __eo_prog_re_eq_elim,
        __eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  · have hQFfalse : native_teq Q (reEqForall r1 r2) = false := by
      cases h : native_teq Q (reEqForall r1 r2) <;> simp_all
    exfalso
    apply hProg
    simp [reEqConclusion, reEqInner, reEqForall, reEqBody, reEqIn,
      reEqVarList, reEqVar, reEqType, reEqName, __eo_prog_re_eq_elim,
      __eo_requires, native_ite, native_not, SmtEval.native_not, hQFfalse]

private theorem eval_reEqSmtVar_push (M : SmtModel) (v : SmtValue) :
    __smtx_model_eval (native_model_push M reEqName reEqSmtType v) reEqSmtVar = v := by
  simp [reEqSmtVar, reEqName, reEqSmtType, __smtx_model_eval, native_model_var_lookup,
    native_model_push]

private theorem map_native_ssm_char_of_value_char :
    ∀ s : native_String,
      List.map (native_ssm_char_of_value ∘ SmtValue.Char) s = s
  | [] => rfl
  | _ :: cs => by
      simp [Function.comp_def, native_ssm_char_of_value, map_native_ssm_char_of_value_char cs]

private theorem native_unpack_seq_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => by simp [native_pack_seq, native_unpack_seq]
  | _ :: xs => by simp [native_pack_seq, native_unpack_seq, native_unpack_seq_pack_seq T xs]

private theorem native_unpack_string_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  simp [native_unpack_string, native_pack_string, native_unpack_seq_pack_seq,
    map_native_ssm_char_of_value_char]

private theorem reEqSmtBody_bool_of_forall_bool
    {r1 r2 : Term}
    (hForall : __smtx_typeof (reEqSmtForall r1 r2) = SmtType.Bool) :
    __smtx_typeof (reEqSmtBody r1 r2) = SmtType.Bool := by
  have hExistsBool :
      __smtx_typeof
          (SmtTerm.exists reEqName reEqSmtType (SmtTerm.not (reEqSmtBody r1 r2))) =
        SmtType.Bool := by
    exact TranslationProofs.smtx_typeof_not_arg_bool _ (by
      simpa [reEqSmtForall] using hForall)
  have hExistsNN :
      term_has_non_none_type
        (SmtTerm.exists reEqName reEqSmtType (SmtTerm.not (reEqSmtBody r1 r2))) := by
    unfold term_has_non_none_type
    rw [hExistsBool]
    simp
  have hNotBodyBool :
      __smtx_typeof (SmtTerm.not (reEqSmtBody r1 r2)) = SmtType.Bool := by
    exact exists_body_bool_of_non_none hExistsNN
  exact TranslationProofs.smtx_typeof_not_arg_bool _ hNotBodyBool

private theorem reEqRegexTypes_of_body_bool
    {r1 r2 : Term}
    (hBody : __smtx_typeof (reEqSmtBody r1 r2) = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan := by
  let lhs := SmtTerm.str_in_re reEqSmtVar (__eo_to_smt r1)
  let rhs := SmtTerm.str_in_re reEqSmtVar (__eo_to_smt r2)
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof lhs) (__smtx_typeof rhs) = SmtType.Bool := by
    simpa [reEqSmtBody, lhs, rhs, typeof_eq_eq] using hBody
  rcases (RuleProofs.smtx_typeof_eq_bool_iff (__smtx_typeof lhs) (__smtx_typeof rhs)).mp
      hEqTy with ⟨hSame, hLhsNN0⟩
  have hLhsNN : term_has_non_none_type lhs := by
    simpa [term_has_non_none_type, lhs] using hLhsNN0
  have hR1Ty :
      __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan :=
    (seq_char_reglan_args_of_non_none
      (op := SmtTerm.str_in_re)
      (typeof_str_in_re_eq reEqSmtVar (__eo_to_smt r1))
      hLhsNN).2
  have hRhsNN0 : __smtx_typeof rhs ≠ SmtType.None := by
    intro hNone
    exact hLhsNN0 (by rw [hSame, hNone])
  have hRhsNN : term_has_non_none_type rhs := by
    simpa [term_has_non_none_type, rhs] using hRhsNN0
  have hR2Ty :
      __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan :=
    (seq_char_reglan_args_of_non_none
      (op := SmtTerm.str_in_re)
      (typeof_str_in_re_eq reEqSmtVar (__eo_to_smt r2))
      hRhsNN).2
  exact ⟨hR1Ty, hR2Ty⟩

private theorem reEqSmtForall_eval_eq_re_ext
    (M : SmtModel) (r1 r2 : Term) (R1 R2 : native_RegLan)
    (hClosedR1 : SmtTermClosedIn [] (__eo_to_smt r1))
    (hClosedR2 : SmtTermClosedIn [] (__eo_to_smt r2))
    (hR1Eval : __smtx_model_eval M (__eo_to_smt r1) = SmtValue.RegLan R1)
    (hR2Eval : __smtx_model_eval M (__eo_to_smt r2) = SmtValue.RegLan R2) :
    __smtx_model_eval M (reEqSmtForall r1 r2) =
      SmtValue.Boolean (native_re_ext_eq R1 R2) := by
  classical
  have hR1Push :
      ∀ v : SmtValue,
        __smtx_model_eval (native_model_push M reEqName reEqSmtType v)
          (__eo_to_smt r1) = SmtValue.RegLan R1 := by
    intro v
    have hEq := smt_model_eval_eq_of_closedIn (__eo_to_smt r1) [] M
      (native_model_push M reEqName reEqSmtType v) hClosedR1
      (model_agrees_on_env_nil_of_globals
        (model_agrees_on_globals_push M reEqName reEqSmtType v))
    rw [← hEq]
    exact hR1Eval
  have hR2Push :
      ∀ v : SmtValue,
        __smtx_model_eval (native_model_push M reEqName reEqSmtType v)
          (__eo_to_smt r2) = SmtValue.RegLan R2 := by
    intro v
    have hEq := smt_model_eval_eq_of_closedIn (__eo_to_smt r2) [] M
      (native_model_push M reEqName reEqSmtType v) hClosedR2
      (model_agrees_on_env_nil_of_globals
        (model_agrees_on_globals_push M reEqName reEqSmtType v))
    rw [← hEq]
    exact hR2Eval
  by_cases hExt :
      ∀ s : native_String,
        native_string_valid s = true ->
          native_str_in_re s R1 = native_str_in_re s R2
  · have hReExt : native_re_ext_eq R1 R2 = true := by
      change
        (if hExt' :
            ∀ s : native_String,
              native_string_valid s = true ->
                native_str_in_re s R1 = native_str_in_re s R2 then
          true
        else
          false) = true
      split
      · rfl
      · rename_i hNot
        exact False.elim (hNot hExt)
    have hNo :
        ¬ ∃ v : SmtValue,
          __smtx_typeof_value v = reEqSmtType ∧
            __smtx_value_canonical_bool v = true ∧
              __smtx_model_eval (native_model_push M reEqName reEqSmtType v)
                (SmtTerm.not (reEqSmtBody r1 r2)) = SmtValue.Boolean true := by
      rintro ⟨v, hvTy, _hvCan, hvEval⟩
      rcases seq_value_canonical (T := SmtType.Char) (by
          simpa [reEqSmtType] using hvTy) with ⟨ss, hvSeq⟩
      subst v
      have hSeqTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
        simpa [__smtx_typeof_value, reEqSmtType] using hvTy
      have hValid : native_string_valid (native_unpack_string ss) = true :=
        native_unpack_string_valid_of_typeof_seq_char hSeqTy
      have hMemEq :
          native_str_in_re (native_unpack_string ss) R1 =
            native_str_in_re (native_unpack_string ss) R2 :=
        hExt (native_unpack_string ss) hValid
      have hBodyTrue :
          __smtx_model_eval
              (native_model_push M reEqName reEqSmtType (SmtValue.Seq ss))
              (reEqSmtBody r1 r2) =
            SmtValue.Boolean true := by
        cases h1 : native_str_in_re (native_unpack_string ss) R1 <;>
          cases h2 : native_str_in_re (native_unpack_string ss) R2 <;>
          simp [reEqSmtBody, reEqSmtVar, __smtx_model_eval, __smtx_model_eval_str_in_re,
            __smtx_model_eval_eq, native_veq, eval_reEqSmtVar_push, hR1Push, hR2Push,
            h1, h2] at hMemEq ⊢
      have hNotFalse :
          __smtx_model_eval
              (native_model_push M reEqName reEqSmtType (SmtValue.Seq ss))
              (SmtTerm.not (reEqSmtBody r1 r2)) =
            SmtValue.Boolean false := by
        simp [__smtx_model_eval, __smtx_model_eval_not, hBodyTrue, SmtEval.native_not]
      rw [hNotFalse] at hvEval
      cases hvEval
    have hExistsFalse :
        __smtx_model_eval M
            (SmtTerm.exists reEqName reEqSmtType (SmtTerm.not (reEqSmtBody r1 r2))) =
          SmtValue.Boolean false := by
      simp [__smtx_model_eval]
      intro x hx hCan hEval
      exact hNo ⟨x, hx, hCan, by
        simpa [reEqSmtBody, reEqSmtVar, __smtx_model_eval] using hEval⟩
    simp [reEqSmtForall, __smtx_model_eval, hExistsFalse, __smtx_model_eval_not,
      SmtEval.native_not, hReExt]
  · have hWitness :
        ∃ s : native_String,
          native_string_valid s = true ∧
            native_str_in_re s R1 ≠ native_str_in_re s R2 := by
      by_cases hW :
          ∃ s : native_String,
            native_string_valid s = true ∧
              native_str_in_re s R1 ≠ native_str_in_re s R2
      · exact hW
      · exfalso
        apply hExt
        intro s hValid
        by_cases hEq : native_str_in_re s R1 = native_str_in_re s R2
        · exact hEq
        · exact False.elim (hW ⟨s, hValid, hEq⟩)
    rcases hWitness with ⟨str, hValid, hDiff⟩
    let v := SmtValue.Seq (native_pack_string str)
    have hvTy : __smtx_typeof_value v = reEqSmtType := by
      change __smtx_typeof_seq_value (native_pack_string str) = SmtType.Seq SmtType.Char
      exact typeof_pack_string str hValid
    have hvCan : __smtx_value_canonical_bool v = true := by
      simpa [v, __smtx_value_canonical_bool] using seq_canonical_pack_string str hValid
    have hUnpack : native_unpack_string (native_pack_string str) = str :=
      native_unpack_string_pack_string str
    have hBodyFalse :
        __smtx_model_eval (native_model_push M reEqName reEqSmtType v)
            (reEqSmtBody r1 r2) =
          SmtValue.Boolean false := by
      cases h1 : native_str_in_re str R1 <;>
        cases h2 : native_str_in_re str R2 <;>
        simp [v, reEqSmtBody, reEqSmtVar, __smtx_model_eval,
          __smtx_model_eval_str_in_re, __smtx_model_eval_eq, native_veq,
          eval_reEqSmtVar_push, hR1Push, hR2Push, hUnpack, h1, h2] at hDiff ⊢
    have hNotTrue :
        __smtx_model_eval (native_model_push M reEqName reEqSmtType v)
            (SmtTerm.not (reEqSmtBody r1 r2)) =
          SmtValue.Boolean true := by
      simp [__smtx_model_eval, __smtx_model_eval_not, hBodyFalse, SmtEval.native_not]
    have hSat :
        ∃ v : SmtValue,
          __smtx_typeof_value v = reEqSmtType ∧
            __smtx_value_canonical_bool v = true ∧
              __smtx_model_eval (native_model_push M reEqName reEqSmtType v)
                (SmtTerm.not (reEqSmtBody r1 r2)) = SmtValue.Boolean true :=
      ⟨v, hvTy, hvCan, hNotTrue⟩
    have hExistsTrue :
        __smtx_model_eval M
            (SmtTerm.exists reEqName reEqSmtType (SmtTerm.not (reEqSmtBody r1 r2))) =
          SmtValue.Boolean true := by
      simp [__smtx_model_eval]
      exact ⟨v, hvTy, hvCan, by
        simpa [reEqSmtBody, reEqSmtVar, __smtx_model_eval] using hNotTrue⟩
    have hReExt : native_re_ext_eq R1 R2 = false := by
      change
        (if hExt' :
            ∀ s : native_String,
              native_string_valid s = true ->
                native_str_in_re s R1 = native_str_in_re s R2 then
          true
        else
          false) = false
      split
      · rename_i hYes
        exact False.elim (hExt hYes)
      · rfl
    simp [reEqSmtForall, __smtx_model_eval, hExistsTrue, __smtx_model_eval_not,
      SmtEval.native_not, hReExt]

private theorem re_eq_elim_shape_of_not_stuck
    (x : Term) :
    __eo_prog_re_eq_elim x ≠ Term.Stuck ->
      ∃ r1 r2,
        x = reEqConclusion r1 r2 (reEqForall r1 r2) ∧
          __eo_prog_re_eq_elim x = reEqConclusion r1 r2 (reEqForall r1 r2) := by
  intro hProg
  cases x with
  | Apply lhs Q =>
      cases lhs with
      | Apply eqHead inner =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases inner with
                  | Apply innerHead r2 =>
                      cases innerHead with
                      | Apply eqHead2 r1 =>
                          cases eqHead2 with
                          | UOp opEq2 =>
                              cases opEq2 with
                              | eq =>
                                  have hSuccess :
                                      Q = reEqForall r1 r2 ∧
                                        __eo_prog_re_eq_elim (reEqConclusion r1 r2 Q) =
                                          reEqConclusion r1 r2 Q :=
                                    re_eq_elim_prog_success (r1 := r1) (r2 := r2) (Q := Q) (by
                                      simpa [reEqConclusion, reEqInner] using hProg)
                                  rcases hSuccess with ⟨hQ, hProgEq⟩
                                  subst Q
                                  exact ⟨r1, r2, rfl, hProgEq⟩
                              | _ =>
                                  simp [__eo_prog_re_eq_elim] at hProg
                          | _ =>
                              simp [__eo_prog_re_eq_elim] at hProg
                      | _ =>
                          simp [__eo_prog_re_eq_elim] at hProg
                  | _ =>
                      simp [__eo_prog_re_eq_elim] at hProg
              | _ =>
                  simp [__eo_prog_re_eq_elim] at hProg
          | _ =>
              simp [__eo_prog_re_eq_elim] at hProg
      | _ =>
          simp [__eo_prog_re_eq_elim] at hProg
  | _ =>
      simp [__eo_prog_re_eq_elim] at hProg

private theorem reEqConclusion_interprets
    (M : SmtModel) (hM : model_total_typed M)
    (r1 r2 : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (reEqConclusion r1 r2 (reEqForall r1 r2)))
    (hClosed :
      __eo_is_closed (reEqConclusion r1 r2 (reEqForall r1 r2)) =
        Term.Boolean true) :
    eo_interprets M (reEqConclusion r1 r2 (reEqForall r1 r2)) true := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (reEqInner r1 r2) (reEqForall r1 r2) hBool with
    ⟨hOuterSame, hInnerNN0⟩
  have hInnerNN :
      term_has_non_none_type (SmtTerm.eq (__eo_to_smt r1) (__eo_to_smt r2)) := by
    simpa [term_has_non_none_type, reEqInner] using hInnerNN0
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (reEqInner r1 r2)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.eq (__eo_to_smt r1) (__eo_to_smt r2)) = SmtType.Bool
    exact eq_term_typeof_of_non_none hInnerNN
  have hForallTy :
      __smtx_typeof (__eo_to_smt (reEqForall r1 r2)) = SmtType.Bool := by
    rw [← hOuterSame]
    exact hInnerTy
  have hForallSmtTy :
      __smtx_typeof (reEqSmtForall r1 r2) = SmtType.Bool := by
    simpa [eo_to_smt_reEqForall] using hForallTy
  have hBodyTy :
      __smtx_typeof (reEqSmtBody r1 r2) = SmtType.Bool :=
    reEqSmtBody_bool_of_forall_bool hForallSmtTy
  rcases reEqRegexTypes_of_body_bool hBodyTy with ⟨hR1Ty, hR2Ty⟩
  have hR1NN : term_has_non_none_type (__eo_to_smt r1) := by
    unfold term_has_non_none_type
    rw [hR1Ty]
    simp
  have hR2NN : term_has_non_none_type (__eo_to_smt r2) := by
    unfold term_has_non_none_type
    rw [hR2Ty]
    simp
  have hR1ValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r1)) = SmtType.RegLan := by
    simpa [hR1Ty] using type_preservation M hM (__eo_to_smt r1) hR1NN
  have hR2ValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r2)) = SmtType.RegLan := by
    simpa [hR2Ty] using type_preservation M hM (__eo_to_smt r2) hR2NN
  rcases reglan_value_canonical hR1ValTy with ⟨R1, hR1Eval⟩
  rcases reglan_value_canonical hR2ValTy with ⟨R2, hR2Eval⟩
  have hClosedSmt :
      SmtTermClosedIn []
        (SmtTerm.eq (SmtTerm.eq (__eo_to_smt r1) (__eo_to_smt r2))
          (reEqSmtForall r1 r2)) := by
    simpa [reEqConclusion, reEqInner, eo_to_smt_reEqForall] using
      smtTermClosedIn_of_eo_is_closed
        (reEqConclusion r1 r2 (reEqForall r1 r2)) hClosed
  have hClosedR1 : SmtTermClosedIn [] (__eo_to_smt r1) := hClosedSmt.1.1
  have hClosedR2 : SmtTermClosedIn [] (__eo_to_smt r2) := hClosedSmt.1.2
  have hForallEval :
      __smtx_model_eval M (reEqSmtForall r1 r2) =
        SmtValue.Boolean (native_re_ext_eq R1 R2) :=
    reEqSmtForall_eval_eq_re_ext M r1 r2 R1 R2 hClosedR1 hClosedR2 hR1Eval hR2Eval
  have hInnerEval :
      __smtx_model_eval M (__eo_to_smt (reEqInner r1 r2)) =
        SmtValue.Boolean (native_re_ext_eq R1 R2) := by
    change
      __smtx_model_eval M (SmtTerm.eq (__eo_to_smt r1) (__eo_to_smt r2)) =
        SmtValue.Boolean (native_re_ext_eq R1 R2)
    simp [__smtx_model_eval, __smtx_model_eval_eq, hR1Eval, hR2Eval]
  have hInnerEvalSmt :
      __smtx_model_eval M (SmtTerm.eq (__eo_to_smt r1) (__eo_to_smt r2)) =
        SmtValue.Boolean (native_re_ext_eq R1 R2) := by
    simpa [reEqInner] using hInnerEval
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt (reEqConclusion r1 r2 (reEqForall r1 r2))) =
        SmtValue.Boolean true := by
    rw [show
        __eo_to_smt (reEqConclusion r1 r2 (reEqForall r1 r2)) =
          SmtTerm.eq (SmtTerm.eq (__eo_to_smt r1) (__eo_to_smt r2))
            (reEqSmtForall r1 r2) by
      rfl]
    simp [__smtx_model_eval, hInnerEvalSmt, hForallEval,
      RuleProofs.smtx_model_eval_eq_refl]
  exact RuleProofs.eo_interprets_of_bool_eval M
    (reEqConclusion r1 r2 (reEqForall r1 r2)) true hBool hEval

theorem cmd_step_re_eq_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_eq_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_eq_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_eq_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_eq_elim args premises ≠ Term.Stuck :=
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
              have hArgOk : eoHasSmtTranslation a1 ∧
                  __eo_is_closed a1 = Term.Boolean true := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hArgOk.1
              have hClosedA1 : __eo_is_closed a1 = Term.Boolean true := hArgOk.2
              have hProgRe : __eo_prog_re_eq_elim a1 ≠ Term.Stuck := by
                change __eo_prog_re_eq_elim a1 ≠ Term.Stuck at hProg
                exact hProg
              rcases re_eq_elim_shape_of_not_stuck a1 hProgRe with
                ⟨r1, r2, ha1, hProgEq⟩
              subst a1
              have hTyProg :
                  __eo_typeof
                      (__eo_prog_re_eq_elim
                        (reEqConclusion r1 r2 (reEqForall r1 r2))) = Term.Bool := by
                change __eo_typeof
                    (__eo_prog_re_eq_elim
                      (reEqConclusion r1 r2 (reEqForall r1 r2))) = Term.Bool at hResultTy
                exact hResultTy
              have hTy :
                  __eo_typeof (reEqConclusion r1 r2 (reEqForall r1 r2)) = Term.Bool := by
                rw [hProgEq] at hTyProg
                exact hTyProg
              have hBool :
                  RuleProofs.eo_has_bool_type
                    (reEqConclusion r1 r2 (reEqForall r1 r2)) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (reEqConclusion r1 r2 (reEqForall r1 r2)) hTransA1 hTy
              have hClosed :
                  __eo_is_closed (reEqConclusion r1 r2 (reEqForall r1 r2)) =
                    Term.Boolean true := by
                simpa using hClosedA1
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_re_eq_elim (reEqConclusion r1 r2 (reEqForall r1 r2))) true
                rw [hProgEq]
                exact reEqConclusion_interprets M hM r1 r2 hBool hClosed
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_re_eq_elim (reEqConclusion r1 r2 (reEqForall r1 r2)))
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (reEqConclusion r1 r2 (reEqForall r1 r2)) hBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
