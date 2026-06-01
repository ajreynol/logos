import Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace RuleProofs

private theorem native_seq_prefix_eq_append_drop
    (pat xs : List SmtValue) :
    native_seq_prefix_eq pat xs = true ->
      pat ++ xs.drop pat.length = xs := by
  induction pat generalizing xs with
  | nil =>
      intro _h
      simp
  | cons p ps ih =>
      cases xs with
      | nil =>
          intro h
          simp [native_seq_prefix_eq] at h
      | cons x xs =>
          intro h
          have hParts : p = x ∧ native_seq_prefix_eq ps xs = true := by
            simpa [native_seq_prefix_eq, native_veq] using h
          rcases hParts with ⟨rfl, hTail⟩
          simpa using ih xs hTail

private theorem native_seq_prefix_eq_append
    (pat rest : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ rest) = true := by
  induction pat with
  | nil =>
      rfl
  | cons p ps ih =>
      simp [native_seq_prefix_eq, native_veq, ih]

private theorem native_seq_indexof_rec_exists_of_append
    (pat pre suf xs : List SmtValue) :
    xs = pre ++ pat ++ suf ->
    ∀ j fuel, pre.length + 1 ≤ fuel ->
      0 ≤ native_seq_indexof_rec xs pat j fuel := by
  intro hxs
  induction pre generalizing xs with
  | nil =>
      intro j fuel hfuel
      subst xs
      cases fuel with
      | zero =>
          omega
      | succ fuel =>
          simp only [List.nil_append]
          unfold native_seq_indexof_rec
          rw [if_pos (native_seq_prefix_eq_append pat suf)]
          exact Int.natCast_nonneg j
  | cons a pre ih =>
      intro j fuel hfuel
      subst xs
      cases fuel with
      | zero =>
          omega
      | succ fuel =>
          unfold native_seq_indexof_rec
          by_cases hp :
              native_seq_prefix_eq pat (a :: pre ++ pat ++ suf) = true
          · rw [if_pos (by simpa using hp)]
            exact Int.natCast_nonneg j
          · rw [if_neg (by simpa using hp)]
            have hfuel' : pre.length + 1 ≤ fuel := by
              exact Nat.succ_le_succ_iff.mp
                (by simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hfuel)
            exact ih (pre ++ pat ++ suf) rfl (j + 1) fuel hfuel'

private theorem native_seq_contains_of_append
    (pre pat suf : List SmtValue) :
    native_seq_contains (pre ++ pat ++ suf) pat = true := by
  unfold native_seq_contains native_seq_indexof
  rw [if_neg (by decide : ¬ ((0 : native_Int) < 0))]
  have hBounds :
      Int.toNat (0 : native_Int) + pat.length ≤
        (pre ++ pat ++ suf).length := by
    simp
    omega
  rw [dif_pos hBounds]
  simp only [Int.toNat_zero, List.drop_zero, Nat.zero_add]
  have hNonneg :
      0 ≤ native_seq_indexof_rec (pre ++ pat ++ suf) pat 0
        ((pre ++ pat ++ suf).length - pat.length + 1) := by
    apply native_seq_indexof_rec_exists_of_append pat pre suf
      (pre ++ pat ++ suf) rfl
    simp
    omega
  simpa [List.append_assoc] using hNonneg

private theorem native_seq_indexof_rec_decomp
    (xs pat : List SmtValue) :
    (i fuel j : Nat) ->
      native_seq_indexof_rec xs pat i fuel = Int.ofNat j ->
      i ≤ j ∧
        ∃ before after : List SmtValue,
          xs = before ++ pat ++ after ∧ before.length = j - i
  | i, 0, j, h => by
      simp [native_seq_indexof_rec] at h
  | i, fuel + 1, j, h => by
      unfold native_seq_indexof_rec at h
      by_cases hPrefix : native_seq_prefix_eq pat xs = true
      · rw [if_pos hPrefix] at h
        have hji : j = i := Int.ofNat.inj h.symm
        subst j
        constructor
        · exact Nat.le_refl _
        · refine ⟨[], xs.drop pat.length, ?_, by simp⟩
          exact (native_seq_prefix_eq_append_drop pat xs hPrefix).symm
      · rw [if_neg hPrefix] at h
        cases xs with
        | nil =>
            simp at h
        | cons x xs =>
            rcases native_seq_indexof_rec_decomp xs pat (i + 1) fuel j h with
              ⟨hLe, before, after, hXs, hBeforeLen⟩
            constructor
            · omega
            · refine ⟨x :: before, after, ?_, ?_⟩
              · simp [hXs, List.append_assoc]
              · simp [hBeforeLen]
                omega

private theorem native_seq_contains_exists
    (xs pat : List SmtValue) :
    native_seq_contains xs pat = true ->
      ∃ before after : List SmtValue, xs = before ++ pat ++ after := by
  intro h
  unfold native_seq_contains native_seq_indexof at h
  rw [if_neg (by decide : ¬ ((0 : native_Int) < 0))] at h
  by_cases hBounds : Int.toNat (0 : native_Int) + pat.length ≤ xs.length
  · rw [dif_pos hBounds] at h
    simp only [Int.toNat_zero, Nat.zero_add, List.drop_zero] at h
    have hNonneg :
        0 ≤ native_seq_indexof_rec xs pat 0 (xs.length - pat.length + 1) := by
      simpa using h
    let j :=
      Int.toNat (native_seq_indexof_rec xs pat 0
        (xs.length - pat.length + 1))
    have hCast :
        Int.ofNat j =
          native_seq_indexof_rec xs pat 0 (xs.length - pat.length + 1) :=
      Int.toNat_of_nonneg hNonneg
    have hIdx :
        native_seq_indexof_rec xs pat 0 (xs.length - pat.length + 1) =
          Int.ofNat j := by
      rw [hCast]
    rcases native_seq_indexof_rec_decomp xs pat 0
        (xs.length - pat.length + 1) j hIdx with
      ⟨_hLe, before, after, hXs, _hLen⟩
    exact ⟨before, after, hXs⟩
  · rw [dif_neg hBounds] at h
    simp at h

private theorem eo_and_true_parts {a b : Term} :
    __eo_and a b = Term.Boolean true ->
      a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite,
      SmtEval.native_and, SmtEval.native_not] at h ⊢
  · exact h
  · split at h <;> simp at h

private theorem str_overlap_endpoints_ctn_valid_properties
    (M : SmtModel) (hM : model_total_typed M)
    (c1 s c2 emp d1 t d2 : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_contains)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) ->
    __eo_prog_str_overlap_endpoints_ctn
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_contains)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) ≠
        Term.Stuck ->
    StepRuleProperties M []
      (__eo_prog_str_overlap_endpoints_ctn
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_contains)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))) := by
  intro hTrans hNe
  let pat : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))
  let full : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))
  let lhs : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) full) pat
  let rhs : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s) pat
  let body : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
  let leftGuard : Term :=
    __eo_gt (__str_value_len c1)
      (__str_overlap_rec (__str_flatten (__str_nary_intro c1))
        (__str_flatten (__str_nary_intro d1)))
  let rightGuard : Term :=
    __eo_gt (__str_value_len c2)
      (__str_overlap_rec
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro c2)))
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro d2))))
  let rightReq : Term := __eo_requires rightGuard (Term.Boolean false) body
  let leftReq : Term := __eo_requires leftGuard (Term.Boolean false) rightReq
  let emptyReq : Term :=
    __eo_requires (__str_is_empty emp) (Term.Boolean true) leftReq
  let shapeGuard : Term :=
    __eo_and
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq emp emp) (__eo_eq s s))
            (__eo_eq d1 d1))
          (__eo_eq t t))
        (__eo_eq d2 d2))
      (__eo_eq emp emp)
  change __eo_requires shapeGuard (Term.Boolean true) emptyReq ≠
    Term.Stuck at hNe
  have hShapeEq : shapeGuard = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck shapeGuard (Term.Boolean true) emptyReq hNe
  have hEmptyReqNe : emptyReq ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck shapeGuard (Term.Boolean true)
      emptyReq hNe
  have hShapeResult :
      __eo_requires shapeGuard (Term.Boolean true) emptyReq = emptyReq :=
    eo_requires_result_eq_of_ne_stuck shapeGuard (Term.Boolean true)
      emptyReq hNe
  have hEmptyEq : __str_is_empty emp = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__str_is_empty emp) (Term.Boolean true)
      leftReq hEmptyReqNe
  have hLeftReqNe : leftReq ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (__str_is_empty emp)
      (Term.Boolean true) leftReq hEmptyReqNe
  have hEmptyResult :
      __eo_requires (__str_is_empty emp) (Term.Boolean true) leftReq =
        leftReq :=
    eo_requires_result_eq_of_ne_stuck (__str_is_empty emp)
      (Term.Boolean true) leftReq hEmptyReqNe
  have hLeftGuardEq : leftGuard = Term.Boolean false :=
    eo_requires_eq_of_ne_stuck leftGuard (Term.Boolean false) rightReq
      hLeftReqNe
  have hRightReqNe : rightReq ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck leftGuard (Term.Boolean false)
      rightReq hLeftReqNe
  have hLeftResult :
      __eo_requires leftGuard (Term.Boolean false) rightReq = rightReq :=
    eo_requires_result_eq_of_ne_stuck leftGuard (Term.Boolean false)
      rightReq hLeftReqNe
  have hRightGuardEq : rightGuard = Term.Boolean false :=
    eo_requires_eq_of_ne_stuck rightGuard (Term.Boolean false) body
      hRightReqNe
  have hBodyNe : body ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck rightGuard (Term.Boolean false)
      body hRightReqNe
  have hRightResult :
      __eo_requires rightGuard (Term.Boolean false) body = body :=
    eo_requires_result_eq_of_ne_stuck rightGuard (Term.Boolean false)
      body hRightReqNe
  have hProgEq :
      __eo_prog_str_overlap_endpoints_ctn
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_contains)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) =
        body := by
    calc
      __eo_prog_str_overlap_endpoints_ctn
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_contains)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) =
          __eo_requires shapeGuard (Term.Boolean true) emptyReq := by
            rfl
      _ = emptyReq := hShapeResult
      _ = leftReq := hEmptyResult
      _ = rightReq := hLeftResult
      _ = body := hRightResult
  have hBodyBool : RuleProofs.eo_has_bool_type body := by
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt lhs) (__eo_to_smt rhs)) := by
      unfold term_has_non_none_type
      simpa [RuleProofs.eo_has_smt_translation, body, lhs, rhs] using hTrans
    have hTy :
        __smtx_typeof (SmtTerm.eq (__eo_to_smt lhs) (__eo_to_smt rhs)) =
          SmtType.Bool :=
      Smtm.eq_term_typeof_of_non_none hNN
    simpa [RuleProofs.eo_has_bool_type, body, lhs, rhs] using hTy
  refine ⟨?_, ?_⟩
  · intro _hPremises
    rw [hProgEq]
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt lhs))
          (__smtx_model_eval M (__eo_to_smt rhs)) := by
      -- This is the remaining semantic bridge from the extracted overlap
      -- guards (`hEmptyEq`, `hLeftGuardEq`, `hRightGuardEq`) to native
      -- sequence containment.
      sorry
    exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBodyBool hRel
  · rw [hProgEq]
    exact hTrans

private theorem str_overlap_endpoints_ctn_arg_properties
    (M : SmtModel) (hM : model_total_typed M) :
    (a1 : Term) ->
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_prog_str_overlap_endpoints_ctn a1 ≠ Term.Stuck ->
    StepRuleProperties M [] (__eo_prog_str_overlap_endpoints_ctn a1)
  | a1, hTrans, hNe => by
      rw [__eo_prog_str_overlap_endpoints_ctn.eq_def] at hNe
      rw [__eo_prog_str_overlap_endpoints_ctn.eq_def]
      split at hNe
      · rename_i _ c1 s c2 emp d1 t d2 emp2 s2 d12 t2 d22 emp3
        have hShapeEq := eo_requires_eq_of_ne_stuck _ _ _ hNe
        rcases eo_and_true_parts hShapeEq with ⟨hABCDE, hEmp3EqTerm⟩
        rcases eo_and_true_parts hABCDE with ⟨hABCD, hD2EqTerm⟩
        rcases eo_and_true_parts hABCD with ⟨hABC, hTEqTerm⟩
        rcases eo_and_true_parts hABC with ⟨hAB, hD1EqTerm⟩
        rcases eo_and_true_parts hAB with ⟨hEmp2EqTerm, hSEqTerm⟩
        have hEmp2 : emp2 = emp := eq_of_eo_eq_true_local emp emp2 hEmp2EqTerm
        have hS2 : s2 = s := eq_of_eo_eq_true_local s s2 hSEqTerm
        have hD12 : d12 = d1 := eq_of_eo_eq_true_local d1 d12 hD1EqTerm
        have hT2 : t2 = t := eq_of_eo_eq_true_local t t2 hTEqTerm
        have hD22 : d22 = d2 := eq_of_eo_eq_true_local d2 d22 hD2EqTerm
        have hEmp3 : emp3 = emp := eq_of_eo_eq_true_local emp emp3 hEmp3EqTerm
        subst emp2
        subst s2
        subst d12
        subst t2
        subst d22
        subst emp3
        have hTrans' :
            RuleProofs.eo_has_smt_translation
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_contains)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) := by
          simpa using hTrans
        have hNe' :
            __eo_prog_str_overlap_endpoints_ctn
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_contains)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) ≠
              Term.Stuck := by
          simpa [__eo_prog_str_overlap_endpoints_ctn.eq_def] using hNe
        simpa [__eo_prog_str_overlap_endpoints_ctn.eq_def] using
          str_overlap_endpoints_ctn_valid_properties M hM c1 s c2 emp d1 t d2
            hTrans' hNe'
      · change Term.Stuck ≠ Term.Stuck at hNe
        exact False.elim (hNe rfl)

end RuleProofs

theorem cmd_step_str_overlap_endpoints_ctn_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_endpoints_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises ≠
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
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                  using hCmdTrans.1
              change StepRuleProperties M [] (__eo_prog_str_overlap_endpoints_ctn a1)
              exact RuleProofs.str_overlap_endpoints_ctn_arg_properties
                M hM a1 hA1Trans hProg
