import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem evaluate_eo_mk_apply_eq_apply_of_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem eo_mk_apply_eq_apply_of_args_ne_stuck (f x : Term) :
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hf hx
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem eo_prog_evaluate_eq_of_ne_stuck (A : Term) :
    __eo_prog_evaluate A ≠ Term.Stuck ->
    __eo_prog_evaluate A =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) (__run_evaluate A) := by
  intro hProg
  cases A <;> simp [__eo_prog_evaluate] at hProg ⊢
  all_goals
    first
    | contradiction
    | exact evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hProg

private theorem eo_prog_evaluate_eq_of_term_and_run_ne_stuck (A : Term) :
    A ≠ Term.Stuck ->
    __run_evaluate A ≠ Term.Stuck ->
    __eo_prog_evaluate A =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) (__run_evaluate A) := by
  intro hA hRun
  cases A
  all_goals
    first
    | exact False.elim (hA rfl)
    | simp only [__eo_prog_evaluate]
      exact eo_mk_apply_eq_apply_of_args_ne_stuck _ _
        (by intro h; cases h) hRun

private def RunEvaluateSoundGoal (M : SmtModel) (A : Term) : Prop :=
  RuleProofs.eo_has_smt_translation A ->
  __eo_typeof (__eo_prog_evaluate A) = Term.Bool ->
  __smtx_typeof (__eo_to_smt A) =
      __smtx_typeof (__eo_to_smt (__run_evaluate A)) ∧
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt A))
      (__smtx_model_eval M (__eo_to_smt (__run_evaluate A)))

private theorem run_evaluate_sound_of_eq_self
    (M : SmtModel) (A : Term)
    (hRun : __run_evaluate A = A) :
  RunEvaluateSoundGoal M A := by
  intro _hATrans _hEvalTy
  rw [hRun]
  exact ⟨rfl, RuleProofs.smt_value_rel_refl _⟩

private theorem run_evaluate_rec_apply_fun
    (M : SmtModel) (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M f :=
  rec f (by
    change sizeOf f < 1 + sizeOf f + sizeOf x
    omega)

private theorem run_evaluate_rec_apply_arg
    (M : SmtModel) (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M x :=
  rec x (by
    change sizeOf x < 1 + sizeOf f + sizeOf x
    omega)

private theorem run_evaluate_rec_apply_apply_arg
    (M : SmtModel) (g y x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.Apply g y) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M y :=
  rec y (by
    change sizeOf y < 1 + (1 + sizeOf g + sizeOf y) + sizeOf x
    omega)

private theorem run_evaluate_rec_apply_apply_apply_arg1
    (M : SmtModel) (g z y x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.Apply g z) y) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M z :=
  rec z (by
    change sizeOf z < 1 + (1 + (1 + sizeOf g + sizeOf z) + sizeOf y) + sizeOf x
    omega)

private theorem run_evaluate_rec_apply_apply_apply_arg2
    (M : SmtModel) (g z y x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.Apply g z) y) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M y :=
  rec y (by
    change sizeOf y < 1 + (1 + (1 + sizeOf g + sizeOf z) + sizeOf y) + sizeOf x
    omega)

private theorem run_evaluate_rec_apply_apply_apply_arg3
    (M : SmtModel) (g z y x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.Apply g z) y) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M x :=
  rec x (by
    change sizeOf x < 1 + (1 + (1 + sizeOf g + sizeOf z) + sizeOf y) + sizeOf x
    omega)

private theorem eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool
    (t : Term) :
    t ≠ Term.Stuck ->
    __eo_typeof t = Term.Bool ->
    __eo_typeof (__run_evaluate t) = Term.Bool ->
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  intro hTNe hTy hRunTy
  have hRunNe : __run_evaluate t ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hRunTy
  have hProgEq :=
    eo_prog_evaluate_eq_of_term_and_run_ne_stuck t hTNe hRunNe
  rw [hProgEq]
  change __eo_typeof_eq (__eo_typeof t) (__eo_typeof (__run_evaluate t)) =
    Term.Bool
  rw [hTy, hRunTy]
  simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
    native_not]

private theorem eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof
    (t T : Term) :
    t ≠ Term.Stuck ->
    T ≠ Term.Stuck ->
    __eo_typeof t = T ->
    __eo_typeof (__run_evaluate t) = T ->
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  intro hTNe hTypeNe hTy hRunTy
  have hRunNe : __run_evaluate t ≠ Term.Stuck := by
    intro hRunStuck
    rw [hRunStuck] at hRunTy
    change Term.Stuck = T at hRunTy
    exact hTypeNe hRunTy.symm
  have hProgEq :=
    eo_prog_evaluate_eq_of_term_and_run_ne_stuck t hTNe hRunNe
  rw [hProgEq]
  change __eo_typeof_eq (__eo_typeof t) (__eo_typeof (__run_evaluate t)) =
    Term.Bool
  rw [hTy, hRunTy]
  simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
    native_not]

private theorem eo_prog_evaluate_typeof_bool_of_smt_type_int
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  sorry

private theorem eo_prog_evaluate_typeof_bool_of_smt_type_bitvec
    (t : Term) (w : native_Nat)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  sorry

private theorem eo_typeof_str_to_lower_eq_seq_char_arg
    {T : Term} :
    __eo_typeof_str_to_lower T =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    T = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  cases T <;> simp [__eo_typeof_str_to_lower] at h ⊢
  case Apply f x =>
    cases f <;> cases x <;> simp at h ⊢
    case UOp.UOp op arg =>
      cases op <;> cases arg <;> simp at h ⊢

private theorem eo_typeof_apply_str_to_lower_eq_seq_char_arg
    (t : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_lower) t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  change __eo_typeof_str_to_lower (__eo_typeof t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
  exact eo_typeof_str_to_lower_eq_seq_char_arg h

private theorem eo_typeof_apply_str_to_upper_eq_seq_char_arg
    (t : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_upper) t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  change __eo_typeof_str_to_lower (__eo_typeof t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
  exact eo_typeof_str_to_lower_eq_seq_char_arg h

private theorem eo_str_to_lower_result_arg_typeof_seq_char
    (t : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_str t)
          (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
            (Term.Boolean true))
          (__eo_mk_apply (Term.UOp UserOp.str_to_lower) t)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  cases t
  case String s =>
    rfl
  all_goals
    apply eo_typeof_apply_str_to_lower_eq_seq_char_arg
    simpa [__eo_is_str, __eo_is_str_internal, __eo_ite, __eo_mk_apply,
      native_ite, native_teq, native_and, native_not] using h

private theorem eo_str_to_upper_result_arg_typeof_seq_char
    (t : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_str t)
          (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
            (Term.Boolean false))
          (__eo_mk_apply (Term.UOp UserOp.str_to_upper) t)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  cases t
  case String s =>
    rfl
  all_goals
    apply eo_typeof_apply_str_to_upper_eq_seq_char_arg
    simpa [__eo_is_str, __eo_is_str_internal, __eo_ite, __eo_mk_apply,
      native_ite, native_teq, native_and, native_not] using h

private theorem eo_typeof_seq_char_of_smt_type_seq_char
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  exact TranslationProofs.eo_to_smt_type_eq_seq_char
    (hMatch.symm.trans hTy)

private theorem eo_typeof_seq_of_smt_type_seq
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    ∃ U : Term,
      __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U ∧
        __eo_to_smt_type U = T := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  exact TranslationProofs.eo_to_smt_type_eq_seq (hMatch.symm.trans hTy)

private theorem eo_typeof_str_rev_eq_seq_arg
    {T U : Term} :
    __eo_typeof_str_rev T = Term.Apply (Term.UOp UserOp.Seq) U ->
    T = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro h
  cases T <;> simp [__eo_typeof_str_rev] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      assumption

private theorem eo_typeof_apply_str_rev_eq_seq_arg
    (t U : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.str_rev) t) =
      Term.Apply (Term.UOp UserOp.Seq) U ->
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro h
  change __eo_typeof_str_rev (__eo_typeof t) =
      Term.Apply (Term.UOp UserOp.Seq) U at h
  exact eo_typeof_str_rev_eq_seq_arg h

private theorem native_char_valid_lt
    {c : native_Char} (hc : native_char_valid c = true) :
    c < 196608 := by
  change decide (c < 196608) = true at hc
  exact of_decide_eq_true hc

private theorem native_str_to_code_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    native_str_to_code [c] = (c : Int) := by
  unfold native_str_to_code
  change (if native_char_valid c = true then (c : Int) else -1) = (c : Int)
  rw [hc]
  rfl

private theorem eo_to_z_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_z (Term.String [c]) = Term.Numeral (c : Int) := by
  have hLen : native_zeq 1 (native_str_len [c]) = true := by
    change decide ((1 : Int) = Int.ofNat [c].length) = true
    rfl
  change (if native_zeq 1 (native_str_len [c]) = true then
        Term.Numeral (native_str_to_code [c]) else Term.Stuck) =
      Term.Numeral (c : Int)
  rw [hLen]
  exact congrArg Term.Numeral (native_str_to_code_singleton hc)

private theorem native_str_from_code_of_valid_nat
    {c : native_Char}
    (hc : native_char_valid c = true) :
    native_str_from_code (c : Int) = [c] := by
  have hNonneg : decide ((0 : Int) ≤ (c : Int)) = true :=
    decide_eq_true (Int.natCast_nonneg c)
  have hValid : native_char_valid (Int.toNat (c : Int)) = true := by
    change native_char_valid c = true
    exact hc
  have hCond : ((decide ((0 : Int) ≤ (c : Int))) &&
      native_char_valid (Int.toNat (c : Int))) = true := by
    rw [hNonneg, hValid]
    rfl
  unfold native_str_from_code
  rw [hCond]
  rfl

private theorem eo_to_str_of_valid_nat
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_str (Term.Numeral (c : Int)) = Term.String [c] := by
  have hcLtNat : c < 196608 := native_char_valid_lt hc
  have hcLtInt : (c : Int) < 196608 := Int.ofNat_lt.mpr hcLtNat
  have hNonneg : native_zleq 0 (c : Int) = true := by
    change decide ((0 : Int) ≤ (c : Int)) = true
    exact decide_eq_true (Int.natCast_nonneg c)
  have hLt : native_zlt (c : Int) 196608 = true := by
    change decide ((c : Int) < (196608 : Int)) = true
    exact decide_eq_true hcLtInt
  have hCond : native_and (native_zleq 0 (c : Int))
      (native_zlt (c : Int) 196608) = true := by
    change (native_zleq 0 (c : Int) &&
      native_zlt (c : Int) 196608) = true
    rw [hNonneg, hLt]
    rfl
  change (if native_and (native_zleq 0 (c : Int))
      (native_zlt (c : Int) 196608) = true then
        Term.String (native_str_from_code (c : Int)) else Term.Stuck) =
      Term.String [c]
  rw [hCond]
  exact congrArg Term.String (native_str_from_code_of_valid_nat hc)

private theorem str_case_lower_guard_singleton
    (c : native_Char) :
    __eo_and
        (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
        (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
      Term.Boolean ((decide (65 ≤ c)) && (decide (c ≤ 90))) := by
  have hUpper : native_zlt (c : Int) 91 = decide (c ≤ 90) := by
    by_cases h : c ≤ 90
    · have hNat : c < 91 := Nat.lt_succ_of_le h
      have hInt : (c : Int) < (91 : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt (c : Int) 91 = true by
        change decide ((c : Int) < (91 : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (c ≤ 90) = true by exact decide_eq_true h]
    · have hInt : ¬ (c : Int) < (91 : Int) := by
        intro hInt
        have hNat : c < 91 := Int.ofNat_lt.mp hInt
        exact h (Nat.le_of_lt_succ hNat)
      rw [show native_zlt (c : Int) 91 = false by
        change decide ((c : Int) < (91 : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (c ≤ 90) = false by exact decide_eq_false h]
  have hLower : native_zlt 64 (c : Int) = decide (65 ≤ c) := by
    by_cases h : 65 ≤ c
    · have hNat : 64 < c := Nat.lt_of_lt_of_le (by decide : 64 < 65) h
      have hInt : (64 : Int) < (c : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt 64 (c : Int) = true by
        change decide ((64 : Int) < (c : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (65 ≤ c) = true by exact decide_eq_true h]
    · have hInt : ¬ (64 : Int) < (c : Int) := by
        intro hInt
        have hNat : 64 < c := Int.ofNat_lt.mp hInt
        exact h (Nat.succ_le_of_lt hNat)
      rw [show native_zlt 64 (c : Int) = false by
        change decide ((64 : Int) < (c : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (65 ≤ c) = false by exact decide_eq_false h]
  change Term.Boolean (native_and (native_zlt (c : Int) 91)
    (native_zlt 64 (c : Int))) = _
  rw [hUpper, hLower]
  cases decide (65 ≤ c) <;> cases decide (c ≤ 90) <;> rfl

private theorem str_case_upper_guard_singleton
    (c : native_Char) :
    __eo_and
        (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
        (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
      Term.Boolean ((decide (97 ≤ c)) && (decide (c ≤ 122))) := by
  have hUpper : native_zlt (c : Int) 123 = decide (c ≤ 122) := by
    by_cases h : c ≤ 122
    · have hNat : c < 123 := Nat.lt_succ_of_le h
      have hInt : (c : Int) < (123 : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt (c : Int) 123 = true by
        change decide ((c : Int) < (123 : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (c ≤ 122) = true by exact decide_eq_true h]
    · have hInt : ¬ (c : Int) < (123 : Int) := by
        intro hInt
        have hNat : c < 123 := Int.ofNat_lt.mp hInt
        exact h (Nat.le_of_lt_succ hNat)
      rw [show native_zlt (c : Int) 123 = false by
        change decide ((c : Int) < (123 : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (c ≤ 122) = false by exact decide_eq_false h]
  have hLower : native_zlt 96 (c : Int) = decide (97 ≤ c) := by
    by_cases h : 97 ≤ c
    · have hNat : 96 < c := Nat.lt_of_lt_of_le (by decide : 96 < 97) h
      have hInt : (96 : Int) < (c : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt 96 (c : Int) = true by
        change decide ((96 : Int) < (c : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (97 ≤ c) = true by exact decide_eq_true h]
    · have hInt : ¬ (96 : Int) < (c : Int) := by
        intro hInt
        have hNat : 96 < c := Int.ofNat_lt.mp hInt
        exact h (Nat.succ_le_of_lt hNat)
      rw [show native_zlt 96 (c : Int) = false by
        change decide ((96 : Int) < (c : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (97 ≤ c) = false by exact decide_eq_false h]
  change Term.Boolean (native_and (native_zlt (c : Int) 123)
    (native_zlt 96 (c : Int))) = _
  rw [hUpper, hLower]
  cases decide (97 ≤ c) <;> cases decide (c ≤ 122) <;> rfl

private theorem str_case_conv_rec_lower_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (Term.String []))
        (Term.Boolean true) =
      Term.String [native_char_to_lower c] := by
  cases hRange : ((decide (65 ≤ c)) && (decide (c ≤ 90)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean false := by
      rw [str_case_lower_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    unfold __str_case_conv_rec
    rw [eo_to_z_singleton hc]
    dsimp
    rw [hGuardFalse]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + 0)))
      (Term.String []) = Term.String [native_char_to_lower c]
    rw [hCast, eo_to_str_of_valid_nat hc]
    unfold native_char_to_lower
    rw [hRange]
    rfl
  · have h90 : c ≤ 90 := by
      cases h65d : decide (65 ≤ c) <;> cases h90d : decide (c ≤ 90) <;>
        simp [h65d, h90d] at hRange
      exact of_decide_eq_true h90d
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean true := by
      rw [str_case_lower_guard_singleton c, hRange]
    have hValidLower : native_char_valid (c + 32) = true := by
      change decide (c + 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.add_le_add_right h90 32) (by decide))
    have hCast : (c : Int) + 32 = ((c + 32 : Nat) : Int) := by
      rw [Int.natCast_add]
      rfl
    unfold __str_case_conv_rec
    rw [eo_to_z_singleton hc]
    dsimp
    rw [hGuardTrue]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + 32)))
      (Term.String []) = Term.String [native_char_to_lower c]
    rw [hCast, eo_to_str_of_valid_nat hValidLower]
    unfold native_char_to_lower
    rw [hRange]
    rfl

private theorem str_case_conv_rec_upper_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (Term.String []))
        (Term.Boolean false) =
      Term.String [native_char_to_upper c] := by
  cases hRange : ((decide (97 ≤ c)) && (decide (c ≤ 122)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean false := by
      rw [str_case_upper_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    unfold __str_case_conv_rec
    rw [eo_to_z_singleton hc]
    dsimp
    rw [hGuardFalse]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + 0)))
      (Term.String []) = Term.String [native_char_to_upper c]
    rw [hCast, eo_to_str_of_valid_nat hc]
    unfold native_char_to_upper
    rw [hRange]
    rfl
  · have h97 : 97 ≤ c := by
      cases h97d : decide (97 ≤ c) <;> cases h122d : decide (c ≤ 122) <;>
        simp [h97d, h122d] at hRange
      exact of_decide_eq_true h97d
    have h32 : 32 ≤ c := Nat.le_trans (by decide) h97
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean true := by
      rw [str_case_upper_guard_singleton c, hRange]
    have hValidUpper : native_char_valid (c - 32) = true := by
      change decide (c - 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.sub_le c 32) (native_char_valid_lt hc))
    have hCast : (c : Int) + (-32 : Int) = ((c - 32 : Nat) : Int) := by
      rw [Int.ofNat_sub h32]
      rfl
    unfold __str_case_conv_rec
    rw [eo_to_z_singleton hc]
    dsimp
    rw [hGuardTrue]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + (-32 : Int))))
      (Term.String []) = Term.String [native_char_to_upper c]
    rw [hCast, eo_to_str_of_valid_nat hValidUpper]
    unfold native_char_to_upper
    rw [hRange]
    rfl

private theorem str_flatten_nary_intro_singleton
    (c : native_Char) :
    __str_flatten (__str_nary_intro (Term.String [c])) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
        (Term.String []) := by
  rfl

private theorem str_case_conv_rec_flatten_lower_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String [c])))
        (Term.Boolean true) =
      Term.String [native_char_to_lower c] := by
  rw [str_flatten_nary_intro_singleton c]
  exact str_case_conv_rec_lower_singleton hc

private theorem str_case_conv_rec_flatten_upper_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String [c])))
        (Term.Boolean false) =
      Term.String [native_char_to_upper c] := by
  rw [str_flatten_nary_intro_singleton c]
  exact str_case_conv_rec_upper_singleton hc

private def strCharChain : native_String -> Term
  | [] => Term.String []
  | c :: cs =>
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
        (strCharChain cs)

private theorem native_string_valid_cons_parts_local
    {c : native_Char} {cs : native_String}
    (h : native_string_valid (c :: cs) = true) :
    native_char_valid c = true ∧ native_string_valid cs = true := by
  simp [native_string_valid] at h
  constructor
  · exact h.1
  · rw [native_string_valid, List.all_eq_true]
    intro x hx
    exact h.2 x hx

private theorem str_case_conv_lower_head_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_str
        (__eo_add (__eo_to_z (Term.String [c]))
          (__eo_ite
            (__eo_and
              (__eo_gt (Term.Numeral 91) (__eo_to_z (Term.String [c])))
              (__eo_gt (__eo_to_z (Term.String [c])) (Term.Numeral 64)))
            (Term.Numeral 32) (Term.Numeral 0))) =
      Term.String [native_char_to_lower c] := by
  cases hRange : ((decide (65 ≤ c)) && (decide (c ≤ 90)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean false := by
      rw [str_case_lower_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    rw [eo_to_z_singleton hc]
    rw [hGuardFalse]
    change __eo_to_str (Term.Numeral ((c : Int) + 0)) =
      Term.String [native_char_to_lower c]
    rw [hCast, eo_to_str_of_valid_nat hc]
    unfold native_char_to_lower
    rw [hRange]
    rfl
  · have h90 : c ≤ 90 := by
      cases h65d : decide (65 ≤ c) <;> cases h90d : decide (c ≤ 90) <;>
        simp [h65d, h90d] at hRange
      exact of_decide_eq_true h90d
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean true := by
      rw [str_case_lower_guard_singleton c, hRange]
    have hValidLower : native_char_valid (c + 32) = true := by
      change decide (c + 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.add_le_add_right h90 32) (by decide))
    have hCast : (c : Int) + 32 = ((c + 32 : Nat) : Int) := by
      rw [Int.natCast_add]
      rfl
    rw [eo_to_z_singleton hc]
    rw [hGuardTrue]
    change __eo_to_str (Term.Numeral ((c : Int) + 32)) =
      Term.String [native_char_to_lower c]
    rw [hCast, eo_to_str_of_valid_nat hValidLower]
    unfold native_char_to_lower
    rw [hRange]
    rfl

private theorem str_case_conv_upper_head_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_str
        (__eo_add (__eo_to_z (Term.String [c]))
          (__eo_ite
            (__eo_and
              (__eo_gt (Term.Numeral 123) (__eo_to_z (Term.String [c])))
              (__eo_gt (__eo_to_z (Term.String [c])) (Term.Numeral 96)))
            (Term.Numeral (-32 : native_Int)) (Term.Numeral 0))) =
      Term.String [native_char_to_upper c] := by
  cases hRange : ((decide (97 ≤ c)) && (decide (c ≤ 122)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean false := by
      rw [str_case_upper_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    rw [eo_to_z_singleton hc]
    rw [hGuardFalse]
    change __eo_to_str (Term.Numeral ((c : Int) + 0)) =
      Term.String [native_char_to_upper c]
    rw [hCast, eo_to_str_of_valid_nat hc]
    unfold native_char_to_upper
    rw [hRange]
    rfl
  · have h97 : 97 ≤ c := by
      cases h97d : decide (97 ≤ c) <;> cases h122d : decide (c ≤ 122) <;>
        simp [h97d, h122d] at hRange
      exact of_decide_eq_true h97d
    have h32 : 32 ≤ c := Nat.le_trans (by decide) h97
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean true := by
      rw [str_case_upper_guard_singleton c, hRange]
    have hValidUpper : native_char_valid (c - 32) = true := by
      change decide (c - 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.sub_le c 32) (native_char_valid_lt hc))
    have hCast : (c : Int) + (-32 : Int) = ((c - 32 : Nat) : Int) := by
      rw [Int.ofNat_sub h32]
      rfl
    rw [eo_to_z_singleton hc]
    rw [hGuardTrue]
    change __eo_to_str (Term.Numeral ((c : Int) + (-32 : Int))) =
      Term.String [native_char_to_upper c]
    rw [hCast, eo_to_str_of_valid_nat hValidUpper]
    unfold native_char_to_upper
    rw [hRange]
    rfl

private theorem str_case_conv_rec_lower_char_chain :
    ∀ s : native_String,
      native_string_valid s = true ->
        __str_case_conv_rec (strCharChain s) (Term.Boolean true) =
          Term.String (native_str_to_lower s)
  | [], _hs => by
      rfl
  | c :: cs, hs => by
      rcases native_string_valid_cons_parts_local hs with ⟨hc, hcs⟩
      have hTail := str_case_conv_rec_lower_char_chain cs hcs
      unfold strCharChain
      unfold __str_case_conv_rec
      dsimp
      rw [str_case_conv_lower_head_singleton hc, hTail]
      rfl

private theorem str_case_conv_rec_upper_char_chain :
    ∀ s : native_String,
      native_string_valid s = true ->
        __str_case_conv_rec (strCharChain s) (Term.Boolean false) =
          Term.String (native_str_to_upper s)
  | [], _hs => by
      rfl
  | c :: cs, hs => by
      rcases native_string_valid_cons_parts_local hs with ⟨hc, hcs⟩
      have hTail := str_case_conv_rec_upper_char_chain cs hcs
      unfold strCharChain
      unfold __str_case_conv_rec
      dsimp
      rw [str_case_conv_upper_head_singleton hc, hTail]
      rfl

private theorem substrWord_zero_eq_strCharChain :
    ∀ s : native_String,
      RuleProofs.substrWord s 0 s.length = strCharChain s
  | [] => by
      rfl
  | c :: cs => by
      rw [show (c :: cs).length = cs.length + 1 from rfl]
      change
        Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String (RuleProofs.extractString (c :: cs) 0)))
            (RuleProofs.substrWord (c :: cs) (0 + 1) cs.length) =
          Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
            (strCharChain cs)
      rw [RuleProofs.extractString_zero_cons c cs]
      rw [show (0 : native_Int) + 1 = 1 by rfl]
      rw [RuleProofs.substrWord_cons_tail c cs]
      rw [substrWord_zero_eq_strCharChain cs]

private theorem str_flatten_nary_intro_string_char_chain
    (s : native_String) :
    __str_flatten (__str_nary_intro (Term.String s)) = strCharChain s := by
  cases s with
  | nil =>
      rw [RuleProofs.str_flatten_nary_intro_empty]
      rfl
  | cons c cs =>
      rw [RuleProofs.str_flatten_nary_intro_cons c cs]
      exact substrWord_zero_eq_strCharChain (c :: cs)

private theorem strCharChain_get_nil :
    ∀ s : native_String,
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
        (strCharChain s) = Term.String []
  | [] => by
      simp [strCharChain, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_list_nil_str_concat, __eo_eq, __eo_requires,
        native_ite, native_teq, native_not]
  | _c :: cs => by
      simp [strCharChain, __eo_get_nil_rec, __eo_requires,
        native_ite, native_teq, native_not]
      exact strCharChain_get_nil cs

private theorem strCharChain_ne_stuck :
    ∀ s : native_String, strCharChain s ≠ Term.Stuck
  | [] => by
      intro h
      cases h
  | _ :: _ => by
      intro h
      cases h

private theorem strCharChain_is_list :
    ∀ s : native_String,
      __eo_is_list (Term.UOp UserOp.str_concat)
        (strCharChain s) = Term.Boolean true
  | [] => by
      change
        __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat) (Term.String [])) =
          Term.Boolean true
      rw [show __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (Term.String []) = Term.String [] by
        exact strCharChain_get_nil []]
      exact eo_is_ok_true_of_ne_stuck _ (by intro h; cases h)
  | c :: cs => by
      change
        __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                (strCharChain cs))) =
          Term.Boolean true
      rw [show __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
            (strCharChain cs)) = Term.String [] by
        exact strCharChain_get_nil (c :: cs)]
      exact eo_is_ok_true_of_ne_stuck _ (by intro h; cases h)

private theorem eo_list_rev_rec_strCharChain :
    ∀ s t : native_String,
      __eo_list_rev_rec (strCharChain s) (strCharChain t) =
        strCharChain (s.reverse ++ t)
  | [], t => by
      cases t <;> rfl
  | c :: cs, t => by
      rw [show strCharChain (c :: cs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (strCharChain cs) by
        rfl]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat)
        (Term.String [c]) (strCharChain cs) (strCharChain t)
        (strCharChain_ne_stuck t)]
      rw [show
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.String [c])) (strCharChain t) =
          strCharChain (c :: t) by
        rfl]
      rw [eo_list_rev_rec_strCharChain cs (c :: t)]
      simp [List.reverse_cons, List.append_assoc]

private theorem eo_list_rev_strCharChain :
    ∀ s : native_String,
      __eo_list_rev (Term.UOp UserOp.str_concat) (strCharChain s) =
        strCharChain s.reverse
  | s => by
      change
        __eo_requires
          (__eo_is_list (Term.UOp UserOp.str_concat) (strCharChain s))
          (Term.Boolean true)
          (__eo_list_rev_rec (strCharChain s)
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (strCharChain s))) =
        strCharChain s.reverse
      rw [strCharChain_is_list s]
      simp [__eo_requires, native_ite, native_teq, native_not]
      rw [strCharChain_get_nil s]
      simpa [strCharChain, List.append_nil] using
        eo_list_rev_rec_strCharChain s []

private theorem str_collect_strCharChain :
    ∀ s : native_String,
      __str_collect (strCharChain s) =
        match s with
        | [] => Term.String []
        | _ =>
            Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) (Term.String s))
              (Term.String [])
  | [] => by
      change
        __eo_requires (Term.String [])
          (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
        Term.String []
      change __eo_requires (Term.String []) (Term.String []) (Term.String []) =
        Term.String []
      exact eo_requires_self_eq_of_ne_stuck _ _
        (by intro h; cases h)
  | c :: cs => by
      have hLen :
          __eo_is_eq (__eo_len (Term.String [c])) (Term.Numeral 1) =
            Term.Boolean true := by
        rfl
      cases cs with
      | nil =>
          change
            __eo_ite
                (__eo_is_eq (__eo_len (Term.String [c])) (Term.Numeral 1))
                (__str_collect_merge (Term.String [c])
                  (__str_collect (Term.String [])))
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                  (__str_collect (Term.String []))) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                (Term.String [])
          rw [hLen, eo_ite_true]
          have hCollectEmpty :
              __str_collect (Term.String []) = Term.String [] := by
            change
              __eo_requires (Term.String [])
                (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
              Term.String []
            change
              __eo_requires (Term.String []) (Term.String []) (Term.String []) =
              Term.String []
            exact eo_requires_self_eq_of_ne_stuck _ _
              (by intro h; cases h)
          rw [hCollectEmpty]
          rfl
      | cons d ds =>
          change
            __eo_ite
                (__eo_is_eq (__eo_len (Term.String [c])) (Term.Numeral 1))
                (__str_collect_merge (Term.String [c])
                  (__str_collect (strCharChain (d :: ds))))
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                  (__str_collect (strCharChain (d :: ds)))) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat)
                  (Term.String (c :: d :: ds)))
                (Term.String [])
          rw [hLen, eo_ite_true]
          rw [str_collect_strCharChain (d :: ds)]
          change
            __eo_ite (__eo_is_str (Term.String (d :: ds)))
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.str_concat)
                    (__eo_concat (Term.String [c]) (Term.String (d :: ds))))
                  (Term.String []))
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat)
                      (Term.String (d :: ds)))
                    (Term.String []))) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat)
                  (Term.String (c :: d :: ds)))
                (Term.String [])
          rw [show __eo_is_str (Term.String (d :: ds)) = Term.Boolean true by
            rfl]
          rw [eo_ite_true]
          rfl

private theorem str_collect_elim_strCharChain :
    ∀ s : native_String,
      __str_nary_elim (__str_collect (strCharChain s)) =
        Term.String s
  | [] => by
      rw [str_collect_strCharChain []]
      change
        __eo_requires (Term.String [])
          (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
        Term.String []
      change __eo_requires (Term.String []) (Term.String []) (Term.String []) =
        Term.String []
      exact eo_requires_self_eq_of_ne_stuck _ _
        (by intro h; cases h)
  | c :: cs => by
      rw [str_collect_strCharChain (c :: cs)]
      change
        __eo_ite
            (__eo_eq (Term.String [])
              (__seq_empty (__eo_typeof (Term.String (c :: cs)))))
            (Term.String (c :: cs))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (Term.String (c :: cs)))
              (Term.String [])) =
          Term.String (c :: cs)
      have hEq :
          __eo_eq (Term.String [])
              (__seq_empty (__eo_typeof (Term.String (c :: cs)))) =
            Term.Boolean true := by
        rfl
      rw [hEq, eo_ite_true]

private theorem str_rev_string_char_chain :
    ∀ s : native_String,
      __str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (strCharChain s))) =
        Term.String s.reverse
  | s => by
      rw [eo_list_rev_strCharChain s]
      exact str_collect_elim_strCharChain s.reverse

private theorem eo_is_str_false_of_not_string
    (t : Term)
    (hNotString : ∀ s : native_String, t ≠ Term.String s) :
    __eo_is_str t = Term.Boolean false := by
  cases t <;>
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not] at hNotString ⊢

private theorem str_rev_result_string
    {s : native_String} :
    __eo_ite (__eo_is_str (Term.String s))
        (__str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro (Term.String s))))))
        (__eo_mk_apply (Term.UOp UserOp.str_rev) (Term.String s)) =
      Term.String s.reverse := by
  have hIsStr :
      __eo_is_str (Term.String s) = Term.Boolean true := by
    rfl
  rw [hIsStr, eo_ite_true]
  rw [str_flatten_nary_intro_string_char_chain]
  exact str_rev_string_char_chain s

private theorem str_rev_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro t)))))
        (__eo_mk_apply (Term.UOp UserOp.str_rev) t) =
      Term.Apply (Term.UOp UserOp.str_rev) t := by
  rw [eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

private theorem eo_str_rev_result_arg_typeof_seq
    (t U : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_str t)
          (__str_nary_elim
            (__str_collect
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__str_nary_intro t)))))
          (__eo_mk_apply (Term.UOp UserOp.str_rev) t)) =
      Term.Apply (Term.UOp UserOp.Seq) U ->
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro h
  cases t
  case String s =>
    rw [str_rev_result_string] at h
    exact h
  all_goals
    apply eo_typeof_apply_str_rev_eq_seq_arg
    simpa [__eo_is_str, __eo_is_str_internal, __eo_ite, __eo_mk_apply,
      native_ite, native_teq, native_and, native_not] using h

private theorem str_to_lower_result_string
    {s : native_String}
    (hValid : native_string_valid s = true) :
    __eo_ite (__eo_is_str (Term.String s))
        (__str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String s)))
          (Term.Boolean true))
        (__eo_mk_apply (Term.UOp UserOp.str_to_lower) (Term.String s)) =
      Term.String (native_str_to_lower s) := by
  have hIsStr :
      __eo_is_str (Term.String s) = Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not]
  rw [hIsStr, eo_ite_true]
  rw [str_flatten_nary_intro_string_char_chain]
  exact str_case_conv_rec_lower_char_chain s hValid

private theorem str_to_upper_result_string
    {s : native_String}
    (hValid : native_string_valid s = true) :
    __eo_ite (__eo_is_str (Term.String s))
        (__str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String s)))
          (Term.Boolean false))
        (__eo_mk_apply (Term.UOp UserOp.str_to_upper) (Term.String s)) =
      Term.String (native_str_to_upper s) := by
  have hIsStr :
      __eo_is_str (Term.String s) = Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not]
  rw [hIsStr, eo_ite_true]
  rw [str_flatten_nary_intro_string_char_chain]
  exact str_case_conv_rec_upper_char_chain s hValid

private theorem str_to_lower_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
          (Term.Boolean true))
        (__eo_mk_apply (Term.UOp UserOp.str_to_lower) t) =
      Term.Apply (Term.UOp UserOp.str_to_lower) t := by
  rw [eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

private theorem str_to_upper_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
          (Term.Boolean false))
        (__eo_mk_apply (Term.UOp UserOp.str_to_upper) t) =
      Term.Apply (Term.UOp UserOp.str_to_upper) t := by
  rw [eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

private theorem smt_value_rel_model_eval_not_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_not a) (__smtx_model_eval_not b) := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel ⊢
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_not, native_veq] at hRel ⊢
  case Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp at hRel ⊢

private theorem smt_value_rel_model_eval_str_to_lower_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_lower a) (__smtx_model_eval_str_to_lower b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_lower, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_model_eval_str_to_upper_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_upper a) (__smtx_model_eval_str_to_upper b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_upper, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_model_eval_str_rev_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_rev a) (__smtx_model_eval_str_rev b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_rev, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_model_eval_and_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_and a b) (__smtx_model_eval_and c d) := by
  intro hAC hBD
  unfold RuleProofs.smt_value_rel at hAC hBD ⊢
  cases a <;> cases c <;> cases b <;> cases d <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_and, native_veq] at hAC hBD ⊢
  case Boolean b₁ b₂ b₃ b₄ =>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
      simp [native_and] at hAC hBD ⊢

private theorem smt_value_rel_model_eval_or_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_or a b) (__smtx_model_eval_or c d) := by
  intro hAC hBD
  unfold RuleProofs.smt_value_rel at hAC hBD ⊢
  cases a <;> cases c <;> cases b <;> cases d <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_or, native_veq] at hAC hBD ⊢
  case Boolean b₁ b₂ b₃ b₄ =>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
      simp [native_or] at hAC hBD ⊢

private theorem smt_value_rel_model_eval_imp_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_imp a b) (__smtx_model_eval_imp c d) := by
  intro hAC hBD
  unfold __smtx_model_eval_imp
  exact smt_value_rel_model_eval_or_of_rel
    (__smtx_model_eval_not a) b (__smtx_model_eval_not c) d
    (smt_value_rel_model_eval_not_of_rel a c hAC) hBD

private theorem smt_value_rel_model_eval_int_pow2_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_int_pow2 a) (__smtx_model_eval_int_pow2 b) := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel ⊢
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_int_pow2,
      native_veq] at hRel ⊢
  case Numeral n m =>
    subst m
    rfl

private theorem smt_typeof_int_ispow2_formula_eq_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Int ->
    __smtx_typeof
        (SmtTerm.and
          (SmtTerm.geq t (SmtTerm.Numeral 0))
          (SmtTerm.eq t
            (SmtTerm.int_pow2 (SmtTerm.int_log2 t)))) =
      SmtType.Bool := by
  intro hTy
  rw [typeof_and_eq, typeof_geq_eq, typeof_eq_eq,
    typeof_int_pow2_eq, typeof_int_log2_eq, hTy, __smtx_typeof.eq_2]
  simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
    __smtx_typeof_guard, native_ite, native_Teq]

private theorem smt_value_rel_boolean_eq
    (v : SmtValue) (b : Bool) :
    RuleProofs.smt_value_rel v (SmtValue.Boolean b) ->
    v = SmtValue.Boolean b := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel
  cases v <;> simp [__smtx_model_eval_eq, native_veq] at hRel
  case Boolean b' =>
    cases b <;> cases b' <;> simp at hRel ⊢

private theorem smt_value_rel_numeral_eq
    (v : SmtValue) (n : native_Int) :
    RuleProofs.smt_value_rel v (SmtValue.Numeral n) ->
    v = SmtValue.Numeral n := by
  intro hRel
  exact (RuleProofs.smt_value_rel_iff_eq
    v (SmtValue.Numeral n) (by
      rintro ⟨r1, r2, _hv, hNum⟩
      cases hNum)).mp hRel

private theorem smt_value_rel_rational_eq
    (v : SmtValue) (q : native_Rat) :
    RuleProofs.smt_value_rel v (SmtValue.Rational q) ->
    v = SmtValue.Rational q := by
  intro hRel
  exact (RuleProofs.smt_value_rel_iff_eq
    v (SmtValue.Rational q) (by
      rintro ⟨r1, r2, _hv, hRat⟩
      cases hRat)).mp hRel

private theorem smt_value_rel_binary_eq
    (v : SmtValue) (w n : native_Int) :
    RuleProofs.smt_value_rel v (SmtValue.Binary w n) ->
    v = SmtValue.Binary w n := by
  intro hRel
  exact (RuleProofs.smt_value_rel_iff_eq
    v (SmtValue.Binary w n) (by
      rintro ⟨r1, r2, _hv, hBin⟩
      cases hBin)).mp hRel

private theorem smtx_typeof_binary_mod_nat_to_int
    (w : native_Nat) (n : native_Int) :
    __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int w)
          (native_mod_total n (native_int_pow2 (native_nat_to_int w)))) =
      SmtType.BitVec w := by
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total n (native_int_pow2 (native_nat_to_int w)))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hWidth :
        native_zleq 0 (native_nat_to_int w) = true := by
      simp [SmtEval.native_zleq, SmtEval.native_nat_to_int]
    have hMod :
        native_zeq
            (native_mod_total n (native_int_pow2 (native_nat_to_int w)))
            (native_mod_total
              (native_mod_total n (native_int_pow2 (native_nat_to_int w)))
              (native_int_pow2 (native_nat_to_int w))) =
          true :=
      native_mod_total_canonical (native_nat_to_int w) n
    simp [SmtEval.native_and, hWidth, hMod, native_ite]
  simpa [SmtEval.native_int_to_nat, SmtEval.native_nat_to_int]
    using
      TranslationProofs.smtx_typeof_binary_of_non_none
        (native_nat_to_int w)
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) hNN

private theorem smtx_typeof_binary_mod_of_nonneg
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true) :
    __smtx_typeof
        (SmtTerm.Binary w
          (native_mod_total n (native_int_pow2 w))) =
      SmtType.BitVec (native_int_to_nat w) := by
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary w
            (native_mod_total n (native_int_pow2 w))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq
            (native_mod_total n (native_int_pow2 w))
            (native_mod_total
              (native_mod_total n (native_int_pow2 w))
              (native_int_pow2 w)) =
          true :=
      native_mod_total_canonical w n
    simp [SmtEval.native_and, hWidth, hMod, native_ite]
  exact
    TranslationProofs.smtx_typeof_binary_of_non_none
      w (native_mod_total n (native_int_pow2 w)) hNN

private theorem smtx_typeof_binary_of_nonneg_and_canonical
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true)
    (hCanon :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    __smtx_typeof (SmtTerm.Binary w n) =
      SmtType.BitVec (native_int_to_nat w) := by
  have hNN :
      __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None := by
    unfold __smtx_typeof
    simp [SmtEval.native_and, hWidth, hCanon, native_ite]
  exact TranslationProofs.smtx_typeof_binary_of_non_none w n hNN

private theorem has_bool_type_not_of_has_translation
    (b : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.not) b) ->
    RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.not (__eo_to_smt b)) ≠ SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.not (__eo_to_smt b)) = SmtType.Bool
  rw [typeof_not_eq]
  rw [typeof_not_eq] at hTrans'
  cases hTy : __smtx_typeof (__eo_to_smt b) <;>
    simp [hTy, native_ite, native_Teq] at hTrans' ⊢

private theorem has_bool_type_and_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_and_eq]
  rw [typeof_and_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

private theorem has_bool_type_or_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_or_eq]
  rw [typeof_or_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

private theorem has_bool_type_xor_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_xor_eq]
  rw [typeof_xor_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

private theorem has_bool_type_imp_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_imp_eq]
  rw [typeof_imp_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

private theorem has_bool_type_imp_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

private theorem has_bool_type_imp_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

private theorem has_bool_type_xor_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
    (typeof_xor_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

private theorem has_bool_type_xor_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
    (typeof_xor_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

private theorem has_bool_type_or_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

private theorem has_bool_type_or_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

private theorem evaluate_eo_typeof_eq_bool_operands_eq
    (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

private theorem evaluate_apply_eq_typeof_bool_operands_eq
    (x y : Term)
    (h : __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) = Term.Bool) :
    __eo_typeof x = __eo_typeof y := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at h
  exact evaluate_eo_typeof_eq_bool_operands_eq
    (__eo_typeof x) (__eo_typeof y) h

private theorem eo_not_arg_boolean_of_typeof_bool
    (t : Term) :
    __eo_typeof (__eo_not t) = Term.Bool ->
    ∃ b : Bool, t = Term.Boolean b := by
  cases t <;> intro h
  case Boolean b =>
    exact ⟨b, rfl⟩
  case Binary w n =>
    change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
      Term.Bool at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

private theorem eo_not_arg_binary_of_typeof_bitvec
    (t : Term) (w : native_Int) :
    __eo_typeof (__eo_not t) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ n : native_Int, t = Term.Binary w n := by
  cases t <;> intro h
  case Binary wt n =>
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wt) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
    exact ⟨n, rfl⟩
  case Boolean b =>
    change Term.Bool =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_and_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_and x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_and] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_and] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_and wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

private theorem eo_and_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_and x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_and] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_and] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_and wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_or_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_or x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_or] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_or] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_or wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

private theorem eo_or_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_or x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_or] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_or] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_or wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_xor_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_xor x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_xor] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_xor] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_xor wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

private theorem eo_xor_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_xor x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_xor] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_xor] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_xor wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_add_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_add x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_add] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_add] at h
    case Rational ry =>
      change Term.UOp UserOp.Real =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_add] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zplus nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_add_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_add x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_add] at h
    case Numeral ny =>
      exact ⟨nx, ny, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_add] at h
    case Rational ry =>
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_add] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zplus nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Int at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          change
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
              Term.UOp UserOp.Int at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Int at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

private theorem eo_add_args_rational_of_typeof_real
    (x y : Term) :
    __eo_typeof (__eo_add x y) = Term.UOp UserOp.Real ->
    ∃ rx : native_Rat, ∃ ry : native_Rat,
      x = Term.Rational rx ∧ y = Term.Rational ry := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_add] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_add] at h
    case Rational ry =>
      exact ⟨rx, ry, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_add] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zplus nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Real at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Real at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          change
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
              Term.UOp UserOp.Real at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Real at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

private theorem eo_mul_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_mul x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_mul] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_mul] at h
    case Rational ry =>
      change Term.UOp UserOp.Real =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_mul] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zmult nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_mul_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_mul x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_mul] at h
    case Numeral ny =>
      exact ⟨nx, ny, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_mul] at h
    case Rational ry =>
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_mul] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zmult nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Int at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          change
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
              Term.UOp UserOp.Int at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Int at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

private theorem eo_mul_args_rational_of_typeof_real
    (x y : Term) :
    __eo_typeof (__eo_mul x y) = Term.UOp UserOp.Real ->
    ∃ rx : native_Rat, ∃ ry : native_Rat,
      x = Term.Rational rx ∧ y = Term.Rational ry := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_mul] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_mul] at h
    case Rational ry =>
      exact ⟨rx, ry, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_mul] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zmult nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Real at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Real at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          change
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
              Term.UOp UserOp.Real at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Real at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

private theorem eo_neg_arg_binary_of_eq_binary
    (x : Term) (w n : native_Int) :
    __eo_neg x = Term.Binary w n ->
    ∃ nx : native_Int, x = Term.Binary w nx := by
  cases x <;> intro h <;> simp [__eo_neg] at h
  case Binary wx nx =>
    rcases h with ⟨hW, _⟩
    cases hW
    exact ⟨nx, rfl⟩

private theorem eo_neg_arg_numeral_of_typeof_int
    (x : Term) :
    __eo_typeof (__eo_neg x) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, x = Term.Numeral nx := by
  cases x <;> intro h
  case Numeral nx =>
    exact ⟨nx, rfl⟩
  case Rational q =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
    cases h
  case Binary w n =>
    simp only [__eo_neg] at h
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
        Term.UOp UserOp.Int at h
    cases h
  all_goals
    simp only [__eo_neg] at h
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

private theorem eo_neg_arg_rational_of_typeof_real
    (x : Term) :
    __eo_typeof (__eo_neg x) = Term.UOp UserOp.Real ->
    ∃ q : native_Rat, x = Term.Rational q := by
  cases x <;> intro h
  case Rational q =>
    exact ⟨q, rfl⟩
  case Numeral nx =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
    cases h
  case Binary w n =>
    simp only [__eo_neg] at h
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
        Term.UOp UserOp.Real at h
    cases h
  all_goals
    simp only [__eo_neg] at h
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

private theorem eo_is_neg_arg_arith_of_typeof_bool
    (x : Term) :
    __eo_typeof (__eo_is_neg x) = Term.Bool ->
      (∃ n : native_Int, x = Term.Numeral n) ∨
        (∃ q : native_Rat, x = Term.Rational q) := by
  cases x <;> intro h
  case Numeral n =>
    exact Or.inl ⟨n, rfl⟩
  case Rational q =>
    exact Or.inr ⟨q, rfl⟩
  all_goals
    simp only [__eo_is_neg] at h
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

private theorem eo_zdiv_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny ∧
        native_zeq 0 ny = false := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zdiv] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · exact ⟨nx, ny, rfl, rfl, hZero⟩
      · simp [hZero, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zdiv] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx (native_binary_max wx))
                (Term.Binary wx
                  (native_mod_total (native_div_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.UOp UserOp.Int at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            change
              Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
                Term.UOp UserOp.Int at h
            cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Int at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

private theorem eo_zmod_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny ∧
        native_zeq 0 ny = false := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · exact ⟨nx, ny, rfl, rfl, hZero⟩
      · simp [hZero, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx nx)
                (Term.Binary wx
                  (native_mod_total (native_mod_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.UOp UserOp.Int at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            change
              Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
                Term.UOp UserOp.Int at h
            cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Int at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

private theorem eo_zmod_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_zmod x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · simp [hZero, native_ite] at h
        change Term.UOp UserOp.Int =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [hZero, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx nx)
                (Term.Binary wx
                  (native_mod_total (native_mod_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            cases h
            exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_zero_extend_literal_arg_binary_of_typeof_bitvec
    (x : Term) (i w : native_Int) :
    __eo_typeof
        (__eo_to_bin
          (__eo_add (__bv_bitwidth (__eo_typeof x)) (Term.Numeral i))
          (__eo_to_z x)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int,
      x = Term.Binary wx nx ∧ w = native_zplus wx i ∧
        __eo_to_bin
            (__eo_add (__bv_bitwidth (__eo_typeof x)) (Term.Numeral i))
            (__eo_to_z x) =
          Term.Binary (native_zplus wx i)
            (native_mod_total nx (native_int_pow2 (native_zplus wx i))) := by
  cases x <;> intro h
  case Binary wx nx =>
    change
      __eo_typeof
          (__eo_to_bin (Term.Numeral (native_zplus wx i))
            (Term.Numeral nx)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change
      __eo_typeof
          (native_ite (native_zleq (native_zplus wx i) 4294967296)
            (__eo_mk_binary (native_zplus wx i) nx) Term.Stuck) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases hLeMax : native_zleq (native_zplus wx i) 4294967296
    · simp [hLeMax, native_ite] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · simp [hLeMax, native_ite, __eo_mk_binary] at h
      cases hNonneg : native_zleq 0 (native_zplus wx i)
      · simp [hNonneg] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [hNonneg] at h
        cases h
        refine ⟨wx, nx, rfl, rfl, ?_⟩
        change
          __eo_to_bin (Term.Numeral (native_zplus wx i))
              (Term.Numeral nx) =
            Term.Binary (native_zplus wx i)
              (native_mod_total nx (native_int_pow2 (native_zplus wx i)))
        simp [__eo_to_bin, __eo_mk_binary, hLeMax, hNonneg, native_ite]
  all_goals
    simp [__eo_to_bin, __eo_add, __bv_bitwidth, __eo_to_z] at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private def eo_eval_sign_extend_rhs (x n : Term) : Term :=
  let bw := __bv_bitwidth (__eo_typeof x)
  let low := __eo_to_z (__eo_extract x (Term.Numeral 0)
    (__eo_add bw (Term.Numeral (-2 : native_Int))))
  let msb := __eo_add bw (Term.Numeral (-1 : native_Int))
  __eo_to_bin (__eo_add bw n)
    (__eo_ite (__eo_eq (__eo_extract x msb msb) (Term.Binary 1 1))
      (__eo_add
        (__eo_neg
          (__eo_ite (__eo_is_z msb)
            (__eo_ite (__eo_is_neg msb) (Term.Numeral 0)
              (__eo_pow (Term.Numeral 2) msb))
            (__eo_mk_apply (Term.UOp UserOp.int_pow2) msb)))
        low)
      low)

private def eo_sign_extend_low_payload
    (w n : native_Int) : native_Int :=
  if native_zlt (native_zplus w (native_zneg 2)) 0 then
    0
  else
    native_mod_total n
      (native_int_pow2 (native_zplus w (native_zneg 1)))

private def eo_sign_extend_msb_set
    (w n : native_Int) : native_Bool :=
  if native_zlt (native_zplus w (native_zneg 1)) 0 then
    false
  else
    native_zeq
      (native_mod_total
        (native_div_total n
          (native_int_pow2 (native_zplus w (native_zneg 1))))
        2) 1

private def eo_sign_extend_payload (w n : native_Int) : native_Int :=
  if eo_sign_extend_msb_set w n then
    native_zplus
      (native_zneg
        (native_int_pow2 (native_zplus w (native_zneg 1))))
      (eo_sign_extend_low_payload w n)
  else
    eo_sign_extend_low_payload w n

private theorem eo_to_bin_literal_width_of_typeof_bitvec
    (y : Term) (wi w : native_Int) :
    __eo_typeof (__eo_to_bin (Term.Numeral wi) y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    w = wi := by
  cases y <;> intro h <;>
    simp [__eo_to_bin, __eo_mk_binary, native_ite] at h
  case Numeral n =>
    cases hLe : native_zleq wi 4294967296 <;> simp [hLe] at h
    · change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · cases hNonneg : native_zleq 0 wi <;> simp [hNonneg] at h
      · change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · cases h
        rfl
  case Binary wb nb =>
    cases hLe : native_zleq wi 4294967296 <;> simp [hLe] at h
    · change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · cases hNonneg : native_zleq 0 wi <;> simp [hNonneg] at h
      · change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · cases h
        rfl
  all_goals
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_to_bin_numeral_eq_of_typeof_bitvec
    (p wi w : native_Int) :
    __eo_typeof (__eo_to_bin (Term.Numeral wi) (Term.Numeral p)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    __eo_to_bin (Term.Numeral wi) (Term.Numeral p) =
      Term.Binary wi
        (native_mod_total p (native_int_pow2 wi)) := by
  intro h
  change
    __eo_typeof
        (native_ite (native_zleq wi 4294967296)
          (__eo_mk_binary wi p) Term.Stuck) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
  cases hLe : native_zleq wi 4294967296
  · simp [hLe, native_ite] at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  · simp [hLe, native_ite, __eo_mk_binary] at h
    cases hNonneg : native_zleq 0 wi
    · simp [hNonneg] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · simp [hNonneg] at h
      simp [__eo_to_bin, __eo_mk_binary, hLe, hNonneg, native_ite]

private theorem eo_eval_sign_extend_rhs_binary_of_typeof_bitvec
    (x : Term) (i w : native_Int) :
    __eo_typeof (eo_eval_sign_extend_rhs x (Term.Numeral i)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int,
      x = Term.Binary wx nx ∧ w = native_zplus wx i := by
  cases x <;> intro h
  case Binary wx nx =>
    change
      __eo_typeof
          (__eo_to_bin (Term.Numeral (native_zplus wx i)) _) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    have hW :=
      eo_to_bin_literal_width_of_typeof_bitvec _
        (native_zplus wx i) w h
    exact ⟨wx, nx, rfl, hW⟩
  all_goals
    dsimp [eo_eval_sign_extend_rhs] at h
    simp only [__eo_extract, __eo_eq, __eo_ite, __eo_to_bin,
      __eo_to_z] at h
    first
    | change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    | have hTrue :
          native_teq Term.Stuck (Term.Boolean true) = false := by
        native_decide
      have hFalse :
          native_teq Term.Stuck (Term.Boolean false) = false := by
        native_decide
      rw [hTrue, hFalse] at h
      simp [native_ite] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h

private theorem eo_extract_literal_arg_binary_of_typeof_bitvec
    (x : Term) (i j w : native_Int)
    (hj0 : native_zleq 0 j = true)
    (hji : native_zleq j i = true) :
    __eo_typeof (__eo_extract x (Term.Numeral j) (Term.Numeral i)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int,
      x = Term.Binary wx nx ∧
        w = native_zplus (native_zplus i (native_zneg j)) 1 ∧
        __eo_extract x (Term.Numeral j) (Term.Numeral i) =
          Term.Binary (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract wx nx i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1))) := by
  cases x <;> intro h
  case Binary wx nx =>
    have hjNonneg : 0 <= j := by
      simpa [native_zleq, SmtEval.native_zleq] using hj0
    have hjiInt : j <= i := by
      simpa [native_zleq, SmtEval.native_zleq] using hji
    have hjNotNeg : native_zlt j 0 = false := by
      simpa [native_zlt, SmtEval.native_zlt] using
        Int.not_lt_of_ge hjNonneg
    have hDeltaNonneg : 0 <= i + -j := by
      simpa [Int.sub_eq_add_neg] using (Int.sub_nonneg.mpr hjiInt)
    have hDeltaNotNeg : native_zlt (i + -j) 0 = false := by
      simpa [native_zlt, SmtEval.native_zlt] using
        Int.not_lt_of_ge hDeltaNonneg
    have hDeltaNotNegNative :
        native_zlt (i + native_zneg j) 0 = false := by
      simpa [native_zneg, SmtEval.native_zneg] using hDeltaNotNeg
    have hWidthNonneg : native_zleq 0 (i + -j + 1) = true := by
      have hNonneg : 0 <= i + -j + 1 :=
        Int.add_nonneg hDeltaNonneg (by decide)
      simpa [native_zleq, SmtEval.native_zleq] using hNonneg
    have hWidthNonnegNative :
        native_zleq 0 (i + native_zneg j + 1) = true := by
      simpa [native_zneg, SmtEval.native_zneg] using hWidthNonneg
    change
      __eo_typeof
          (native_ite
            (native_or (native_zlt j 0) (native_zlt (i + -j) 0))
            (Term.Binary 0 0)
            (__eo_mk_binary (native_zplus (i + -j) 1)
              (native_binary_extract wx nx i j))) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    simp [hjNotNeg, hDeltaNotNeg, native_or, native_ite,
      __eo_mk_binary, hWidthNonneg, native_zplus,
      SmtEval.native_zplus] at h
    cases h
    refine ⟨wx, nx, rfl, rfl, ?_⟩
    change
      native_ite
          (native_or (native_zlt j 0)
            (native_zlt (i + native_zneg j) 0))
          (Term.Binary 0 0)
          (__eo_mk_binary (native_zplus (i + native_zneg j) 1)
            (native_binary_extract wx nx i j)) =
        Term.Binary (native_zplus (native_zplus i (native_zneg j)) 1)
          (native_mod_total (native_binary_extract wx nx i j)
            (native_int_pow2
              (native_zplus (native_zplus i (native_zneg j)) 1)))
    simp [hjNotNeg, hDeltaNotNegNative, hWidthNonnegNative,
      __eo_mk_binary, native_or, native_ite, native_zplus,
      SmtEval.native_zplus]
  case String s =>
    change
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_sign_extend_low_payload_eq
    (w n : native_Int) :
    __eo_to_z
        (__eo_extract (Term.Binary w n) (Term.Numeral 0)
          (Term.Numeral (native_zplus w (native_zneg 2)))) =
      Term.Numeral (eo_sign_extend_low_payload w n) := by
  by_cases hNeg :
      native_zlt (native_zplus w (native_zneg 2)) 0 = true
  · have hNegPrime : native_zlt (w + -2) 0 = true := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNeg
    simp [__eo_extract, __eo_to_z, eo_sign_extend_low_payload,
      hNegPrime, native_ite, native_or, native_zplus,
      SmtEval.native_zplus, native_zneg, SmtEval.native_zneg]
  · have hNegFalse :
        native_zlt (native_zplus w (native_zneg 2)) 0 = false := by
      cases h : native_zlt (native_zplus w (native_zneg 2)) 0 <;>
        simp [h] at hNeg ⊢
    have hNegPrime : native_zlt (w + -2) 0 = false := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNegFalse
    have hGe : 0 <= w + -2 := by
      simpa [native_zlt, SmtEval.native_zlt] using hNegPrime
    have hNonnegPred : 0 <= w + -2 + 1 :=
      Int.add_nonneg hGe (by decide)
    have hPowArg : w + -2 + 1 = w + -1 := by
      rw [Int.add_assoc]
      have hConst : (-2 : native_Int) + 1 = -1 := by
        native_decide
      rw [hConst]
    have hLe : native_zleq 0 (w + -1) = true := by
      have hTmp : native_zleq 0 (w + -2 + 1) = true := by
        simpa [native_zleq, SmtEval.native_zleq] using hNonnegPred
      simpa [hPowArg] using hTmp
    have hDiv : native_div_total n (native_int_pow2 0) = n := by
      simp [native_div_total, native_int_pow2, native_zexp_total]
    have hZlt00 : native_zlt 0 0 = false := by
      native_decide
    simp [__eo_extract, __eo_to_z, __eo_mk_binary,
      eo_sign_extend_low_payload, hNegPrime, hLe, hDiv, hPowArg,
      hZlt00, native_binary_extract, native_ite, native_or,
      native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg]

private theorem eo_sign_extend_msb_eq
    (w n : native_Int) :
    __eo_eq
        (__eo_extract (Term.Binary w n)
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral (native_zplus w (native_zneg 1))))
        (Term.Binary 1 1) =
      Term.Boolean (eo_sign_extend_msb_set w n) := by
  by_cases hNeg :
      native_zlt (native_zplus w (native_zneg 1)) 0 = true
  · have hNegPrime : native_zlt (w + -1) 0 = true := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNeg
    simp [__eo_extract, __eo_eq, eo_sign_extend_msb_set,
      hNegPrime, native_ite, native_or, native_teq,
      native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg]
  · have hNegFalse :
        native_zlt (native_zplus w (native_zneg 1)) 0 = false := by
      cases h : native_zlt (native_zplus w (native_zneg 1)) 0 <;>
        simp [h] at hNeg ⊢
    have hNegPrime : native_zlt (w + -1) 0 = false := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNegFalse
    have hDelta : w + -1 + -(w + -1) = 0 :=
      Int.add_right_neg (w + -1)
    have hWidth : w + -1 + -(w + -1) + 1 = 1 := by
      rw [hDelta]
      rfl
    have hLe1 : native_zleq 0 (1 : native_Int) = true := by
      native_decide
    have hPow1 : native_int_pow2 (1 : native_Int) = 2 := by
      native_decide
    have hZlt00 : native_zlt 0 0 = false := by
      native_decide
    simp [__eo_extract, __eo_eq, __eo_mk_binary,
      eo_sign_extend_msb_set, hNegPrime, hDelta,
      hLe1, hPow1, hZlt00, native_binary_extract,
      native_ite, native_or, native_teq, native_zeq,
      SmtEval.native_zeq, native_zplus, SmtEval.native_zplus,
      native_zneg, SmtEval.native_zneg]
    constructor <;> intro h <;> exact h.symm

private theorem eo_int_pow2_literal_eq (k : native_Int) :
    __eo_ite (__eo_is_z (Term.Numeral k))
      (__eo_ite (__eo_is_neg (Term.Numeral k)) (Term.Numeral 0)
        (__eo_pow (Term.Numeral 2) (Term.Numeral k)))
      (__eo_mk_apply (Term.UOp UserOp.int_pow2) (Term.Numeral k)) =
    Term.Numeral (native_int_pow2 k) := by
  by_cases hk : k < 0
  · have hlt : native_zlt k 0 = true := by
      simpa [native_zlt, SmtEval.native_zlt] using hk
    simp [__eo_ite, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      native_ite, native_teq, native_and, native_not,
      hlt, native_int_pow2, native_zexp_total, hk]
  · have hlt : native_zlt k 0 = false := by
      simpa [native_zlt, SmtEval.native_zlt] using hk
    simp [__eo_ite, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      __eo_pow, native_ite, native_teq, native_and, native_not,
      hlt, native_int_pow2, native_zexp_total, hk]

private theorem eo_eval_sign_extend_rhs_binary_to_bin
    (w n i : native_Int) :
    eo_eval_sign_extend_rhs (Term.Binary w n) (Term.Numeral i) =
      __eo_to_bin (Term.Numeral (native_zplus w i))
        (Term.Numeral (eo_sign_extend_payload w n)) := by
  dsimp [eo_eval_sign_extend_rhs]
  change
    __eo_to_bin (Term.Numeral (native_zplus w i))
      (__eo_ite
        (__eo_eq
          (__eo_extract (Term.Binary w n)
            (Term.Numeral (native_zplus w (native_zneg 1)))
            (Term.Numeral (native_zplus w (native_zneg 1))))
          (Term.Binary 1 1))
        (__eo_add
          (__eo_neg
            (__eo_ite
              (__eo_is_z
                (Term.Numeral (native_zplus w (native_zneg 1))))
              (__eo_ite
                (__eo_is_neg
                  (Term.Numeral (native_zplus w (native_zneg 1))))
                (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2)
                  (Term.Numeral (native_zplus w (native_zneg 1)))))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (Term.Numeral (native_zplus w (native_zneg 1))))))
          (__eo_to_z
            (__eo_extract (Term.Binary w n) (Term.Numeral 0)
              (Term.Numeral (native_zplus w (native_zneg 2))))))
        (__eo_to_z
          (__eo_extract (Term.Binary w n) (Term.Numeral 0)
            (Term.Numeral (native_zplus w (native_zneg 2)))))) =
      _
  rw [eo_sign_extend_msb_eq, eo_sign_extend_low_payload_eq,
    eo_int_pow2_literal_eq]
  cases hMsb : eo_sign_extend_msb_set w n
  · simp [eo_sign_extend_payload, hMsb, __eo_ite, native_ite,
      native_teq]
  · simp [eo_sign_extend_payload, hMsb, __eo_ite, __eo_add,
      __eo_neg, native_ite, native_teq]

private theorem native_int_pow2_succ_pred
    {w : native_Int} (hwpos : 0 < w) :
    native_int_pow2 w = 2 * native_int_pow2 (w - 1) := by
  have hw0 : 0 <= w := Int.le_of_lt hwpos
  have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
  have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
  have hnotW : ¬ w < 0 := Int.not_lt_of_ge hw0
  have hnotP : ¬ w - 1 < 0 := Int.not_lt_of_ge hwp0
  have hNat : w.toNat = (w - 1).toNat + 1 := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_add, Int.natCast_one]
    rw [Int.toNat_of_nonneg hw0, Int.toNat_of_nonneg hwp0]
    omega
  rw [native_int_pow2, native_int_pow2, native_zexp_total,
    native_zexp_total]
  simp [hnotW, hnotP]
  rw [hNat]
  have hSub : (w - 1).toNat + 1 - 1 = (w - 1).toNat :=
    Nat.add_sub_cancel (w - 1).toNat 1
  rw [hSub]
  rw [← Nat.succ_eq_add_one]
  rw [Int.pow_succ]
  rw [Int.mul_comm]

private theorem eo_sign_extend_low_payload_eq_mod_of_pos
    {w n : native_Int} (hwpos : 0 < w) :
    eo_sign_extend_low_payload w n =
      native_mod_total n
        (native_int_pow2 (native_zplus w (native_zneg 1))) := by
  by_cases hNeg :
      native_zlt (native_zplus w (native_zneg 2)) 0 = true
  · have hlt : w + -2 < 0 := by
      simpa [native_zlt, SmtEval.native_zlt, native_zplus,
        SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] using
        hNeg
    have hwEq : w = 1 := by
      have hlt2 : w < 2 := by
        have h := Int.add_lt_add_right hlt 2
        have hLeft : w + -2 + 2 = w := by
          rw [Int.add_assoc]
          have hc : (-2 : Int) + 2 = 0 := by
            native_decide
          rw [hc, Int.add_zero]
        have hRight : (0 : Int) + 2 = 2 := by
          rfl
        simpa [hLeft, hRight] using h
      have hle1 : w <= 1 := Int.le_of_lt_add_one hlt2
      have hge1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      exact Int.le_antisymm hle1 hge1
    subst w
    simp [eo_sign_extend_low_payload, native_zplus,
      SmtEval.native_zplus, native_zneg, SmtEval.native_zneg,
      native_zlt, SmtEval.native_zlt, native_int_pow2,
      native_zexp_total, native_mod_total]
  · have hNegFalse :
        native_zlt (native_zplus w (native_zneg 2)) 0 = false := by
      cases h : native_zlt (native_zplus w (native_zneg 2)) 0 <;>
        simp [h] at hNeg ⊢
    simp [eo_sign_extend_low_payload, hNegFalse]

private theorem sign_payload_eq_uts_core
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    (if native_zeq
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2)
          1 then
        native_zplus (native_zneg (native_int_pow2 (w - 1)))
          (native_mod_total n (native_int_pow2 (w - 1)))
      else
        native_mod_total n (native_int_pow2 (w - 1))) =
      native_binary_uts w n := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    let q := native_div_total n p
    let r := native_mod_total n p
    have hpPos : 0 < p := by
      have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
      have hnot : ¬ w - 1 < 0 := Int.not_lt_of_ge hwp0
      simp [p, native_int_pow2, native_zexp_total, hnot]
      exact Int.pow_pos (by decide)
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow : native_int_pow2 w = 2 * p := by
      simpa [p] using native_int_pow2_succ_pred (w := w) hwpos
    have hqNonneg : 0 <= q :=
      Int.ediv_nonneg hRange.1 (Int.le_of_lt hpPos)
    have hqLt2 : q < 2 := by
      have hlt : n < 2 * p := by
        simpa [hPow] using hRange.2
      exact Int.ediv_lt_of_lt_mul hpPos hlt
    have hqCases : q = 0 ∨ q = 1 := by
      by_cases hq0 : q = 0
      · exact Or.inl hq0
      · have hqPos : 0 < q := by
          rcases Int.lt_or_eq_of_le hqNonneg with hlt | heq
          · exact hlt
          · exact False.elim (hq0 heq.symm)
        have hqGe1 : 1 <= q := (Int.add_one_le_iff).mpr hqPos
        have hqLe1 : q <= 1 := Int.le_of_lt_add_one hqLt2
        exact Or.inr (Int.le_antisymm hqLe1 hqGe1)
    have hDivMod : p * q + r = n := by
      simpa [q, r, p, native_div_total, native_mod_total] using
        Int.mul_ediv_add_emod n p
    have hNMod : native_mod_total n p = r := by
      rfl
    rcases hqCases with hq | hq
    · have hSign : native_zeq (native_mod_total q 2) 1 = false := by
        simp [hq, native_zeq, native_mod_total]
      have hnEq : n = r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hCond :
          native_zeq
              (native_mod_total
                (native_div_total n (native_int_pow2 (w - 1))) 2)
              1 =
            false := by
        simpa [q, p] using hSign
      rw [hCond]
      change native_mod_total n p = native_binary_uts w n
      rw [native_binary_uts]
      change native_mod_total n p =
        native_zplus (native_zmult 2 (native_mod_total n p))
          (native_zneg n)
      rw [hnEq] at hNMod
      rw [hnEq, hNMod]
      simp [native_zplus, native_zmult, native_zneg]
      rw [Int.two_mul]
      rw [Int.add_assoc]
      rw [Int.add_right_neg]
      rw [Int.add_zero]
    · have hSign : native_zeq (native_mod_total q 2) 1 = true := by
        simp [hq, native_zeq, native_mod_total]
      have hnEq : n = p + r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hCond :
          native_zeq
              (native_mod_total
                (native_div_total n (native_int_pow2 (w - 1))) 2)
              1 =
            true := by
        simpa [q, p] using hSign
      rw [hCond]
      change
        native_zplus (native_zneg p) (native_mod_total n p) =
          native_binary_uts w n
      rw [native_binary_uts]
      change
        native_zplus (native_zneg p) (native_mod_total n p) =
          native_zplus (native_zmult 2 (native_mod_total n p))
            (native_zneg n)
      rw [hnEq] at hNMod
      rw [hnEq, hNMod]
      simp [native_zplus, native_zmult, native_zneg]
      rw [Int.two_mul]
      rw [Int.neg_add]
      rw [Int.add_assoc]
      rw [show r + (-p + -r) = -p by
        calc
          r + (-p + -r) = r + (-r + -p) := by
            rw [Int.add_comm (-p) (-r)]
          _ = r + -r + -p := by
            rw [← Int.add_assoc]
          _ = 0 + -p := by
            rw [Int.add_right_neg]
          _ = -p := by
            rw [Int.zero_add]]
      rw [Int.add_comm]
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    native_decide

private theorem eo_sign_extend_payload_eq_uts
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    eo_sign_extend_payload w n = native_binary_uts w n := by
  by_cases hwpos : 0 < w
  · have hLow :=
      eo_sign_extend_low_payload_eq_mod_of_pos
        (w := w) (n := n) hwpos
    have hMsbNeg :
        native_zlt (native_zplus w (native_zneg 1)) 0 = false := by
      have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      have hwp0Sub : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
      have hwp0 : 0 <= w + -1 := by
        simpa [Int.sub_eq_add_neg] using hwp0Sub
      simpa [native_zlt, SmtEval.native_zlt, native_zplus,
        SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] using
        Int.not_lt_of_ge hwp0
    rw [eo_sign_extend_payload, eo_sign_extend_msb_set, hMsbNeg,
      hLow]
    simpa [native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg, Int.sub_eq_add_neg] using
      sign_payload_eq_uts_core (w := w) (n := n) hw0 hCanon
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    native_decide

private theorem term_apply_ne_stuck (f x : Term) :
    Term.Apply f x ≠ Term.Stuck := by
  intro h
  cases h

private theorem bv_list_repeat_rec_binary_ne_stuck
    (w n : native_Int) :
    ∀ k : native_Nat,
      __eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n) k ≠
        Term.Stuck := by
  intro k
  induction k with
  | zero =>
      change Term.Binary 0 0 ≠ Term.Stuck
      intro h
      cases h
  | succ k ih =>
      change
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k) ≠
          Term.Stuck
      rw [eo_mk_apply_eq_apply_of_args_ne_stuck _ _
        (term_apply_ne_stuck _ _) ih]
      exact term_apply_ne_stuck _ _

private theorem bv_list_repeat_rec_binary_succ_eq
    (w n : native_Int) (k : native_Nat) :
    __eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
        (Nat.succ k) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          k) := by
  change
    __eo_mk_apply
        (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          k) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          k)
  exact eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (term_apply_ne_stuck _ _)
    (bv_list_repeat_rec_binary_ne_stuck w n k)

private theorem bv_eval_concat_list_repeat_rec_binary
    (w n : native_Int)
    (hWNonneg : native_zleq 0 w = true) :
    ∀ k : native_Nat,
      ∃ m : native_Int,
        __bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k) =
          Term.Binary (native_zmult (native_nat_to_int k) w) m ∧
        __smtx_model_eval_repeat_rec k (SmtValue.Binary w n) =
          SmtValue.Binary (native_zmult (native_nat_to_int k) w) m ∧
        native_zeq m
          (native_mod_total m
            (native_int_pow2
              (native_zmult (native_nat_to_int k) w))) =
          true
  | Nat.zero => by
      refine ⟨0, ?_, ?_, ?_⟩
      · change Term.Binary 0 0 =
          Term.Binary (native_zmult (native_nat_to_int 0) w) 0
        simp [SmtEval.native_zmult, SmtEval.native_nat_to_int]
      · simp [__smtx_model_eval_repeat_rec, SmtEval.native_zmult,
          SmtEval.native_nat_to_int]
      · simp [SmtEval.native_zeq, SmtEval.native_mod_total,
          SmtEval.native_zmult, SmtEval.native_nat_to_int]
  | Nat.succ k => by
      rcases bv_eval_concat_list_repeat_rec_binary w n hWNonneg k with
        ⟨m, hTerm, hEval, _hCanon⟩
      let recW := native_zmult (native_nat_to_int k) w
      let newW := native_zmult (native_nat_to_int (Nat.succ k)) w
      let newM :=
        native_mod_total (native_binary_concat w n recW m)
          (native_int_pow2 newW)
      have hWidthEq :
          native_zplus w recW = newW := by
        have hWidthEqInt : w + ↑k * w = (↑k + 1) * w := by
          calc
            w + ↑k * w = 1 * w + ↑k * w := by simp
            _ = (1 + ↑k) * w := by rw [Int.add_mul]
            _ = (↑k + 1) * w := by simp [Int.add_comm]
        simpa [recW, newW, SmtEval.native_zplus, SmtEval.native_zmult,
          SmtEval.native_nat_to_int] using hWidthEqInt
      have hWidthNonneg :
          native_zleq 0 (native_zplus w recW) = true := by
        have hw : 0 <= w := by
          simpa [SmtEval.native_zleq] using hWNonneg
        have hk : 0 <= native_nat_to_int k := by
          simp [SmtEval.native_nat_to_int]
        have hRecW : 0 <= recW := by
          simpa [recW, SmtEval.native_zmult] using Int.mul_nonneg hk hw
        have hAdd : 0 <= w + recW := Int.add_nonneg hw hRecW
        simpa [SmtEval.native_zleq, SmtEval.native_zplus] using hAdd
      refine ⟨newM, ?_, ?_, ?_⟩
      · rw [bv_list_repeat_rec_binary_succ_eq]
        change
          __eo_concat (Term.Binary w n)
              (__bv_eval_concat
                (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                  (Term.Binary w n) k)) =
            Term.Binary newW newM
        rw [hTerm]
        change
          __eo_mk_binary (native_zplus w recW)
              (native_binary_concat w n recW m) =
            Term.Binary newW newM
        have hMk :
            __eo_mk_binary (native_zplus w recW)
                (native_binary_concat w n recW m) =
              Term.Binary (native_zplus w recW)
                (native_mod_total (native_binary_concat w n recW m)
                  (native_int_pow2 (native_zplus w recW))) := by
          simp [__eo_mk_binary, hWidthNonneg, native_ite]
        rw [hMk]
        exact congrArg
          (fun z =>
            Term.Binary z
              (native_mod_total (native_binary_concat w n recW m)
                (native_int_pow2 z)))
          hWidthEq
      · rw [__smtx_model_eval_repeat_rec, hEval, __smtx_model_eval_concat]
        exact congrArg
          (fun z =>
            SmtValue.Binary z
              (native_mod_total (native_binary_concat w n recW m)
                (native_int_pow2 z)))
          hWidthEq
      · exact native_mod_total_canonical newW
          (native_binary_concat w n recW m)

private theorem bv_eval_concat_list_repeat_binary_eval
    (M : SmtModel) (i w n : native_Int)
    (hi0 : native_zleq 0 i = true)
    (hWNonneg : native_zleq 0 w = true) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_eval_concat
            (__eo_list_repeat (Term.UOp UserOp.concat)
              (Term.Binary w n) (Term.Numeral i)))) =
      __smtx_model_eval_repeat_rec (native_int_to_nat i)
        (SmtValue.Binary w n) := by
  have hiNonneg : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hiNotNeg : native_zlt i 0 = false := by
    simp [SmtEval.native_zlt]
    omega
  have hList :
      __eo_list_repeat (Term.UOp UserOp.concat) (Term.Binary w n)
          (Term.Numeral i) =
        __eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          (native_int_to_nat i) := by
    simp [__eo_list_repeat, native_ite, hiNotNeg]
  rcases bv_eval_concat_list_repeat_rec_binary w n hWNonneg
      (native_int_to_nat i) with
    ⟨m, hTerm, hEval, _hCanon⟩
  rw [hList, hTerm, hEval]
  change
    __smtx_model_eval M
        (SmtTerm.Binary
          (native_zmult (native_nat_to_int (native_int_to_nat i)) w) m) =
      SmtValue.Binary
        (native_zmult (native_nat_to_int (native_int_to_nat i)) w) m
  rw [__smtx_model_eval.eq_5]

private theorem bv_eval_concat_list_repeat_rec_binary_stuck_of_neg
    (w n : native_Int)
    (hWNeg : native_zleq 0 w = false) :
    ∀ k : native_Nat,
      k ≠ 0 ->
        __bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k) =
          Term.Stuck := by
  intro k hk
  induction k with
  | zero =>
      exact False.elim (hk rfl)
  | succ k ih =>
      rw [bv_list_repeat_rec_binary_succ_eq]
      change
        __eo_concat (Term.Binary w n)
          (__bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k)) =
          Term.Stuck
      cases k with
      | zero =>
          change __eo_concat (Term.Binary w n) (Term.Binary 0 0) =
            Term.Stuck
          change
            __eo_mk_binary (native_zplus w 0)
                (native_binary_concat w n 0 0) =
              Term.Stuck
          have hWidth :
              native_zleq 0 (native_zplus w 0) = false := by
            simpa [SmtEval.native_zleq, SmtEval.native_zplus]
              using hWNeg
          simp [__eo_mk_binary, hWidth, native_ite]
      | succ k' =>
          have hTail :
              __bv_eval_concat
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Binary w n) (Nat.succ k')) =
                Term.Stuck := by
            exact ih (by intro h; cases h)
          rw [hTail]
          rfl

private theorem bv_eval_concat_list_repeat_rec_not_binary_stuck
    (x : Term)
    (hNotBinary : ¬ ∃ w : native_Int, ∃ n : native_Int,
      x = Term.Binary w n) :
    ∀ k : native_Nat,
      k ≠ 0 ->
        __bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat) x k) =
          Term.Stuck := by
  intro k hk
  induction k with
  | zero =>
      exact False.elim (hk rfl)
  | succ k ih =>
      cases x with
      | Stuck =>
          rfl
      | String s =>
          cases k with
          | zero =>
              change
                __bv_eval_concat
                    (__eo_mk_apply
                      (Term.Apply (Term.UOp UserOp.concat) (Term.String s))
                      (Term.Binary 0 0)) =
                  Term.Stuck
              rw [eo_mk_apply_eq_apply_of_args_ne_stuck _ _
                (term_apply_ne_stuck _ _)
                (by intro h; cases h)]
              rfl
          | succ k' =>
              change
                __bv_eval_concat
                    (__eo_mk_apply
                      (Term.Apply (Term.UOp UserOp.concat) (Term.String s))
                      (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                        (Term.String s) (Nat.succ k'))) =
                  Term.Stuck
              by_cases hTailStuck :
                  __eo_list_repeat_rec (Term.UOp UserOp.concat)
                      (Term.String s) (Nat.succ k') =
                    Term.Stuck
              · rw [hTailStuck]
                rfl
              · rw [eo_mk_apply_eq_apply_of_args_ne_stuck _ _
                  (term_apply_ne_stuck _ _) hTailStuck]
                change
                  __eo_concat (Term.String s)
                    (__bv_eval_concat
                      (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                        (Term.String s) (Nat.succ k'))) =
                    Term.Stuck
                have hTailEval :
                    __bv_eval_concat
                        (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                          (Term.String s) (Nat.succ k')) =
                      Term.Stuck :=
                  ih (by intro h; cases h)
                rw [hTailEval]
                rfl
      | Binary w n =>
          exfalso
          exact hNotBinary ⟨w, n, rfl⟩
      | __eo_List =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.__eo_List)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.__eo_List k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.__eo_List k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | __eo_List_nil =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.__eo_List_nil)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.__eo_List_nil k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.__eo_List_nil k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Bool =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.Bool)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.Bool k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.Bool k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Boolean b =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Boolean b))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Boolean b) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Boolean b) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Numeral n =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Numeral n))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Numeral n) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Numeral n) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Rational q =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Rational q))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Rational q) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Rational q) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | «Type» =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.Type)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.Type k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.Type k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DatatypeTypeRef s =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DatatypeTypeRef s))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DatatypeTypeRef s) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DatatypeTypeRef s) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp op =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.UOp op))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp op) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp op) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp1 op a =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.UOp1 op a))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp1 op a) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp1 op a) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp2 op a b =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.UOp2 op a b))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp2 op a b) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp2 op a b) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp3 op a b c =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.UOp3 op a b c))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp3 op a b c) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp3 op a b c) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Apply f a =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Apply f a))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Apply f a) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Apply f a) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Var s T =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Var s T))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Var s T) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Var s T) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DtcAppType a b =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DtcAppType a b))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DtcAppType a b) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DtcAppType a b) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DtCons s d i =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DtCons s d i))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DtCons s d i) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DtCons s d i) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UConst i T =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.UConst i T))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UConst i T) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UConst i T) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | FunType =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.FunType)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.FunType k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.FunType k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | __eo_List_cons =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.__eo_List_cons)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.__eo_List_cons k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.__eo_List_cons k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DatatypeType s d =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DatatypeType s d))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DatatypeType s d) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DatatypeType s d) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DtSel s d i j =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DtSel s d i j))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DtSel s d i j) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DtSel s d i j) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | USort i =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.USort i))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.USort i) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.USort i) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      all_goals
        change
          __bv_eval_concat
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.concat) _)
                (__eo_list_repeat_rec (Term.UOp UserOp.concat) _ k)) =
            Term.Stuck
        cases hTail :
            __eo_list_repeat_rec (Term.UOp UserOp.concat) _ k <;>
          simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]

private theorem eo_repeat_literal_arg_binary_of_typeof_bitvec
    (x : Term) (i w : native_Int)
    (hi1 : native_zleq 1 i = true) :
    __eo_typeof
        (__bv_eval_concat
          (__eo_list_repeat (Term.UOp UserOp.concat) x
            (Term.Numeral i))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int, ∃ m : native_Int,
      x = Term.Binary wx nx ∧
        native_zleq 0 wx = true ∧
        w = native_zmult i wx ∧
        __bv_eval_concat
            (__eo_list_repeat (Term.UOp UserOp.concat) x
              (Term.Numeral i)) =
          Term.Binary (native_zmult i wx) m ∧
        native_zeq m
          (native_mod_total m
            (native_int_pow2 (native_zmult i wx))) =
          true := by
  intro h
  have hi : (1 : Int) <= i := by
    simpa [native_zleq, SmtEval.native_zleq] using hi1
  have hi0Int : (0 : Int) <= i := by
    omega
  have hi0 : native_zleq 0 i = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hi0Int
  have hiPos : (0 : Int) < i := by
    omega
  have hiNotNeg : native_zlt i 0 = false := by
    simp [native_zlt, SmtEval.native_zlt]
    omega
  have hIntNat :
      native_nat_to_int (native_int_to_nat i) = i := by
    simpa [native_nat_to_int, native_int_to_nat,
      SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
      Int.toNat_of_nonneg hi0Int]
  have hNatNeZero : native_int_to_nat i ≠ 0 := by
    intro hZero
    have hIeq0 : i = 0 := by
      calc
        i = native_nat_to_int (native_int_to_nat i) := hIntNat.symm
        _ = native_nat_to_int 0 := by rw [hZero]
        _ = 0 := by simp [native_nat_to_int, SmtEval.native_nat_to_int]
    have hBad : (0 : Int) < 0 := by
      simpa [hIeq0] using hiPos
    exact (by decide : ¬ (0 : Int) < 0) hBad
  have hList (hxNe : x ≠ Term.Stuck) :
      __eo_list_repeat (Term.UOp UserOp.concat) x (Term.Numeral i) =
        __eo_list_repeat_rec (Term.UOp UserOp.concat) x
          (native_int_to_nat i) := by
    cases x <;> simp [__eo_list_repeat, native_ite, hiNotNeg] at hxNe ⊢
  by_cases hBinary :
      ∃ wx : native_Int, ∃ nx : native_Int, x = Term.Binary wx nx
  · rcases hBinary with ⟨wx, nx, rfl⟩
    cases hWxNonneg : native_zleq 0 wx
    · have hStuck :=
        bv_eval_concat_list_repeat_rec_binary_stuck_of_neg wx nx
          hWxNonneg (native_int_to_nat i) hNatNeZero
      rw [hList (by intro h; cases h), hStuck] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · rcases bv_eval_concat_list_repeat_rec_binary wx nx hWxNonneg
          (native_int_to_nat i) with
        ⟨m, hTerm, _hEval, hCanon⟩
      have hWidth : w = native_zmult i wx := by
        rw [hList (by intro h; cases h), hTerm] at h
        change
          Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral
                (native_zmult
                  (native_nat_to_int (native_int_to_nat i)) wx)) =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
        simp [hIntNat]
      have hRepeatTerm :
          __bv_eval_concat
              (__eo_list_repeat (Term.UOp UserOp.concat)
                (Term.Binary wx nx) (Term.Numeral i)) =
            Term.Binary (native_zmult i wx) m := by
        rw [hList (by intro h; cases h)]
        simpa [hIntNat] using hTerm
      have hCanon' :
          native_zeq m
            (native_mod_total m
              (native_int_pow2 (native_zmult i wx))) =
            true := by
        simpa [hIntNat] using hCanon
      exact ⟨wx, nx, m, rfl, hWxNonneg, hWidth, hRepeatTerm, hCanon'⟩
  · by_cases hxStuck : x = Term.Stuck
    · subst x
      simp [__eo_list_repeat, __bv_eval_concat] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · have hStuck :=
        bv_eval_concat_list_repeat_rec_not_binary_stuck x hBinary
          (native_int_to_nat i) hNatNeZero
      rw [hList hxStuck, hStuck] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h

private theorem eo_concat_args_string_of_typeof_seq
    (x y T : Term) :
    __eo_typeof (__eo_concat x y) =
      Term.Apply (Term.UOp UserOp.Seq) T ->
    ∃ sx : native_String, ∃ sy : native_String,
      x = Term.String sx ∧ y = Term.String sy ∧
        T = Term.UOp UserOp.Char := by
  cases x <;> intro h
  case String sx =>
    cases y <;> simp only [__eo_concat] at h
    case String sy =>
      change
        __eo_typeof (Term.String (native_str_concat sx sy)) =
          Term.Apply (Term.UOp UserOp.Seq) T at h
      change
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
          Term.Apply (Term.UOp UserOp.Seq) T at h
      cases h
      exact ⟨sx, sy, rfl, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.Seq) T at h
      change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_concat] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_mk_binary (native_zplus wx wy)
              (native_binary_concat wx nx wy ny)) =
          Term.Apply (Term.UOp UserOp.Seq) T at h
      cases hWidth : native_zleq 0 (native_zplus wx wy)
      · simp [__eo_mk_binary, hWidth, native_ite] at h
        change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
        cases h
      · simp [__eo_mk_binary, hWidth, native_ite] at h
        change
          Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_zplus wx wy)) =
            Term.Apply (Term.UOp UserOp.Seq) T at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.Seq) T at h
      change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.Seq) T at h
    change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
    cases h

private theorem native_string_valid_of_string_type
    {str : native_String}
    (hTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq SmtType.Char) :
    native_string_valid str = true := by
  change __smtx_typeof (SmtTerm.String str) =
    SmtType.Seq SmtType.Char at hTy
  cases hValid : native_string_valid str <;>
    simp [__smtx_typeof, native_ite, hValid] at hTy ⊢

private theorem smt_string_seq_type_inv
    {str : native_String} {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq T) :
    native_string_valid str = true ∧ T = SmtType.Char := by
  change __smtx_typeof (SmtTerm.String str) = SmtType.Seq T at hTy
  rw [__smtx_typeof.eq_4] at hTy
  cases hValid : native_string_valid str
  · simp [native_ite, hValid] at hTy
  · simp [native_ite, hValid] at hTy
    constructor
    · rfl
    · cases hTy
      rfl

private theorem native_string_valid_reverse_local
    {str : native_String}
    (hValid : native_string_valid str = true) :
    native_string_valid str.reverse = true := by
  rw [native_string_valid, List.all_eq_true] at hValid ⊢
  intro c hc
  exact hValid c (by simpa using List.mem_reverse.mp hc)

private theorem native_string_valid_append_local
    {xs ys : native_String}
    (hxs : native_string_valid xs = true)
    (hys : native_string_valid ys = true) :
    native_string_valid (xs ++ ys) = true := by
  rw [native_string_valid, List.all_eq_true] at hxs hys ⊢
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hxs c hc
  · exact hys c hc

private theorem eo_eq_true_eq_local
    (x y : Term) :
    __eo_eq x y = Term.Boolean true ->
    x = y := by
  intro h
  have hyx : y = x := by
    cases x <;> cases y <;> simp [__eo_eq, native_teq] at h ⊢ <;>
      assumption
  exact hyx.symm

private theorem eo_requires_arg_eq_of_ne_stuck_local
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
      x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

private theorem eo_requires_result_ne_stuck_of_ne_stuck_local
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
      z ≠ Term.Stuck := by
  intro h hz
  have hxy : x = y := eo_requires_arg_eq_of_ne_stuck_local h
  subst y
  subst z
  simp [__eo_requires, native_ite, native_not, native_teq] at h

private theorem eo_typeof_ite_args_of_ne_stuck
    (cTy tTy eTy : Term) :
    __eo_typeof_ite cTy tTy eTy ≠ Term.Stuck ->
      cTy = Term.Bool ∧ tTy = eTy ∧ tTy ≠ Term.Stuck := by
  intro h
  cases cTy <;> cases tTy <;> cases eTy <;>
    simp [__eo_typeof_ite, __eo_requires, __eo_eq, native_ite,
      native_not, native_teq] at h ⊢ <;>
    simp_all

private theorem eo_typeof_ite_bool_same_of_ne_stuck
    (T : Term) :
    T ≠ Term.Stuck ->
      __eo_typeof_ite Term.Bool T T = T := by
  intro hT
  cases T <;>
    simp [__eo_typeof_ite, __eo_requires, __eo_eq, native_ite,
      native_not, native_teq] at hT ⊢

private theorem eo_ite_selected_type_of_typeof
    (c t e T : Term) :
    __eo_typeof (__eo_ite c t e) = T ->
      T ≠ Term.Stuck ->
        ∃ b : Bool, c = Term.Boolean b ∧
          (if b then __eo_typeof t = T else __eo_typeof e = T) := by
  cases c <;> intro h hT <;> simp [__eo_ite, native_ite, native_teq] at h
  case Boolean b =>
    cases b
    · exact ⟨false, rfl, h⟩
    · exact ⟨true, rfl, h⟩
  all_goals
    exfalso
    change Term.Stuck = T at h
    exact hT h.symm

private theorem eo_typeof_str_concat_args_of_seq_char
    (x y : Term)
    (h :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∧
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  change __eo_typeof_str_concat (__eo_typeof x) (__eo_typeof y) =
    Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
  cases hx : __eo_typeof x <;> cases hy : __eo_typeof y <;>
    simp [__eo_typeof_str_concat, hx, hy] at h ⊢
  case Apply f a g b =>
    cases f <;>
      try
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
        cases h
    case UOp op =>
      cases op <;>
        try
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
          cases h
      case Seq =>
        cases g <;>
          try
            change Term.Stuck =
              Term.Apply (Term.UOp UserOp.Seq)
                (Term.UOp UserOp.Char) at h
            cases h
        case UOp op' =>
          cases op' <;>
            try
              change Term.Stuck =
                Term.Apply (Term.UOp UserOp.Seq)
                  (Term.UOp UserOp.Char) at h
              cases h
          case Seq =>
            change
              __eo_requires (__eo_eq a b) (Term.Boolean true)
                  (Term.Apply (Term.UOp UserOp.Seq) a) =
                Term.Apply (Term.UOp UserOp.Seq)
                  (Term.UOp UserOp.Char) at h
            cases hReq :
              native_teq (__eo_eq a b) (Term.Boolean true)
            · simp [__eo_requires, hReq, native_ite] at h
            · have hEqBoolAB : __eo_eq a b = Term.Boolean true := by
                simpa [native_teq] using hReq
              rw [hEqBoolAB] at h
              simp [__eo_requires, native_ite, native_teq, native_not] at h
              cases h
              have hEqBool : __eo_eq (Term.UOp UserOp.Char) b =
                  Term.Boolean true := by
                simpa using hEqBoolAB
              have hB : b = Term.UOp UserOp.Char :=
                (eo_eq_true_eq_local (Term.UOp UserOp.Char) b hEqBool).symm
              constructor
              · simp
              · simp [hB]

private theorem smt_str_concat_args_of_non_none_local
    (x y : Term)
    (hNN :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) ≠
        SmtType.None) :
    ∃ T : SmtType,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ∧
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
            SmtType.Seq T := by
  change
    __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y)) ≠
      SmtType.None at hNN
  cases hx : __smtx_typeof (__eo_to_smt x)
  case Seq T =>
    cases hy : __smtx_typeof (__eo_to_smt y)
    case Seq U =>
      by_cases hTU : T = U
      · subst U
        exact ⟨T, rfl, rfl, by
          rw [show
              __eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) =
                SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y) by
            rfl]
          simp [__smtx_typeof, __smtx_typeof_seq_op_2, hx, hy,
            native_Teq, native_ite]⟩
      · exfalso
        apply hNN
        simp [__smtx_typeof, __smtx_typeof_seq_op_2, hx, hy,
          native_Teq, hTU, native_ite]
    all_goals
      exfalso
      apply hNN
      simp [__smtx_typeof, __smtx_typeof_seq_op_2, hx, hy]
  all_goals
    exfalso
    apply hNN
    simp [__smtx_typeof, __smtx_typeof_seq_op_2, hx]

private theorem native_unpack_pack_seq_local (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, native_unpack_seq,
        native_unpack_pack_seq_local T xs]

private theorem elem_typeof_pack_seq_local (T : SmtType) :
    ∀ xs : List SmtValue,
      __smtx_elem_typeof_seq_value (native_pack_seq T xs) = T
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, __smtx_elem_typeof_seq_value,
        elem_typeof_pack_seq_local T xs]

private theorem smt_value_rel_seq_right_local
    {v : SmtValue} {s : SmtSeq} :
    RuleProofs.smt_value_rel v (SmtValue.Seq s) ->
    ∃ s', v = SmtValue.Seq s' ∧ RuleProofs.smt_seq_rel s' s := by
  intro hRel
  cases v <;>
    simp [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel,
      __smtx_model_eval_eq, native_veq] at hRel ⊢
  case Seq s' =>
    exact hRel

private theorem eo_eq_numeral_zero_true_eq
    (x : Term) :
    __eo_eq x (Term.Numeral 0) = Term.Boolean true ->
    x = Term.Numeral 0 := by
  cases x <;> intro h <;> simp [__eo_eq, native_teq] at h ⊢
  exact h.symm

private theorem eo_ite_guard_cases_of_ne_stuck
    (c x y : Term) :
    __eo_ite c x y ≠ Term.Stuck ->
    c = Term.Boolean true ∨ c = Term.Boolean false := by
  intro h
  by_cases hTrue : native_teq c (Term.Boolean true) = true
  · left
    simpa [native_teq] using hTrue
  · by_cases hFalse : native_teq c (Term.Boolean false) = true
    · right
      simpa [native_teq] using hFalse
    · simp [__eo_ite, hTrue, hFalse, native_ite] at h

private theorem eo_div_total_args_shape_of_typeof_int
    (x y : Term) :
    __eo_ite (__eo_eq y (Term.Numeral 0))
        (Term.Numeral 0) (__eo_zdiv x y) ≠ Term.Stuck ->
    __eo_typeof
        (__eo_ite (__eo_eq y (Term.Numeral 0))
          (Term.Numeral 0) (__eo_zdiv x y)) =
      Term.UOp UserOp.Int ->
    ∃ ny : native_Int, y = Term.Numeral ny ∧
      (ny = 0 ∨
        ∃ nx : native_Int, x = Term.Numeral nx ∧
          native_zeq 0 ny = false) := by
  intro hNe hTy
  rcases eo_ite_guard_cases_of_ne_stuck
      (__eo_eq y (Term.Numeral 0))
      (Term.Numeral 0) (__eo_zdiv x y) hNe with
    hGuard | hGuard
  · have hY : y = Term.Numeral 0 :=
      eo_eq_numeral_zero_true_eq y hGuard
    subst y
    exact ⟨0, rfl, Or.inl rfl⟩
  · have hZDivTy :
        __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int := by
      rw [hGuard] at hTy
      simpa [__eo_ite] using hTy
    rcases eo_zdiv_args_numeral_of_typeof_int x y hZDivTy with
      ⟨nx, ny, hX, hY, hNZ⟩
    exact ⟨ny, hY, Or.inr ⟨nx, hX, hNZ⟩⟩

private theorem eo_mod_total_args_shape_of_typeof_int
    (x y : Term) :
    __eo_ite (__eo_eq y (Term.Numeral 0))
        x (__eo_zmod x y) ≠ Term.Stuck ->
    __eo_typeof
        (__eo_ite (__eo_eq y (Term.Numeral 0))
          x (__eo_zmod x y)) =
      Term.UOp UserOp.Int ->
    ∃ ny : native_Int, y = Term.Numeral ny ∧
      (ny = 0 ∨
        ∃ nx : native_Int, x = Term.Numeral nx ∧
          native_zeq 0 ny = false) := by
  intro hNe hTy
  rcases eo_ite_guard_cases_of_ne_stuck
      (__eo_eq y (Term.Numeral 0))
      x (__eo_zmod x y) hNe with
    hGuard | hGuard
  · have hY : y = Term.Numeral 0 :=
      eo_eq_numeral_zero_true_eq y hGuard
    subst y
    exact ⟨0, rfl, Or.inl rfl⟩
  · have hZModTy :
        __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int := by
      rw [hGuard] at hTy
      simpa [__eo_ite] using hTy
    rcases eo_zmod_args_numeral_of_typeof_int x y hZModTy with
      ⟨nx, ny, hX, hY, hNZ⟩
    exact ⟨ny, hY, Or.inr ⟨nx, hX, hNZ⟩⟩

private theorem eo_typeof_int_pow2_eq_int_arg_eq_int
    (T : Term) :
    __eo_typeof_int_pow2 T = Term.UOp UserOp.Int ->
    T = Term.UOp UserOp.Int := by
  cases T <;> intro h <;> simp [__eo_typeof_int_pow2] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

private theorem eo_int_pow2_result_arg_typeof_int
    (x : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_z x)
          (__eo_ite (__eo_is_neg x) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) x))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) x)) =
      Term.UOp UserOp.Int ->
    __eo_typeof x = Term.UOp UserOp.Int := by
  cases x <;> intro h
  case Numeral n =>
    rfl
  all_goals
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_pow, __eo_mk_apply, native_ite, native_teq, native_not] at h
  all_goals
    first
    | cases h
    | exact eo_typeof_int_pow2_eq_int_arg_eq_int _ h

private theorem eo_int_pow2_eval_numeral_to_smt
    (n : native_Int) :
    __eo_to_smt
        (__eo_ite (__eo_is_z (Term.Numeral n))
          (__eo_ite (__eo_is_neg (Term.Numeral n)) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) (Term.Numeral n)))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) (Term.Numeral n))) =
      SmtTerm.Numeral (native_int_pow2 n) := by
  by_cases hNeg : n < 0
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_int_pow2,
      native_zexp_total, native_zlt, native_and, native_not, hNeg]
    rfl
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_pow, native_ite, native_teq, native_int_pow2,
      native_zexp_total, native_zlt, native_and, native_not, hNeg]
    rfl

private theorem native_int_log_rec_two_eq_nat_log2_go
    (fuel remaining : Nat) :
    native_int_log_rec 2 fuel remaining =
      Nat.rec (motive := fun _ => Nat -> Nat) (fun _ => 0)
        (fun _ ih n => Bool.rec 0 (ih (n.div 2)).succ (Nat.ble 2 n))
        fuel remaining := by
  induction fuel generalizing remaining with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [native_int_log_rec, ih]
      by_cases h : remaining < 2
      · cases hBle : Nat.ble 2 remaining
        · simp [h]
        · have hLe : 2 <= remaining := by
            exact Eq.mp Nat.ble_eq hBle
          exact False.elim ((Nat.not_le.mpr h) hLe)
      · cases hBle : Nat.ble 2 remaining
        · have hLe : 2 <= remaining := Nat.le_of_not_gt h
          have hBleTrue : Nat.ble 2 remaining = true :=
            Eq.mpr Nat.ble_eq hLe
          rw [hBle] at hBleTrue
          cases hBleTrue
        · simp [h]
          rw [Nat.add_comm]
          have hDiv : remaining / 2 = remaining.div 2 := rfl
          rw [hDiv]

private theorem native_int_log_rec_two_eq_nat_log2 (n : Nat) :
    native_int_log_rec 2 n n = Nat.log2 n := by
  unfold Nat.log2
  rw [native_int_log_rec_two_eq_nat_log2_go]

private theorem native_int_log_two_eq_log2 (n : native_Int) :
    native_int_log 2 n = native_int_log2 n := by
  unfold native_int_log native_int_log2
  by_cases h : n.toNat = 0
  · simp [h]
  · simp [h, native_int_log_rec_two_eq_nat_log2]

private theorem eo_typeof_int_ispow2_eq_bool_arg_eq_int
    (T : Term) :
    __eo_typeof_int_ispow2 T = Term.Bool ->
    T = Term.UOp UserOp.Int := by
  cases T <;> intro h <;> simp [__eo_typeof_int_ispow2] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

private theorem eo_int_ispow2_result_arg_typeof_int
    (x : Term) :
    __eo_typeof
        (let isZ := __eo_is_z x
         __eo_ite isZ
          (__eo_ite (__eo_is_neg x) (Term.Boolean false)
            (__eo_eq x
              (__eo_pow (Term.Numeral 2)
                (__eo_ite isZ (__eo_log (Term.Numeral 2) x)
                  (Term.Numeral 0)))))
          (__eo_mk_apply (Term.UOp UserOp.int_ispow2) x)) =
      Term.Bool ->
    __eo_typeof x = Term.UOp UserOp.Int := by
  cases x <;> intro h
  case Numeral n =>
    rfl
  all_goals
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, __eo_pow, __eo_eq, __eo_mk_apply, native_ite,
      native_teq, native_not] at h
  all_goals
    first
    | cases h
    | exact eo_typeof_int_ispow2_eq_bool_arg_eq_int _ h

private theorem int_ispow2_numeral_to_smt_type_bool
    (n : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (let isZ := __eo_is_z (Term.Numeral n)
           __eo_ite isZ
            (__eo_ite (__eo_is_neg (Term.Numeral n)) (Term.Boolean false)
              (__eo_eq (Term.Numeral n)
                (__eo_pow (Term.Numeral 2)
                  (__eo_ite isZ
                    (__eo_log (Term.Numeral 2) (Term.Numeral n))
                    (Term.Numeral 0)))))
            (__eo_mk_apply (Term.UOp UserOp.int_ispow2)
              (Term.Numeral n)))) =
      SmtType.Bool := by
  by_cases hNeg : n < 0
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_and, native_not, native_zlt, hNeg]
    rw [__smtx_typeof.eq_1]
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_eq, __eo_pow, __eo_log, native_ite, native_teq, native_and,
      native_not, native_zlt, hNeg, native_int_log_two_eq_log2,
      eq_comm]
    rw [__smtx_typeof.eq_1]

private theorem int_ispow2_numeral_eval_rel
    (M : SmtModel) (n : native_Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.geq (SmtTerm.Numeral n) (SmtTerm.Numeral 0))
          (SmtTerm.eq (SmtTerm.Numeral n)
            (SmtTerm.int_pow2 (SmtTerm.int_log2 (SmtTerm.Numeral n))))))
      (__smtx_model_eval M
        (__eo_to_smt
          (let isZ := __eo_is_z (Term.Numeral n)
           __eo_ite isZ
            (__eo_ite (__eo_is_neg (Term.Numeral n)) (Term.Boolean false)
              (__eo_eq (Term.Numeral n)
                (__eo_pow (Term.Numeral 2)
                  (__eo_ite isZ
                    (__eo_log (Term.Numeral 2) (Term.Numeral n))
                    (Term.Numeral 0)))))
            (__eo_mk_apply (Term.UOp UserOp.int_ispow2)
              (Term.Numeral n))))) := by
  by_cases hNeg : n < 0
  · have hGeq : native_zleq 0 n = false := by
      unfold native_zleq
      rw [decide_eq_false_iff_not]
      exact Int.not_le.mpr hNeg
    simp [__smtx_model_eval, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_eq, __smtx_model_eval_and,
      __smtx_model_eval_int_pow2, __smtx_model_eval_int_log2,
      __eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_and, native_not,
      native_veq, native_zlt, hNeg, hGeq, RuleProofs.smt_value_rel]
  · have hGeq : native_zleq 0 n = true := by
      unfold native_zleq
      rw [decide_eq_true_eq]
      exact Int.le_of_not_gt hNeg
    simp [__smtx_model_eval, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_eq, __smtx_model_eval_and,
      __smtx_model_eval_int_pow2, __smtx_model_eval_int_log2,
      __eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite, __eo_eq,
      __eo_pow, __eo_log, native_ite, native_teq, native_and, native_not,
      native_veq, native_zlt, hGeq, hNeg, native_int_log_two_eq_log2,
      native_int_pow2, RuleProofs.smt_value_rel, eq_comm]

private theorem eo_abs_arg_numeral_of_typeof_int
    (x : Term) :
    __eo_typeof (__eo_ite (__eo_is_neg x) (__eo_neg x) x) =
      Term.UOp UserOp.Int ->
    ∃ nx : native_Int, x = Term.Numeral nx := by
  cases x <;> intro h
  case Numeral nx =>
    exact ⟨nx, rfl⟩
  case Rational q =>
    cases hNeg : native_qlt q (native_mk_rational 0 1)
    · simp [__eo_is_neg, __eo_ite, hNeg, native_ite,
        native_teq] at h
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
    · simp [__eo_is_neg, __eo_neg, __eo_ite, hNeg, native_ite,
        native_teq] at h
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
  all_goals
    simp [__eo_is_neg, __eo_ite, native_ite, native_teq] at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

private theorem eo_neg_arg_binary_of_typeof_bitvec
    (x : Term) (w : native_Int) :
    __eo_typeof (__eo_neg x) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, x = Term.Binary w nx := by
  cases x <;> intro h
  case Numeral n =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Int =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  case Rational r =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Real =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  case Binary wx nx =>
    simp only [__eo_neg] at h
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
    exact ⟨nx, rfl⟩
  all_goals
    simp only [__eo_neg] at h
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem run_evaluate_sound_apply_not_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.not) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.not) b) := by
  intro hATrans hEvalTy
  have hNotBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) b) :=
    has_bool_type_not_of_has_translation b hATrans
  have hBBool : RuleProofs.eo_has_bool_type b :=
    RuleProofs.eo_has_bool_type_not_arg b hNotBool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hNotEoBool :
      __eo_typeof (Term.Apply (Term.UOp UserOp.not) b) = Term.Bool := by
    change __eo_typeof_not (__eo_typeof b) = Term.Bool
    rw [hBEoBool]
    rfl
  have hRunNotNe : __eo_not (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.not) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.not) b))
          (__eo_not (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_not (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunNotNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.not) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.not) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunNotEoBool : __eo_typeof (__eo_not (__run_evaluate b)) = Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.not) b)
        (__eo_not (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hNotEoBool
  rcases eo_not_arg_boolean_of_typeof_bool
      (__run_evaluate b) hRunNotEoBool with
    ⟨runBool, hRunBool⟩
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunBool]
    rfl
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool := by
    have hBNe : b ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans
    have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
      term_ne_stuck_of_typeof_bool hRunBEoBool
    have hProgEq :=
      eo_prog_evaluate_eq_of_term_and_run_ne_stuck b hBNe hRunBNe
    rw [hProgEq]
    change __eo_typeof_eq (__eo_typeof b) (__eo_typeof (__run_evaluate b)) =
      Term.Bool
    rw [hBEoBool, hRunBEoBool]
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not]
  rcases run_evaluate_rec_apply_arg M (Term.UOp UserOp.not) b rec
      hBTrans hBProgTy with
    ⟨_hSameTy, hRel⟩
  change
    __smtx_typeof (SmtTerm.not (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt (__eo_not (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.not (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt (__eo_not (__run_evaluate b))))
  rw [hRunBool]
  constructor
  · change
      __smtx_typeof (SmtTerm.not (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_not runBool))
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_not_eq]
    rw [hBTy]
    rw [__smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runBool)) := by
      simpa [hRunBool] using hRel
    have hRelNot :=
      smt_value_rel_model_eval_not_of_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (SmtTerm.Boolean runBool)) hRelBool
    simpa [__eo_not, __smtx_model_eval, __smtx_model_eval_not] using hRelNot

private theorem run_evaluate_sound_apply_bvnot_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.bvnot) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.bvnot) b) := by
  intro hATrans hEvalTy
  have hBvNotNN :
      term_has_non_none_type (SmtTerm.bvnot (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_unop_arg_of_non_none
      (op := SmtTerm.bvnot) (t := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_38])
      hBvNotNN with
    ⟨w, hBTy⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvNotEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvnot (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hBEoBv]
    rfl
  have hRunNotNe : __eo_not (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.bvnot) b))
          (__eo_not (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_not (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunNotNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunNotEoBv :
      __eo_typeof (__eo_not (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.bvnot) b)
        (__eo_not (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvNotEoType
  rcases eo_not_arg_binary_of_typeof_bitvec
      (__run_evaluate b) (native_nat_to_int w) hRunNotEoBv with
    ⟨runN, hRunB⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_arg M (Term.UOp UserOp.bvnot) b rec
      hBTrans hBProgTy with
    ⟨_hSameTy, hRel⟩
  change
    __smtx_typeof (SmtTerm.bvnot (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt (__eo_not (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt (__eo_not (__run_evaluate b))))
  rw [hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvnot (__eo_to_smt b)) =
        __smtx_typeof
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_not (native_nat_to_int w) runN)
              (native_int_pow2 (native_nat_to_int w))))
    rw [show
        __smtx_typeof (SmtTerm.bvnot (__eo_to_smt b)) =
          __smtx_typeof_bv_op_1 (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_38]]
    rw [hBTy]
    change SmtType.BitVec w =
      __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int w)
          (native_mod_total
            (native_binary_not (native_nat_to_int w) runN)
            (native_int_pow2 (native_nat_to_int w))))
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runN) := by
      rw [hRunB] at hRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
            SmtTerm.Binary (native_nat_to_int w) runN by
        rfl] at hRel
      rw [__smtx_model_eval.eq_5] at hRel
      exact hRel
    have hEvalB :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runN :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runN hRelValue
    rw [show
        __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt b)) =
          __smtx_model_eval_bvnot
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hEvalB]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary (native_nat_to_int w)
          (native_mod_total
            (native_binary_not (native_nat_to_int w) runN)
            (native_int_pow2 (native_nat_to_int w))))
        (__smtx_model_eval M
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_not (native_nat_to_int w) runN)
              (native_int_pow2 (native_nat_to_int w)))))
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_not (native_nat_to_int w) runN)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_not (native_nat_to_int w) runN)
              (native_int_pow2 (native_nat_to_int w))) by
    rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvneg_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.bvneg) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.bvneg) b) := by
  intro hATrans hEvalTy
  have hBvNegNN :
      term_has_non_none_type (SmtTerm.bvneg (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_unop_arg_of_non_none
      (op := SmtTerm.bvneg) (t := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_46])
      hBvNegNN with
    ⟨w, hBTy⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvNegEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvnot (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hBEoBv]
    rfl
  have hRunNegNe : __eo_neg (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvneg) b))
            (__eo_neg (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.bvneg) b))
          (__eo_neg (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_neg (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunNegNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvneg) b))
            (__eo_neg (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvneg) b))
            (__eo_neg (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunNegEoBv :
      __eo_typeof (__eo_neg (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.bvneg) b)
        (__eo_neg (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvNegEoType
  rcases eo_neg_arg_binary_of_typeof_bitvec
      (__run_evaluate b) (native_nat_to_int w) hRunNegEoBv with
    ⟨runN, hRunB⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_arg M (Term.UOp UserOp.bvneg) b rec
      hBTrans hBProgTy with
    ⟨_hSameTy, hRel⟩
  change
    __smtx_typeof (SmtTerm.bvneg (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt (__eo_neg (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.bvneg (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt (__eo_neg (__run_evaluate b))))
  rw [hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvneg (__eo_to_smt b)) =
        __smtx_typeof
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total (native_zneg runN)
              (native_int_pow2 (native_nat_to_int w))))
    rw [show
        __smtx_typeof (SmtTerm.bvneg (__eo_to_smt b)) =
          __smtx_typeof_bv_op_1 (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_46]]
    rw [hBTy]
    change SmtType.BitVec w =
      __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int w)
          (native_mod_total (native_zneg runN)
            (native_int_pow2 (native_nat_to_int w))))
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runN) := by
      rw [hRunB] at hRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
            SmtTerm.Binary (native_nat_to_int w) runN by
        rfl] at hRel
      rw [__smtx_model_eval.eq_5] at hRel
      exact hRel
    have hEvalB :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runN :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runN hRelValue
    rw [show
        __smtx_model_eval M (SmtTerm.bvneg (__eo_to_smt b)) =
          __smtx_model_eval_bvneg
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_46]]
    rw [hEvalB]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary (native_nat_to_int w)
          (native_mod_total (native_zneg runN)
            (native_int_pow2 (native_nat_to_int w))))
        (__smtx_model_eval M
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total (native_zneg runN)
              (native_int_pow2 (native_nat_to_int w)))))
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total (native_zneg runN)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total (native_zneg runN)
              (native_int_pow2 (native_nat_to_int w))) by
    rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_uneg_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b) := by
  intro hATrans hEvalTy
  have hUnegNN :
      term_has_non_none_type (SmtTerm.uneg (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases arith_unop_arg_of_non_none
      (op := SmtTerm.uneg) (t := __eo_to_smt b)
      (typeof_uneg_eq (__eo_to_smt b)) hUnegNN with hBTyInt | hBTyReal
  · have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
    have hUnegEoType :
        __eo_typeof (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b) =
          Term.UOp UserOp.Int := by
      change __eo_typeof_abs (__eo_typeof b) = Term.UOp UserOp.Int
      rw [hBEoInt]
      simp [__eo_typeof_abs, __eo_requires, __is_arith_type, native_ite,
        native_teq, native_not, SmtEval.native_not]
    have hRunNegNe : __eo_neg (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
            (__eo_neg (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_neg (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunNegNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunNegEoInt :
        __eo_typeof (__eo_neg (__run_evaluate b)) =
          Term.UOp UserOp.Int := by
      have hEq :=
        evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b)
          (__eo_neg (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hUnegEoType
    rcases eo_neg_arg_numeral_of_typeof_int
        (__run_evaluate b) hRunNegEoInt with
      ⟨runN, hRunB⟩
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
      rw [hRunB]
      rfl
    have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
      intro h
      cases h
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hIntTypeNe hBEoInt hRunBEoType
    rcases run_evaluate_rec_apply_arg M
        (Term.UOp UserOp.__eoo_neg_2) b rec hBTrans hBProgTy with
      ⟨_hSameTy, hRel⟩
    change
      __smtx_typeof (SmtTerm.uneg (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt (__eo_neg (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.uneg (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_neg (__run_evaluate b))))
    rw [hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.uneg (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Numeral (native_zneg runN))
      rw [typeof_uneg_eq, hBTyInt]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_arith_overload_op_1]
    · have hRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runN) := by
        rw [hRunB] at hRel
        rw [show __eo_to_smt (Term.Numeral runN) =
            SmtTerm.Numeral runN by
          rfl] at hRel
        rw [__smtx_model_eval.eq_2] at hRel
        exact hRel
      have hEvalB :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runN :=
        smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runN hRelValue
      rw [show
          __smtx_model_eval M (SmtTerm.uneg (__eo_to_smt b)) =
            __smtx_model_eval_uneg
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_23]]
      rw [hEvalB]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral (native_zneg runN))
          (__smtx_model_eval M (SmtTerm.Numeral (native_zneg runN)))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  · have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hBEoReal : __eo_typeof b = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hBMatch.symm.trans hBTyReal)
    have hUnegEoType :
        __eo_typeof (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_abs (__eo_typeof b) = Term.UOp UserOp.Real
      rw [hBEoReal]
      simp [__eo_typeof_abs, __eo_requires, __is_arith_type, native_ite,
        native_teq, native_not, SmtEval.native_not]
    have hRunNegNe : __eo_neg (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
            (__eo_neg (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_neg (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunNegNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunNegEoReal :
        __eo_typeof (__eo_neg (__run_evaluate b)) =
          Term.UOp UserOp.Real := by
      have hEq :=
        evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b)
          (__eo_neg (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hUnegEoType
    rcases eo_neg_arg_rational_of_typeof_real
        (__run_evaluate b) hRunNegEoReal with
      ⟨runQ, hRunB⟩
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Real := by
      rw [hRunB]
      rfl
    have hRealTypeNe : Term.UOp UserOp.Real ≠ Term.Stuck := by
      intro h
      cases h
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hRealTypeNe hBEoReal hRunBEoType
    rcases run_evaluate_rec_apply_arg M
        (Term.UOp UserOp.__eoo_neg_2) b rec hBTrans hBProgTy with
      ⟨_hSameTy, hRel⟩
    change
      __smtx_typeof (SmtTerm.uneg (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt (__eo_neg (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.uneg (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_neg (__run_evaluate b))))
    rw [hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.uneg (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Rational (native_qneg runQ))
      rw [typeof_uneg_eq, hBTyReal]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_arith_overload_op_1]
    · have hRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runQ) := by
        rw [hRunB] at hRel
        rw [show __eo_to_smt (Term.Rational runQ) =
            SmtTerm.Rational runQ by
          rfl] at hRel
        rw [__smtx_model_eval.eq_3] at hRel
        exact hRel
      have hEvalB :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runQ :=
        smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runQ hRelValue
      rw [show
          __smtx_model_eval M (SmtTerm.uneg (__eo_to_smt b)) =
            __smtx_model_eval_uneg
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_23]]
      rw [hEvalB]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Rational (native_qneg runQ))
          (__smtx_model_eval M (SmtTerm.Rational (native_qneg runQ)))
      rw [__smtx_model_eval.eq_3]
      exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_abs_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.abs) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.abs) b) := by
  intro hATrans hEvalTy
  have hAbsNN :
      term_has_non_none_type (SmtTerm.abs (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  have hBTyInt : __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_arg_of_non_none hAbsNN
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hAbsEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.abs) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_abs (__eo_typeof b) = Term.UOp UserOp.Int
    rw [hBEoInt]
    simp [__eo_typeof_abs, __eo_requires, __is_arith_type, native_ite,
      native_teq, native_not, SmtEval.native_not]
  have hRunAbsNe :
      __eo_ite (__eo_is_neg (__run_evaluate b))
          (__eo_neg (__run_evaluate b)) (__run_evaluate b) ≠
        Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.abs) b))
            (__eo_ite (__eo_is_neg (__run_evaluate b))
              (__eo_neg (__run_evaluate b)) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.abs) b))
          (__eo_ite (__eo_is_neg (__run_evaluate b))
            (__eo_neg (__run_evaluate b)) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun :
        __eo_ite (__eo_is_neg (__run_evaluate b))
          (__eo_neg (__run_evaluate b)) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunAbsNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.abs) b))
            (__eo_ite (__eo_is_neg (__run_evaluate b))
              (__eo_neg (__run_evaluate b)) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.abs) b))
            (__eo_ite (__eo_is_neg (__run_evaluate b))
              (__eo_neg (__run_evaluate b)) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunAbsEoInt :
      __eo_typeof
          (__eo_ite (__eo_is_neg (__run_evaluate b))
            (__eo_neg (__run_evaluate b)) (__run_evaluate b)) =
        Term.UOp UserOp.Int := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.abs) b)
        (__eo_ite (__eo_is_neg (__run_evaluate b))
          (__eo_neg (__run_evaluate b)) (__run_evaluate b))
        hEvalEqTy
    exact hEq.symm.trans hAbsEoType
  rcases eo_abs_arg_numeral_of_typeof_int
      (__run_evaluate b) hRunAbsEoInt with
    ⟨runN, hRunB⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
    rw [hRunB]
    rfl
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.abs) b rec hBTrans hBProgTy with
    ⟨_hSameTy, hRel⟩
  change
    __smtx_typeof (SmtTerm.abs (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_ite (__eo_is_neg (__run_evaluate b))
              (__eo_neg (__run_evaluate b)) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.abs (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_ite (__eo_is_neg (__run_evaluate b))
              (__eo_neg (__run_evaluate b)) (__run_evaluate b))))
  rw [hRunB]
  constructor
  · rw [typeof_abs_eq, hBTyInt]
    simp [native_ite, native_Teq]
    cases hNeg : native_zlt runN 0
    · simp [__eo_is_neg, hNeg, native_teq]
      change SmtType.Int = __smtx_typeof (SmtTerm.Numeral runN)
      rw [__smtx_typeof.eq_2]
    · simp [__eo_is_neg, __eo_neg, hNeg, native_teq]
      change
        SmtType.Int =
          __smtx_typeof (SmtTerm.Numeral (native_zneg runN))
      rw [__smtx_typeof.eq_2]
  · have hRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Numeral runN) := by
      rw [hRunB] at hRel
      rw [show __eo_to_smt (Term.Numeral runN) =
          SmtTerm.Numeral runN by
        rfl] at hRel
      rw [__smtx_model_eval.eq_2] at hRel
      exact hRel
    have hEvalB :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Numeral runN :=
      smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt b)) runN hRelValue
    rw [show
        __smtx_model_eval M (SmtTerm.abs (__eo_to_smt b)) =
          __smtx_model_eval_abs
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_22]]
    rw [hEvalB]
    cases hNeg : native_zlt runN 0
    · simp [__smtx_model_eval_abs, __smtx_model_eval_lt,
        __smtx_model_eval_ite, __eo_is_neg, __eo_ite, hNeg,
        native_ite, native_teq, RuleProofs.smt_value_rel,
        __smtx_model_eval_eq, native_veq]
      change
        SmtValue.Numeral runN =
          __smtx_model_eval M (SmtTerm.Numeral runN)
      rw [__smtx_model_eval.eq_2]
    · simp [__smtx_model_eval_abs, __smtx_model_eval_lt,
        __smtx_model_eval_ite, __smtx_model_eval__,
        __eo_is_neg, __eo_neg, __eo_ite, hNeg, native_ite, native_teq,
        RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq,
        native_zplus]
      change
        SmtValue.Numeral (native_zneg runN) =
          __smtx_model_eval M (SmtTerm.Numeral (native_zneg runN))
      rw [__smtx_model_eval.eq_2]

private theorem run_evaluate_sound_apply_int_pow2_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.int_pow2) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.int_pow2) b) := by
  intro hATrans hEvalTy
  have hPowNN :
      term_has_non_none_type (SmtTerm.int_pow2 (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  have hBTyInt : __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_pow2)
      (typeof_int_pow2_eq (__eo_to_smt b)) hPowNN
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hPowEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.int_pow2) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_int_pow2 (__eo_typeof b) = Term.UOp UserOp.Int
    rw [hBEoInt]
    rfl
  let runPow :=
    __eo_ite (__eo_is_z (__run_evaluate b))
      (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
        (__eo_pow (Term.Numeral 2) (__run_evaluate b)))
      (__eo_mk_apply (Term.UOp UserOp.int_pow2) (__run_evaluate b))
  have hRunPowNe : runPow ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_pow2) b))
            runPow) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.int_pow2) b))
          runPow ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runPow <;>
      simp [__eo_mk_apply, hRun] at hMk hRunPowNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_pow2) b))
            runPow) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_pow2) b))
            runPow) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunPowEoInt :
      __eo_typeof runPow = Term.UOp UserOp.Int := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.int_pow2) b)
        runPow hEvalEqTy
    exact hEq.symm.trans hPowEoType
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int :=
    eo_int_pow2_result_arg_typeof_int (__run_evaluate b) hRunPowEoInt
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.int_pow2) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.int_pow2 (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_ite (__eo_is_z (__run_evaluate b))
              (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2) (__run_evaluate b)))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (__run_evaluate b)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.int_pow2 (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_ite (__eo_is_z (__run_evaluate b))
              (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2) (__run_evaluate b)))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (__run_evaluate b)))))
  cases hRun : __run_evaluate b with
  | Numeral runN =>
      constructor
      · rw [eo_int_pow2_eval_numeral_to_smt]
        rw [typeof_int_pow2_eq, hBTyInt]
        rw [__smtx_typeof.eq_2]
        simp [native_ite, native_Teq]
      · have hRelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Numeral runN) := by
          rw [hRun] at hBRel
          rw [show __eo_to_smt (Term.Numeral runN) =
              SmtTerm.Numeral runN by
            rfl] at hBRel
          rw [__smtx_model_eval.eq_2] at hBRel
          exact hBRel
        have hEvalB :
            __smtx_model_eval M (__eo_to_smt b) =
              SmtValue.Numeral runN :=
          smt_value_rel_numeral_eq
            (__smtx_model_eval M (__eo_to_smt b)) runN hRelValue
        rw [show
            __smtx_model_eval M (SmtTerm.int_pow2 (__eo_to_smt b)) =
              __smtx_model_eval_int_pow2
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_28]]
        rw [hEvalB]
        rw [eo_int_pow2_eval_numeral_to_smt]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_int_pow2 runN))
            (__smtx_model_eval M
              (SmtTerm.Numeral (native_int_pow2 runN)))
        rw [__smtx_model_eval.eq_2]
        exact RuleProofs.smt_value_rel_refl _
  | Stuck =>
      rw [hRun] at hRunBEoType
      change Term.Stuck = Term.UOp UserOp.Int at hRunBEoType
      cases hRunBEoType
  | _ =>
      have hRunPowToSmt :
          __eo_to_smt
              (__eo_ite (__eo_is_z (__run_evaluate b))
                (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
                  (__eo_pow (Term.Numeral 2) (__run_evaluate b)))
                (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                  (__run_evaluate b))) =
            SmtTerm.int_pow2 (__eo_to_smt (__run_evaluate b)) := by
        rw [hRun]
        simp [__eo_is_z, __eo_is_z_internal, __eo_ite, __eo_mk_apply,
          native_ite, native_teq, native_and, native_not] <;> rfl
      rw [← hRun]
      constructor
      · rw [hRunPowToSmt]
        rw [typeof_int_pow2_eq, typeof_int_pow2_eq, ← hBSameTy, hBTyInt]
      · rw [hRunPowToSmt]
        rw [__smtx_model_eval.eq_28, __smtx_model_eval.eq_28]
        exact smt_value_rel_model_eval_int_pow2_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (__run_evaluate b))) hBRel

private theorem run_evaluate_sound_apply_int_ispow2_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.int_ispow2) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.int_ispow2) b) := by
  intro hATrans hEvalTy
  let geqTerm :=
    SmtTerm.geq (__eo_to_smt b) (SmtTerm.Numeral 0)
  let eqTerm :=
    SmtTerm.eq (__eo_to_smt b)
      (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt b)))
  have hIspowNN :
      term_has_non_none_type (SmtTerm.and geqTerm eqTerm) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation, geqTerm, eqTerm]
      using hATrans
  have hArgs :
      __smtx_typeof geqTerm = SmtType.Bool ∧
        __smtx_typeof eqTerm = SmtType.Bool :=
    bool_binop_args_bool_of_non_none (op := SmtTerm.and)
      (typeof_and_eq geqTerm eqTerm) hIspowNN
  have hGeqNN : term_has_non_none_type geqTerm := by
    unfold term_has_non_none_type
    rw [hArgs.1]
    simp
  have hGeqArgs :
      (__smtx_typeof (__eo_to_smt b) = SmtType.Int ∧
          __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int) ∨
        (__smtx_typeof (__eo_to_smt b) = SmtType.Real ∧
          __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Real) :=
    arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
      (typeof_geq_eq (__eo_to_smt b) (SmtTerm.Numeral 0)) hGeqNN
  have hBTyInt : __smtx_typeof (__eo_to_smt b) = SmtType.Int := by
    rcases hGeqArgs with hInt | hReal
    · exact hInt.1
    · have hZeroReal := hReal.2
      rw [__smtx_typeof.eq_2] at hZeroReal
      simp at hZeroReal
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hIspowEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.int_ispow2) b) =
        Term.Bool := by
    change __eo_typeof_int_ispow2 (__eo_typeof b) = Term.Bool
    rw [hBEoInt]
    rfl
  let runIspow :=
    let isZ := __eo_is_z (__run_evaluate b)
    __eo_ite isZ
      (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Boolean false)
        (__eo_eq (__run_evaluate b)
          (__eo_pow (Term.Numeral 2)
            (__eo_ite isZ
              (__eo_log (Term.Numeral 2) (__run_evaluate b))
              (Term.Numeral 0)))))
      (__eo_mk_apply (Term.UOp UserOp.int_ispow2) (__run_evaluate b))
  have hRunIspowNe : runIspow ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_ispow2) b))
            runIspow) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.int_ispow2) b))
          runIspow ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runIspow <;>
      simp [__eo_mk_apply, hRun] at hMk hRunIspowNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_ispow2) b))
            runIspow) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_ispow2) b))
            runIspow) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunIspowEoBool :
      __eo_typeof runIspow = Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.int_ispow2) b)
        runIspow hEvalEqTy
    exact hEq.symm.trans hIspowEoType
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int :=
    eo_int_ispow2_result_arg_typeof_int
      (__run_evaluate b) hRunIspowEoBool
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.int_ispow2) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  change
    __smtx_typeof
        (SmtTerm.and
          (SmtTerm.geq (__eo_to_smt b) (SmtTerm.Numeral 0))
          (SmtTerm.eq (__eo_to_smt b)
            (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt b))))) =
        __smtx_typeof (__eo_to_smt runIspow) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.and
            (SmtTerm.geq (__eo_to_smt b) (SmtTerm.Numeral 0))
            (SmtTerm.eq (__eo_to_smt b)
              (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt b))))))
        (__smtx_model_eval M (__eo_to_smt runIspow))
  cases hRun : __run_evaluate b with
  | Numeral runN =>
      constructor
      · calc
          __smtx_typeof
              (SmtTerm.and
                (SmtTerm.geq (__eo_to_smt b) (SmtTerm.Numeral 0))
                (SmtTerm.eq (__eo_to_smt b)
                  (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt b))))) =
              SmtType.Bool :=
            smt_typeof_int_ispow2_formula_eq_bool (__eo_to_smt b) hBTyInt
          _ = __smtx_typeof (__eo_to_smt runIspow) := by
            dsimp [runIspow]
            rw [hRun]
            exact (int_ispow2_numeral_to_smt_type_bool runN).symm
      · have hRelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Numeral runN) := by
          rw [hRun] at hBRel
          rw [show __eo_to_smt (Term.Numeral runN) =
              SmtTerm.Numeral runN by
            rfl] at hBRel
          rw [__smtx_model_eval.eq_2] at hBRel
          exact hBRel
        have hEvalB :
            __smtx_model_eval M (__eo_to_smt b) =
              SmtValue.Numeral runN :=
          smt_value_rel_numeral_eq
            (__smtx_model_eval M (__eo_to_smt b)) runN hRelValue
        dsimp [runIspow]
        rw [hRun]
        simpa [__smtx_model_eval, hEvalB] using
          int_ispow2_numeral_eval_rel M runN
  | Stuck =>
      rw [hRun] at hRunBEoType
      change Term.Stuck = Term.UOp UserOp.Int at hRunBEoType
      cases hRunBEoType
  | _ =>
      have hRunIspowToSmt :
          __eo_to_smt runIspow =
            SmtTerm.and
              (SmtTerm.geq (__eo_to_smt (__run_evaluate b))
                (SmtTerm.Numeral 0))
              (SmtTerm.eq (__eo_to_smt (__run_evaluate b))
                (SmtTerm.int_pow2
                  (SmtTerm.int_log2
                    (__eo_to_smt (__run_evaluate b))))) := by
        dsimp [runIspow]
        rw [hRun]
        simp [__eo_is_z, __eo_is_z_internal, __eo_ite, __eo_mk_apply,
          native_ite, native_teq, native_and, native_not] <;> rfl
      have hRunBTyInt :
          __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Int :=
        hBSameTy.symm.trans hBTyInt
      have hBEvalValueTy :
          __smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt b)) =
            SmtType.Int := by
        simpa [hBTyInt] using
          smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt b) (by
              unfold term_has_non_none_type
              rw [hBTyInt]
              simp)
      rcases int_value_canonical hBEvalValueTy with
        ⟨evalB, hEvalB⟩
      have hRunEval :
          __smtx_model_eval M (__eo_to_smt (__run_evaluate b)) =
            SmtValue.Numeral evalB := by
        have hRelSym :=
          RuleProofs.smt_value_rel_symm _ _ hBRel
        rw [hEvalB] at hRelSym
        exact smt_value_rel_numeral_eq _ evalB hRelSym
      rw [hRunIspowToSmt]
      constructor
      · exact
          (smt_typeof_int_ispow2_formula_eq_bool (__eo_to_smt b) hBTyInt).trans
            (smt_typeof_int_ispow2_formula_eq_bool
              (__eo_to_smt (__run_evaluate b)) hRunBTyInt).symm
      · simp [__smtx_model_eval, hEvalB, hRunEval]
        exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_at_bvsize_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp._at_bvsize) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp._at_bvsize) b) := by
  intro hATrans _hEvalTy
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) b) =
        let _v0 := __smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt b))
        native_ite (native_zleq 0 _v0)
          (SmtTerm._at_purify (SmtTerm.Numeral _v0))
          SmtTerm.None := by
    rfl
  have hApplyNN :
      __smtx_typeof
          (let _v0 := __smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt b))
           native_ite (native_zleq 0 _v0)
             (SmtTerm._at_purify (SmtTerm.Numeral _v0))
             SmtTerm.None) ≠
        SmtType.None := by
    unfold RuleProofs.eo_has_smt_translation at hATrans
    rw [← hTranslate]
    exact hATrans
  have hArgExists :
      ∃ w : native_Nat, __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w := by
    cases hTy : __smtx_typeof (__eo_to_smt b) with
    | BitVec w =>
        exact ⟨w, rfl⟩
    | _ =>
        exfalso
        have hNeg : native_zleq 0 (native_zneg 1) = false := by
          native_decide
        apply hApplyNN
        rw [hTy]
        simp [__smtx_bv_sizeof_type, hNeg, native_ite]
  rcases hArgExists with ⟨w, hBTy⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hRun :
      __run_evaluate (Term.Apply (Term.UOp UserOp._at_bvsize) b) =
        Term.Numeral (native_nat_to_int w) := by
    change __bv_bitwidth (__eo_typeof b) =
      Term.Numeral (native_nat_to_int w)
    rw [hBEoBv]
    rfl
  rw [hRun]
  rw [show
      __eo_to_smt (Term.Numeral (native_nat_to_int w)) =
        SmtTerm.Numeral (native_nat_to_int w) by
    rfl]
  have hWNonneg : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  constructor
  · rw [hTranslate, hBTy]
    simp [__smtx_bv_sizeof_type, __smtx_typeof, native_ite, hWNonneg]
  · rw [hTranslate, hBTy]
    simp [__smtx_bv_sizeof_type, __smtx_model_eval,
      __smtx_model_eval__at_purify, native_ite, hWNonneg]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_zero_extend_core
    (M : SmtModel) (hM : model_total_typed M)
    (n x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp1 UserOp1.zero_extend n) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp1 UserOp1.zero_extend n) x) := by
  intro hATrans hEvalTy
  have hZeroNN :
      term_has_non_none_type
        (SmtTerm.zero_extend (__eo_to_smt n) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases zero_extend_args_of_non_none hZeroNN with
    ⟨i, w, hnSmt, hxSmtTy, hi0⟩
  have hnTerm : n = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
  subst n
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxSmtTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXEoBv :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hXMatch.symm.trans hxSmtTy)
  have hZeroEoType :
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i)) := by
    change
      __eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral i)
          (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i))
    rw [hXEoBv]
    rfl
  let runZero :=
    __eo_to_bin
      (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate x)))
        (Term.Numeral i))
      (__eo_to_z (__run_evaluate x))
  have hRunZeroNe : runZero ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x))
            runZero) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x))
          runZero ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runZero <;>
      simp [__eo_mk_apply, hRun] at hMk hRunZeroNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x))
            runZero) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x))
            runZero) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunZeroEoBv :
      __eo_typeof runZero =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x)
        runZero hEvalEqTy
    exact hEq.symm.trans hZeroEoType
  rcases eo_zero_extend_literal_arg_binary_of_typeof_bitvec
      (__run_evaluate x) i (native_zplus (native_nat_to_int w) i)
      hRunZeroEoBv with
    ⟨runW, runN, hRunX, hWidthEq, hRunZeroEq⟩
  have hRunW : runW = native_nat_to_int w := by
    have hAdd :
        native_nat_to_int w + i = runW + i := by
      simpa [native_zplus, SmtEval.native_zplus] using hWidthEq
    have hAddLeft : i + native_nat_to_int w = i + runW := by
      simpa [Int.add_comm] using hAdd
    exact (Int.add_left_cancel hAddLeft).symm
  subst runW
  have hRunXEoBv :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunX]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof x
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans)
      hBvTypeNe hXEoBv hRunXEoBv
  rcases run_evaluate_rec_apply_arg M
      (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x rec
      hXTrans hXProgTy with
    ⟨_hXSameTy, hXRel⟩
  have hRunZeroEq' :
      runZero =
        Term.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total runN
            (native_int_pow2 (native_zplus (native_nat_to_int w) i))) := by
    simpa [runZero, hRunX] using hRunZeroEq
  have hi : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hwNonneg : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hw : 0 <= native_nat_to_int w := by
    simpa [SmtEval.native_zleq] using hwNonneg
  have hWidthNonneg :
      native_zleq 0 (native_zplus (native_nat_to_int w) i) = true := by
    have hAdd : 0 <= native_nat_to_int w + i := Int.add_nonneg hw hi
    simpa [SmtEval.native_zleq, SmtEval.native_zplus] using hAdd
  have hWidthComm :
      native_zplus i (native_nat_to_int w) =
        native_zplus (native_nat_to_int w) i := by
    simp [SmtEval.native_zplus, Int.add_comm]
  change
    __smtx_typeof
        (SmtTerm.zero_extend (SmtTerm.Numeral i) (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt runZero) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.zero_extend (SmtTerm.Numeral i) (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt runZero))
  rw [hRunZeroEq']
  constructor
  · rw [typeof_zero_extend_eq, hxSmtTy]
    simp [__smtx_typeof_zero_extend, native_ite, hi0]
    change
      SmtType.BitVec
          (native_int_to_nat (native_zplus i (native_nat_to_int w))) =
        __smtx_typeof
          (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total runN
              (native_int_pow2 (native_zplus (native_nat_to_int w) i))))
    rw [smtx_typeof_binary_mod_of_nonneg _ _ hWidthNonneg]
    rw [hWidthComm]
  · have hXRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (SmtValue.Binary (native_nat_to_int w) runN) := by
      rw [hRunX] at hXRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
            SmtTerm.Binary (native_nat_to_int w) runN by
        rfl] at hXRel
      rw [__smtx_model_eval.eq_5] at hXRel
      exact hXRel
    have hXEval :
        __smtx_model_eval M (__eo_to_smt x) =
          SmtValue.Binary (native_nat_to_int w) runN :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt x))
        (native_nat_to_int w) runN hXRelValue
    have hXEvalValueTy :
        __smtx_typeof_value
            (__smtx_model_eval M (__eo_to_smt x)) =
          SmtType.BitVec w := by
      simpa [hxSmtTy] using
        smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt x) (by
            unfold term_has_non_none_type
            rw [hxSmtTy]
            simp)
    have hCanonOrig :
        native_zeq runN
            (native_mod_total runN
              (native_int_pow2 (native_nat_to_int w))) =
          true :=
      bitvec_payload_canonical (by simpa [hXEval] using hXEvalValueTy)
    have hCanonNew :
        native_zeq runN
            (native_mod_total runN
              (native_int_pow2
                (native_zplus (native_nat_to_int w) i))) =
          true := by
      have hCanon :=
        bitvec_payload_canonical_zero_extend
          (i := i) (w := native_nat_to_int w) (n := runN)
          hi0 hwNonneg hCanonOrig
      simpa [hWidthComm] using hCanon
    have hPayloadEq :
        runN =
          native_mod_total runN
            (native_int_pow2 (native_zplus (native_nat_to_int w) i)) := by
      simpa [SmtEval.native_zeq] using hCanonNew
    rw [show
        __smtx_model_eval M
            (SmtTerm.zero_extend (SmtTerm.Numeral i) (__eo_to_smt x)) =
          __smtx_model_eval_zero_extend
            (SmtValue.Numeral i)
            (__smtx_model_eval M (__eo_to_smt x)) by
      rw [__smtx_model_eval.eq_66, __smtx_model_eval.eq_2]]
    rw [hXEval]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary (native_zplus i (native_nat_to_int w)) runN)
        (__smtx_model_eval M
          (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total runN
              (native_int_pow2 (native_zplus (native_nat_to_int w) i)))))
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
              (native_mod_total runN
                (native_int_pow2 (native_zplus (native_nat_to_int w) i)))) =
          SmtValue.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total runN
              (native_int_pow2 (native_zplus (native_nat_to_int w) i))) by
      rw [__smtx_model_eval.eq_5]]
    rw [hWidthComm]
    rw [← hPayloadEq]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_sign_extend_core
    (M : SmtModel) (hM : model_total_typed M)
    (n x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp1 UserOp1.sign_extend n) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp1 UserOp1.sign_extend n) x) := by
  intro hATrans hEvalTy
  have hSignNN :
      term_has_non_none_type
        (SmtTerm.sign_extend (__eo_to_smt n) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases sign_extend_args_of_non_none hSignNN with
    ⟨i, w, hnSmt, hxSmtTy, hi0⟩
  have hnTerm : n = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
  subst n
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxSmtTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXEoBv :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hXMatch.symm.trans hxSmtTy)
  have hSignEoType :
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i)) := by
    change
      __eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral i)
          (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i))
    rw [hXEoBv]
    rfl
  let runSign :=
    eo_eval_sign_extend_rhs (__run_evaluate x) (Term.Numeral i)
  have hRunSignNe : runSign ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x))
            runSign) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x))
          runSign ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runSign <;>
      simp [__eo_mk_apply, hRun] at hMk hRunSignNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x))
            runSign) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x))
            runSign) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunSignEoBv :
      __eo_typeof runSign =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x)
        runSign hEvalEqTy
    exact hEq.symm.trans hSignEoType
  rcases eo_eval_sign_extend_rhs_binary_of_typeof_bitvec
      (__run_evaluate x) i (native_zplus (native_nat_to_int w) i)
      hRunSignEoBv with
    ⟨runW, runN, hRunX, hWidthEq⟩
  have hRunW : runW = native_nat_to_int w := by
    have hAdd :
        native_nat_to_int w + i = runW + i := by
      simpa [native_zplus, SmtEval.native_zplus] using hWidthEq
    have hAddLeft : i + native_nat_to_int w = i + runW := by
      simpa [Int.add_comm] using hAdd
    exact (Int.add_left_cancel hAddLeft).symm
  subst runW
  have hRunXEoBv :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunX]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof x
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans)
      hBvTypeNe hXEoBv hRunXEoBv
  rcases run_evaluate_rec_apply_arg M
      (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x rec
      hXTrans hXProgTy with
    ⟨_hXSameTy, hXRel⟩
  have hi : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hwNonneg : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hw : 0 <= native_nat_to_int w := by
    simpa [SmtEval.native_zleq] using hwNonneg
  have hWidthNonneg :
      native_zleq 0 (native_zplus (native_nat_to_int w) i) = true := by
    have hAdd : 0 <= native_nat_to_int w + i := Int.add_nonneg hw hi
    simpa [SmtEval.native_zleq, SmtEval.native_zplus] using hAdd
  have hWidthComm :
      native_zplus i (native_nat_to_int w) =
        native_zplus (native_nat_to_int w) i := by
    simp [SmtEval.native_zplus, Int.add_comm]
  have hXRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt x))
        (SmtValue.Binary (native_nat_to_int w) runN) := by
    rw [hRunX] at hXRel
    rw [show
        __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
          SmtTerm.Binary (native_nat_to_int w) runN by
      rfl] at hXRel
    rw [__smtx_model_eval.eq_5] at hXRel
    exact hXRel
  have hXEval :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) runN :=
    smt_value_rel_binary_eq
      (__smtx_model_eval M (__eo_to_smt x))
      (native_nat_to_int w) runN hXRelValue
  have hXEvalValueTy :
      __smtx_typeof_value
          (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec w := by
    simpa [hxSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt x) (by
          unfold term_has_non_none_type
          rw [hxSmtTy]
          simp)
  have hCanonOrig :
      native_zeq runN
          (native_mod_total runN
            (native_int_pow2 (native_nat_to_int w))) =
        true :=
    bitvec_payload_canonical (by simpa [hXEval] using hXEvalValueTy)
  have hPayloadEq :
      eo_sign_extend_payload (native_nat_to_int w) runN =
        native_binary_uts (native_nat_to_int w) runN :=
    eo_sign_extend_payload_eq_uts hwNonneg hCanonOrig
  have hRunSignToBin :
      runSign =
        __eo_to_bin
          (Term.Numeral (native_zplus (native_nat_to_int w) i))
          (Term.Numeral
            (eo_sign_extend_payload (native_nat_to_int w) runN)) := by
    simpa [runSign, hRunX] using
      eo_eval_sign_extend_rhs_binary_to_bin
        (native_nat_to_int w) runN i
  have hRunSignToBinTy :
      __eo_typeof
          (__eo_to_bin
            (Term.Numeral (native_zplus (native_nat_to_int w) i))
            (Term.Numeral
              (eo_sign_extend_payload (native_nat_to_int w) runN))) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i)) := by
    rw [← hRunSignToBin]
    exact hRunSignEoBv
  have hRunSignEq' :
      runSign =
        Term.Binary (native_zplus (native_nat_to_int w) i)
          (native_mod_total
            (native_binary_uts (native_nat_to_int w) runN)
            (native_int_pow2
              (native_zplus (native_nat_to_int w) i))) := by
    have hToBin :=
      eo_to_bin_numeral_eq_of_typeof_bitvec
        (eo_sign_extend_payload (native_nat_to_int w) runN)
        (native_zplus (native_nat_to_int w) i)
        (native_zplus (native_nat_to_int w) i)
        hRunSignToBinTy
    rw [hRunSignToBin]
    rw [hToBin]
    rw [hPayloadEq]
  change
    __smtx_typeof
        (SmtTerm.sign_extend (SmtTerm.Numeral i) (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt runSign) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.sign_extend (SmtTerm.Numeral i) (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt runSign))
  rw [hRunSignEq']
  constructor
  · rw [typeof_sign_extend_eq, hxSmtTy]
    simp [__smtx_typeof_sign_extend, native_ite, hi0]
    change
      SmtType.BitVec
          (native_int_to_nat (native_zplus i (native_nat_to_int w))) =
        __smtx_typeof
          (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total
              (native_binary_uts (native_nat_to_int w) runN)
              (native_int_pow2
                (native_zplus (native_nat_to_int w) i))))
    rw [smtx_typeof_binary_mod_of_nonneg _ _ hWidthNonneg]
    rw [hWidthComm]
  · rw [show
        __smtx_model_eval M
            (SmtTerm.sign_extend (SmtTerm.Numeral i) (__eo_to_smt x)) =
          __smtx_model_eval_sign_extend
            (SmtValue.Numeral i)
            (__smtx_model_eval M (__eo_to_smt x)) by
      rw [__smtx_model_eval.eq_67, __smtx_model_eval.eq_2]]
    rw [hXEval]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary (native_zplus i (native_nat_to_int w))
          (native_mod_total
            (native_binary_uts (native_nat_to_int w) runN)
            (native_int_pow2
              (native_zplus i (native_nat_to_int w)))))
        (__smtx_model_eval M
          (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total
              (native_binary_uts (native_nat_to_int w) runN)
              (native_int_pow2
                (native_zplus (native_nat_to_int w) i)))))
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
              (native_mod_total
                (native_binary_uts (native_nat_to_int w) runN)
                (native_int_pow2
                  (native_zplus (native_nat_to_int w) i)))) =
          SmtValue.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total
              (native_binary_uts (native_nat_to_int w) runN)
              (native_int_pow2
                (native_zplus (native_nat_to_int w) i))) by
      rw [__smtx_model_eval.eq_5]]
    rw [hWidthComm]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_repeat_core
    (M : SmtModel) (hM : model_total_typed M)
    (n x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp1 UserOp1.repeat n) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp1 UserOp1.repeat n) x) := by
  intro hATrans hEvalTy
  have hRepeatNN :
      term_has_non_none_type
        (SmtTerm.repeat (__eo_to_smt n) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases repeat_args_of_non_none hRepeatNN with
    ⟨i, w, hnSmt, hxSmtTy, hi1⟩
  have hnTerm : n = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
  subst n
  have hi : (1 : Int) <= i := by
    simpa [native_zleq, SmtEval.native_zleq] using hi1
  have hi0Int : (0 : Int) <= i := by
    omega
  have hi0 : native_zleq 0 i = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hi0Int
  have hiNotNeg : native_zlt i 0 = false := by
    simp [native_zlt, SmtEval.native_zlt]
    omega
  have hIntNat :
      native_nat_to_int (native_int_to_nat i) = i := by
    simpa [native_nat_to_int, native_int_to_nat,
      SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
      Int.toNat_of_nonneg hi0Int]
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxSmtTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXEoBv :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hXMatch.symm.trans hxSmtTy)
  have hRepeatEoType :
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zmult i (native_nat_to_int w))) := by
    change
      __eo_typeof_repeat (Term.UOp UserOp.Int) (Term.Numeral i)
          (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zmult i (native_nat_to_int w)))
    rw [hXEoBv]
    rfl
  let runRepeat :=
    __bv_eval_concat
      (__eo_list_repeat (Term.UOp UserOp.concat)
        (__run_evaluate x) (Term.Numeral i))
  have hRunRepeatEq :
      __run_evaluate
          (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x) =
        runRepeat := by
    dsimp [runRepeat]
    simp [__run_evaluate, __eo_is_z, __eo_is_z_internal,
      __eo_is_neg, __eo_not, __eo_and, __eo_ite, native_ite,
      native_teq, native_and, native_not, SmtEval.native_not, hiNotNeg]
  have hRunRepeatNe : runRepeat ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))
            (__run_evaluate
              (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))) =
        Term.Bool at hEvalTy
    rw [hRunRepeatEq, hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))
          runRepeat ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runRepeat <;>
      simp [__eo_mk_apply, hRun] at hMk hRunRepeatNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))
            runRepeat) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))
            (__run_evaluate
              (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))) =
        Term.Bool at hEvalTy
    rw [hRunRepeatEq] at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunRepeatEoBv :
      __eo_typeof runRepeat =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zmult i (native_nat_to_int w))) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x)
        runRepeat hEvalEqTy
    exact hEq.symm.trans hRepeatEoType
  dsimp [runRepeat] at hRunRepeatEoBv
  rcases eo_repeat_literal_arg_binary_of_typeof_bitvec
      (__run_evaluate x) i (native_zmult i (native_nat_to_int w))
      hi1 hRunRepeatEoBv with
    ⟨runW, runN, repM, hRunX, hRunWNonneg, hWidthEq,
      hRunRepeatTerm, hRepCanon⟩
  have hRunW : runW = native_nat_to_int w := by
    have hMul :
        i * native_nat_to_int w = i * runW := by
      simpa [native_zmult, SmtEval.native_zmult] using hWidthEq
    have hiNe : i ≠ 0 := by
      intro hiZero
      have hBad : (1 : Int) <= 0 := by
        simpa [hiZero] using hi
      exact (by decide : ¬ (1 : Int) <= 0) hBad
    have hEq : native_nat_to_int w = runW :=
      (Int.mul_eq_mul_left_iff hiNe).mp hMul
    exact hEq.symm
  subst runW
  have hRunXEoBv :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunX]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof x
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans)
      hBvTypeNe hXEoBv hRunXEoBv
  rcases run_evaluate_rec_apply_arg M
      (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x rec
      hXTrans hXProgTy with
    ⟨_hXSameTy, hXRel⟩
  have hXRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt x))
        (SmtValue.Binary (native_nat_to_int w) runN) := by
    rw [hRunX] at hXRel
    rw [show
        __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
          SmtTerm.Binary (native_nat_to_int w) runN by
      rfl] at hXRel
    rw [__smtx_model_eval.eq_5] at hXRel
    exact hXRel
  have hXEval :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) runN :=
    smt_value_rel_binary_eq
      (__smtx_model_eval M (__eo_to_smt x))
      (native_nat_to_int w) runN hXRelValue
  have hWidthNonneg :
      native_zleq 0 (native_zmult i (native_nat_to_int w)) = true := by
    have hw : 0 <= native_nat_to_int w := by
      simp [SmtEval.native_nat_to_int]
    have hMul : 0 <= i * native_nat_to_int w :=
      Int.mul_nonneg hi0Int hw
    simpa [native_zleq, SmtEval.native_zleq, native_zmult,
      SmtEval.native_zmult] using hMul
  have hListRun :
      __eo_list_repeat (Term.UOp UserOp.concat)
          (Term.Binary (native_nat_to_int w) runN) (Term.Numeral i) =
        __eo_list_repeat_rec (Term.UOp UserOp.concat)
          (Term.Binary (native_nat_to_int w) runN)
          (native_int_to_nat i) := by
    simp [__eo_list_repeat, native_ite, hiNotNeg]
  rcases bv_eval_concat_list_repeat_rec_binary
      (native_nat_to_int w) runN hRunWNonneg (native_int_to_nat i) with
    ⟨repM', hRepeatTerm', hRepeatEvalRec, _hRepCanon'⟩
  have hRunRepeatTerm' :
      __bv_eval_concat
          (__eo_list_repeat (Term.UOp UserOp.concat)
            (__run_evaluate x) (Term.Numeral i)) =
        Term.Binary (native_zmult i (native_nat_to_int w)) repM' := by
    rw [hRunX, hListRun]
    simpa [hIntNat] using hRepeatTerm'
  have hRepMEq : repM' = repM := by
    rw [hRunRepeatTerm'] at hRunRepeatTerm
    cases hRunRepeatTerm
    rfl
  have hRepeatEvalRec' :
      __smtx_model_eval_repeat_rec (native_int_to_nat i)
          (SmtValue.Binary (native_nat_to_int w) runN) =
        SmtValue.Binary (native_zmult i (native_nat_to_int w)) repM := by
    rw [hRepeatEvalRec, hRepMEq]
    simp [hIntNat]
  rw [hRunRepeatEq]
  change
    __smtx_typeof
        (SmtTerm.repeat (SmtTerm.Numeral i) (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt runRepeat) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.repeat (SmtTerm.Numeral i) (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt runRepeat))
  rw [show
      runRepeat =
        Term.Binary (native_zmult i (native_nat_to_int w)) repM by
    dsimp [runRepeat]
    exact hRunRepeatTerm]
  constructor
  · rw [typeof_repeat_eq, hxSmtTy]
    simp [__smtx_typeof_repeat, native_ite, hi1]
    change
      SmtType.BitVec
          (native_int_to_nat (native_zmult i (native_nat_to_int w))) =
        __smtx_typeof
          (SmtTerm.Binary (native_zmult i (native_nat_to_int w)) repM)
    rw [smtx_typeof_binary_of_nonneg_and_canonical
      (native_zmult i (native_nat_to_int w)) repM
      hWidthNonneg hRepCanon]
  · rw [show
        __smtx_model_eval M
            (SmtTerm.repeat (SmtTerm.Numeral i) (__eo_to_smt x)) =
          __smtx_model_eval_repeat
            (SmtValue.Numeral i)
            (__smtx_model_eval M (__eo_to_smt x)) by
      rw [__smtx_model_eval.eq_37, __smtx_model_eval.eq_2]]
    rw [hXEval]
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval_repeat_rec (native_int_to_nat i)
          (SmtValue.Binary (native_nat_to_int w) runN))
        (__smtx_model_eval M
          (SmtTerm.Binary (native_zmult i (native_nat_to_int w)) repM))
    rw [hRepeatEvalRec']
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_zmult i (native_nat_to_int w)) repM) =
          SmtValue.Binary (native_zmult i (native_nat_to_int w)) repM by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvand_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b) := by
  intro hATrans hEvalTy
  have hBvAndNN :
      term_has_non_none_type
        (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvand) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_39]) hBvAndNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvAndEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunAndNe :
      __eo_and (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
          (__eo_and (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_and (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunAndNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunAndEoBv :
      __eo_typeof (__eo_and (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b)
        (__eo_and (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvAndEoType
  rcases eo_and_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunAndEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvand) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvand) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_and
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_and
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_and, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_39]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvand
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvand
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_and
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_and, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_and (native_nat_to_int w) runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvor_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b) := by
  intro hATrans hEvalTy
  have hBvOrNN :
      term_has_non_none_type
        (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvor) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_40]) hBvOrNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvOrEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunOrNe :
      __eo_or (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
          (__eo_or (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_or (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunOrNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunOrEoBv :
      __eo_typeof (__eo_or (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b)
        (__eo_or (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvOrEoType
  rcases eo_or_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunOrEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvor) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvor) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_or
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_or
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_or, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_40]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvor
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvor
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_or
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_or, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_or (native_nat_to_int w) runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvxor_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b) := by
  intro hATrans hEvalTy
  have hBvXorNN :
      term_has_non_none_type
        (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvxor) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_43]) hBvXorNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvXorEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunXorNe :
      __eo_xor (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
          (__eo_xor (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_xor (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunXorNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunXorEoBv :
      __eo_typeof (__eo_xor (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b)
        (__eo_xor (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvXorEoType
  rcases eo_xor_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunXorEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvxor) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvxor) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_xor
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_xor
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_xor, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_43]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvxor
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvxor
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_xor
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_xor, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_xor (native_nat_to_int w) runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvadd_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b) := by
  intro hATrans hEvalTy
  have hBvAddNN :
      term_has_non_none_type
        (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvadd) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_47]) hBvAddNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvAddEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunAddNe :
      __eo_add (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
          (__eo_add (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_add (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunAddNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunAddEoBv :
      __eo_typeof (__eo_add (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b)
        (__eo_add (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvAddEoType
  rcases eo_add_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunAddEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvadd) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvadd) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_47]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_47]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvadd
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_zplus runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvmul_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b) := by
  intro hATrans hEvalTy
  have hBvMulNN :
      term_has_non_none_type
        (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvmul) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_48]) hBvMulNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvMulEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunMulNe :
      __eo_mul (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
          (__eo_mul (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_mul (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunMulNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunMulEoBv :
      __eo_typeof (__eo_mul (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b)
        (__eo_mul (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvMulEoType
  rcases eo_mul_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunMulEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvmul) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvmul) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_mul
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_mul
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_mul, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_48]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvmul
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_48]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvmul
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_mul
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_mul, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_zmult runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvsub_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b) := by
  intro hATrans hEvalTy
  have hBvSubNN :
      term_has_non_none_type
        (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvsub) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_51]) hBvSubNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvSubEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunSubNe :
      __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
          (__eo_add (__run_evaluate a)
            (__eo_neg (__run_evaluate b))) ≠
        Term.Stuck := by
    intro hMk
    cases hRun :
        __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunSubNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunSubEoBv :
      __eo_typeof
          (__eo_add (__run_evaluate a)
            (__eo_neg (__run_evaluate b))) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b)
        (__eo_add (__run_evaluate a)
          (__eo_neg (__run_evaluate b))) hEvalEqTy
    exact hEq.symm.trans hBvSubEoType
  rcases eo_add_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__eo_neg (__run_evaluate b))
      (native_nat_to_int w) hRunSubEoBv with
    ⟨runA, runNegB, hRunA, hRunNegB⟩
  rcases eo_neg_arg_binary_of_eq_binary
      (__run_evaluate b) (native_nat_to_int w) runNegB hRunNegB with
    ⟨runB, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvsub) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvsub) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (__eo_neg (Term.Binary (native_nat_to_int w) runB))))
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (__eo_neg (Term.Binary (native_nat_to_int w) runB))) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_neg, __eo_requires, native_ite, native_teq,
        native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_51]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvsub
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_51]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvsub
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (__eo_neg (Term.Binary (native_nat_to_int w) runB))) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_neg, __eo_requires, native_ite, native_teq,
        native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_zplus runA
                  (native_mod_total (native_zneg runB)
                    (native_int_pow2 (native_nat_to_int w))))
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_plus_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) := by
  intro hATrans hEvalTy
  have hPlusNN :
      term_has_non_none_type
        (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases arith_binop_args_of_non_none
      (op := SmtTerm.plus) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (typeof_plus_eq (__eo_to_smt a) (__eo_to_smt b)) hPlusNN with
    hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
    have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
    have hPlusEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) =
          Term.UOp UserOp.Int := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Int
      rw [hAEoInt, hBEoInt]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunAddNe :
        __eo_add (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_add (__run_evaluate a) (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunAddNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunAddEoInt :
        __eo_typeof (__eo_add (__run_evaluate a) (__run_evaluate b)) =
          Term.UOp UserOp.Int := by
      have hEq :=
        evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b)
          (__eo_add (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hPlusEoType
    rcases eo_add_args_numeral_of_typeof_int
        (__run_evaluate a) (__run_evaluate b) hRunAddEoInt with
      ⟨runA, runB, hRunA, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
      rw [hRunB]
      rfl
    have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hIntTypeNe hAEoInt hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hIntTypeNe hBEoInt hRunBEoType
    rcases run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.plus) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.plus) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Numeral (native_zplus runA runB))
      rw [typeof_plus_eq, hATyInt, hBTyInt]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_plus
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_12]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral (native_zplus runA runB))
          (__smtx_model_eval M
            (SmtTerm.Numeral (native_zplus runA runB)))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoReal : __eo_typeof a = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hAMatch.symm.trans hATyReal)
    have hBEoReal : __eo_typeof b = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hBMatch.symm.trans hBTyReal)
    have hPlusEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Real
      rw [hAEoReal, hBEoReal]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunAddNe :
        __eo_add (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_add (__run_evaluate a) (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunAddNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunAddEoReal :
        __eo_typeof (__eo_add (__run_evaluate a) (__run_evaluate b)) =
          Term.UOp UserOp.Real := by
      have hEq :=
        evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b)
          (__eo_add (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hPlusEoType
    rcases eo_add_args_rational_of_typeof_real
        (__run_evaluate a) (__run_evaluate b) hRunAddEoReal with
      ⟨runA, runB, hRunA, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Real := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Real := by
      rw [hRunB]
      rfl
    have hRealTypeNe : Term.UOp UserOp.Real ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hRealTypeNe hAEoReal hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hRealTypeNe hBEoReal hRunBEoType
    rcases run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.plus) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.plus) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Rational (native_qplus runA runB))
      rw [typeof_plus_eq, hATyReal, hBTyReal]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_plus
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_12]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Rational (native_qplus runA runB))
          (__smtx_model_eval M
            (SmtTerm.Rational (native_qplus runA runB)))
      rw [__smtx_model_eval.eq_3]
      exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_mult_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) := by
  intro hATrans hEvalTy
  have hMultNN :
      term_has_non_none_type
        (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases arith_binop_args_of_non_none
      (op := SmtTerm.mult) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (typeof_mult_eq (__eo_to_smt a) (__eo_to_smt b)) hMultNN with
    hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
    have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
    have hMultEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) =
          Term.UOp UserOp.Int := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Int
      rw [hAEoInt, hBEoInt]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunMulNe :
        __eo_mul (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_mul (__run_evaluate a) (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunMulNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunMulEoInt :
        __eo_typeof (__eo_mul (__run_evaluate a) (__run_evaluate b)) =
          Term.UOp UserOp.Int := by
      have hEq :=
        evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b)
          (__eo_mul (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hMultEoType
    rcases eo_mul_args_numeral_of_typeof_int
        (__run_evaluate a) (__run_evaluate b) hRunMulEoInt with
      ⟨runA, runB, hRunA, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
      rw [hRunB]
      rfl
    have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hIntTypeNe hAEoInt hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hIntTypeNe hBEoInt hRunBEoType
    rcases run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.mult) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.mult) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Numeral (native_zmult runA runB))
      rw [typeof_mult_eq, hATyInt, hBTyInt]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_mult
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_14]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral (native_zmult runA runB))
          (__smtx_model_eval M
            (SmtTerm.Numeral (native_zmult runA runB)))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoReal : __eo_typeof a = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hAMatch.symm.trans hATyReal)
    have hBEoReal : __eo_typeof b = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hBMatch.symm.trans hBTyReal)
    have hMultEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Real
      rw [hAEoReal, hBEoReal]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunMulNe :
        __eo_mul (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_mul (__run_evaluate a) (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunMulNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunMulEoReal :
        __eo_typeof (__eo_mul (__run_evaluate a) (__run_evaluate b)) =
          Term.UOp UserOp.Real := by
      have hEq :=
        evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b)
          (__eo_mul (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hMultEoType
    rcases eo_mul_args_rational_of_typeof_real
        (__run_evaluate a) (__run_evaluate b) hRunMulEoReal with
      ⟨runA, runB, hRunA, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Real := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Real := by
      rw [hRunB]
      rfl
    have hRealTypeNe : Term.UOp UserOp.Real ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hRealTypeNe hAEoReal hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hRealTypeNe hBEoReal hRunBEoType
    rcases run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.mult) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.mult) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Rational (native_qmult runA runB))
      rw [typeof_mult_eq, hATyReal, hBTyReal]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_mult
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_14]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Rational (native_qmult runA runB))
          (__smtx_model_eval M
            (SmtTerm.Rational (native_qmult runA runB)))
      rw [__smtx_model_eval.eq_3]
      exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_neg_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) := by
  intro hATrans hEvalTy
  have hNegNN :
      term_has_non_none_type
        (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases arith_binop_args_of_non_none
      (op := SmtTerm.neg) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (typeof_neg_eq (__eo_to_smt a) (__eo_to_smt b)) hNegNN with
    hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
    have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
    have hNegEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) =
          Term.UOp UserOp.Int := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Int
      rw [hAEoInt, hBEoInt]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunSubNe :
        __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b))) ≠
          Term.Stuck := by
      intro hMk
      cases hRun :
          __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunSubNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool at hEvalTy
      rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunSubEoInt :
        __eo_typeof
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b))) =
          Term.UOp UserOp.Int := by
      have hEq :=
        evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b)
          (__eo_add (__run_evaluate a)
            (__eo_neg (__run_evaluate b))) hEvalEqTy
      exact hEq.symm.trans hNegEoType
    rcases eo_add_args_numeral_of_typeof_int
        (__run_evaluate a) (__eo_neg (__run_evaluate b)) hRunSubEoInt with
      ⟨runA, runNegB, hRunA, hRunNegB⟩
    have hRunNegBEoInt :
        __eo_typeof (__eo_neg (__run_evaluate b)) =
          Term.UOp UserOp.Int := by
      rw [hRunNegB]
      rfl
    rcases eo_neg_arg_numeral_of_typeof_int
        (__run_evaluate b) hRunNegBEoInt with
      ⟨runB, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
      rw [hRunB]
      rfl
    have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hIntTypeNe hAEoInt hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hIntTypeNe hBEoInt hRunBEoType
    rcases run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.neg) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.neg) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (SmtTerm.Numeral (native_zplus runA (native_zneg runB)))
      rw [typeof_neg_eq, hATyInt, hBTyInt]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval__
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_13]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral (native_zplus runA (native_zneg runB)))
          (__smtx_model_eval M
            (SmtTerm.Numeral (native_zplus runA (native_zneg runB))))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoReal : __eo_typeof a = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hAMatch.symm.trans hATyReal)
    have hBEoReal : __eo_typeof b = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hBMatch.symm.trans hBTyReal)
    have hNegEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Real
      rw [hAEoReal, hBEoReal]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunSubNe :
        __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b))) ≠
          Term.Stuck := by
      intro hMk
      cases hRun :
          __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunSubNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool at hEvalTy
      rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunSubEoReal :
        __eo_typeof
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b))) =
          Term.UOp UserOp.Real := by
      have hEq :=
        evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b)
          (__eo_add (__run_evaluate a)
            (__eo_neg (__run_evaluate b))) hEvalEqTy
      exact hEq.symm.trans hNegEoType
    rcases eo_add_args_rational_of_typeof_real
        (__run_evaluate a) (__eo_neg (__run_evaluate b))
        hRunSubEoReal with
      ⟨runA, runNegB, hRunA, hRunNegB⟩
    have hRunNegBEoReal :
        __eo_typeof (__eo_neg (__run_evaluate b)) =
          Term.UOp UserOp.Real := by
      rw [hRunNegB]
      rfl
    rcases eo_neg_arg_rational_of_typeof_real
        (__run_evaluate b) hRunNegBEoReal with
      ⟨runB, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Real := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Real := by
      rw [hRunB]
      rfl
    have hRealTypeNe : Term.UOp UserOp.Real ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hRealTypeNe hAEoReal hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hRealTypeNe hBEoReal hRunBEoType
    rcases run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.neg) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.neg) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (SmtTerm.Rational (native_qplus runA (native_qneg runB)))
      rw [typeof_neg_eq, hATyReal, hBTyReal]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval__
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_13]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Rational (native_qplus runA (native_qneg runB)))
          (__smtx_model_eval M
            (SmtTerm.Rational (native_qplus runA (native_qneg runB))))
      rw [__smtx_model_eval.eq_3]
      exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_div_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b) := by
  intro hATrans hEvalTy
  have hDivNN :
      term_has_non_none_type
        (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases int_binop_args_of_non_none
      (op := SmtTerm.div) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (R := SmtType.Int)
      (typeof_div_eq (__eo_to_smt a) (__eo_to_smt b)) hDivNN with
    ⟨hATyInt, hBTyInt⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyInt]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hDivEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_div (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int
    rw [hAEoInt, hBEoInt]
    rfl
  have hRunDivNe :
      __eo_zdiv (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
            (__eo_zdiv (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
          (__eo_zdiv (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_zdiv (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunDivNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
            (__eo_zdiv (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
            (__eo_zdiv (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunDivEoInt :
      __eo_typeof (__eo_zdiv (__run_evaluate a) (__run_evaluate b)) =
        Term.UOp UserOp.Int := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b)
        (__eo_zdiv (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hDivEoType
  rcases eo_zdiv_args_numeral_of_typeof_int
      (__run_evaluate a) (__run_evaluate b) hRunDivEoInt with
    ⟨runA, runB, hRunA, hRunB, hNZ⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
    rw [hRunB]
    rfl
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
    rw [hRunA]
    rfl
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hIntTypeNe hAEoInt hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.div) a b rec hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.div) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  have hRunBNe : runB ≠ 0 := by
    intro hZero
    subst runB
    simp [native_zeq] at hNZ
  change
    __smtx_typeof (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_zdiv (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_zdiv (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · rw [show
        __eo_to_smt
            (__eo_zdiv (Term.Numeral runA) (Term.Numeral runB)) =
          SmtTerm.Numeral (native_div_total runA runB) by
      simp [__eo_zdiv, hNZ, native_ite]
      rfl]
    change
      __smtx_typeof (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Numeral (native_div_total runA runB))
    rw [typeof_div_eq, hATyInt, hBTyInt]
    rw [__smtx_typeof.eq_2]
    simp [native_ite, native_Teq]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Numeral runA) := by
      rw [hRunA] at hARel
      rw [show __eo_to_smt (Term.Numeral runA) =
          SmtTerm.Numeral runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_2] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Numeral runB) := by
      rw [hRunB] at hBRel
      rw [show __eo_to_smt (Term.Numeral runB) =
          SmtTerm.Numeral runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_2] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Numeral runA :=
      smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Numeral runB :=
      smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
    have hDivByZeroFalse :
        __smtx_model_eval_eq
            (SmtValue.Numeral runB) (SmtValue.Numeral 0) =
          SmtValue.Boolean false := by
      have hValNe :
          SmtValue.Numeral runB ≠ SmtValue.Numeral 0 := by
        intro h
        cases h
        exact hRunBNe rfl
      simp [__smtx_model_eval_eq, native_veq, hValNe]
    rw [show
        __smtx_model_eval M
            (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_ite
            (__smtx_model_eval_eq
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Numeral 0))
            (__smtx_model_eval_apply M
              (native_model_lookup M native_div_by_zero_id
                (SmtType.FunType SmtType.Int SmtType.Int))
              (__smtx_model_eval M (__eo_to_smt a)))
            (__smtx_model_eval_div_total
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b))) by
      rw [__smtx_model_eval.eq_24]]
    rw [hAEval, hBEval, hDivByZeroFalse]
    rw [show
        __eo_to_smt
            (__eo_zdiv (Term.Numeral runA) (Term.Numeral runB)) =
          SmtTerm.Numeral (native_div_total runA runB) by
      simp [__eo_zdiv, hNZ, native_ite]
      rfl]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Numeral (native_div_total runA runB))
        (__smtx_model_eval M
          (SmtTerm.Numeral (native_div_total runA runB)))
    rw [__smtx_model_eval.eq_2]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_mod_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b) := by
  intro hATrans hEvalTy
  have hModNN :
      term_has_non_none_type
        (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases int_binop_args_of_non_none
      (op := SmtTerm.mod) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (R := SmtType.Int)
      (typeof_mod_eq (__eo_to_smt a) (__eo_to_smt b)) hModNN with
    ⟨hATyInt, hBTyInt⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyInt]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hModEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_div (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int
    rw [hAEoInt, hBEoInt]
    rfl
  have hRunModNe :
      __eo_zmod (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
            (__eo_zmod (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
          (__eo_zmod (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_zmod (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunModNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
            (__eo_zmod (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
            (__eo_zmod (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunModEoInt :
      __eo_typeof (__eo_zmod (__run_evaluate a) (__run_evaluate b)) =
        Term.UOp UserOp.Int := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b)
        (__eo_zmod (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hModEoType
  rcases eo_zmod_args_numeral_of_typeof_int
      (__run_evaluate a) (__run_evaluate b) hRunModEoInt with
    ⟨runA, runB, hRunA, hRunB, hNZ⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
    rw [hRunB]
    rfl
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
    rw [hRunA]
    rfl
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hIntTypeNe hAEoInt hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.mod) a b rec hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.mod) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  have hRunBNe : runB ≠ 0 := by
    intro hZero
    subst runB
    simp [native_zeq] at hNZ
  change
    __smtx_typeof (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_zmod (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_zmod (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · rw [show
        __eo_to_smt
            (__eo_zmod (Term.Numeral runA) (Term.Numeral runB)) =
          SmtTerm.Numeral (native_mod_total runA runB) by
      simp [__eo_zmod, hNZ, native_ite]
      rfl]
    change
      __smtx_typeof (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Numeral (native_mod_total runA runB))
    rw [typeof_mod_eq, hATyInt, hBTyInt]
    rw [__smtx_typeof.eq_2]
    simp [native_ite, native_Teq]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Numeral runA) := by
      rw [hRunA] at hARel
      rw [show __eo_to_smt (Term.Numeral runA) =
          SmtTerm.Numeral runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_2] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Numeral runB) := by
      rw [hRunB] at hBRel
      rw [show __eo_to_smt (Term.Numeral runB) =
          SmtTerm.Numeral runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_2] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Numeral runA :=
      smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Numeral runB :=
      smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
    have hModByZeroFalse :
        __smtx_model_eval_eq
            (SmtValue.Numeral runB) (SmtValue.Numeral 0) =
          SmtValue.Boolean false := by
      have hValNe :
          SmtValue.Numeral runB ≠ SmtValue.Numeral 0 := by
        intro h
        cases h
        exact hRunBNe rfl
      simp [__smtx_model_eval_eq, native_veq, hValNe]
    rw [show
        __smtx_model_eval M
            (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_ite
            (__smtx_model_eval_eq
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Numeral 0))
            (__smtx_model_eval_apply M
              (native_model_lookup M native_mod_by_zero_id
                (SmtType.FunType SmtType.Int SmtType.Int))
              (__smtx_model_eval M (__eo_to_smt a)))
            (__smtx_model_eval_mod_total
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b))) by
      rw [__smtx_model_eval.eq_25]]
    rw [hAEval, hBEval, hModByZeroFalse]
    rw [show
        __eo_to_smt
            (__eo_zmod (Term.Numeral runA) (Term.Numeral runB)) =
          SmtTerm.Numeral (native_mod_total runA runB) by
      simp [__eo_zmod, hNZ, native_ite]
      rfl]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Numeral (native_mod_total runA runB))
        (__smtx_model_eval M
          (SmtTerm.Numeral (native_mod_total runA runB)))
    rw [__smtx_model_eval.eq_2]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_div_total_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b) := by
  intro hATrans hEvalTy
  have hDivTotalNN :
      term_has_non_none_type
        (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases int_binop_args_of_non_none
      (op := SmtTerm.div_total)
      (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (R := SmtType.Int)
      (typeof_div_total_eq (__eo_to_smt a) (__eo_to_smt b))
      hDivTotalNN with
    ⟨hATyInt, hBTyInt⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyInt]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hDivTotalEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_div (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int
    rw [hAEoInt, hBEoInt]
    rfl
  let runBTerm := __run_evaluate b
  let runDivTotal :=
    __eo_ite (__eo_eq runBTerm (Term.Numeral 0))
      (Term.Numeral 0) (__eo_zdiv (__run_evaluate a) runBTerm)
  have hRunDivTotalNe : runDivTotal ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
            runDivTotal) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
          runDivTotal ≠ Term.Stuck := by
    intro hMk
    cases hRun : runDivTotal <;>
      simp [__eo_mk_apply, hRun] at hMk hRunDivTotalNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
            runDivTotal) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
            runDivTotal) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunDivTotalEoInt :
      __eo_typeof runDivTotal = Term.UOp UserOp.Int := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)
        runDivTotal hEvalEqTy
    exact hEq.symm.trans hDivTotalEoType
  rcases eo_div_total_args_shape_of_typeof_int
      (__run_evaluate a) runBTerm hRunDivTotalNe hRunDivTotalEoInt with
    ⟨runB, hRunB, hRunBShape⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
    change __eo_typeof runBTerm = Term.UOp UserOp.Int
    rw [hRunB]
    rfl
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.div_total) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  have hBRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (SmtValue.Numeral runB) := by
    change __run_evaluate b = Term.Numeral runB at hRunB
    rw [hRunB] at hBRel
    rw [show __eo_to_smt (Term.Numeral runB) =
        SmtTerm.Numeral runB by
      rfl] at hBRel
    rw [__smtx_model_eval.eq_2] at hBRel
    exact hBRel
  have hBEval :
      __smtx_model_eval M (__eo_to_smt b) =
        SmtValue.Numeral runB :=
    smt_value_rel_numeral_eq
      (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
  change
    __smtx_typeof
        (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_ite (__eo_eq (__run_evaluate b) (Term.Numeral 0))
              (Term.Numeral 0)
              (__eo_zdiv (__run_evaluate a) (__run_evaluate b)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_ite (__eo_eq (__run_evaluate b) (Term.Numeral 0))
              (Term.Numeral 0)
              (__eo_zdiv (__run_evaluate a) (__run_evaluate b)))))
  change __run_evaluate b = Term.Numeral runB at hRunB
  rw [hRunB]
  cases hRunBShape with
  | inl hRunBZero =>
      subst runB
      constructor
      · rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral 0) (Term.Numeral 0))
                  (Term.Numeral 0)
                  (__eo_zdiv (__run_evaluate a) (Term.Numeral 0))) =
              SmtTerm.Numeral 0 by
          simp [__eo_eq, __eo_ite, native_teq, native_ite]
          rfl]
        change
          __smtx_typeof
              (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_typeof (SmtTerm.Numeral 0)
        rw [typeof_div_total_eq, hATyInt, hBTyInt]
        rw [__smtx_typeof.eq_2]
        simp [native_ite, native_Teq]
      · have hAEvalValueTy :
            __smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt a)) =
              SmtType.Int := by
          simpa [hATyInt] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt a) (by
                unfold term_has_non_none_type
                rw [hATyInt]
                simp)
        rcases int_value_canonical hAEvalValueTy with
          ⟨evalA, hAEval⟩
        rw [show
            __smtx_model_eval M
                (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_div_total
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_30]]
        rw [hAEval, hBEval]
        rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral 0) (Term.Numeral 0))
                  (Term.Numeral 0)
                  (__eo_zdiv (__run_evaluate a) (Term.Numeral 0))) =
              SmtTerm.Numeral 0 by
          simp [__eo_eq, __eo_ite, native_teq, native_ite]
          rfl]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_div_total evalA 0))
            (__smtx_model_eval M (SmtTerm.Numeral 0))
        rw [__smtx_model_eval.eq_2]
        simp [native_div_total]
        exact RuleProofs.smt_value_rel_refl _
  | inr hRunBNonzero =>
      rcases hRunBNonzero with ⟨runA, hRunA, hNZ⟩
      have hRunAEoType :
          __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
        rw [hRunA]
        rfl
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
          (Term.UOp UserOp.Int)
          (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
          hIntTypeNe hAEoInt hRunAEoType
      rcases run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.div_total) a b rec hATransA hAProgTy with
        ⟨_hASameTy, hARel⟩
      have hRunBNe : runB ≠ 0 := by
        intro hZero
        subst runB
        simp [native_zeq] at hNZ
      have hZeroRunBNe : 0 ≠ runB := by
        intro hZero
        exact hRunBNe hZero.symm
      rw [hRunA]
      constructor
      · rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral runB) (Term.Numeral 0))
                  (Term.Numeral 0)
                  (__eo_zdiv (Term.Numeral runA) (Term.Numeral runB))) =
              SmtTerm.Numeral (native_div_total runA runB) by
          simp [__eo_eq, __eo_ite, __eo_zdiv, hNZ, native_ite,
            native_teq, hZeroRunBNe]
          rfl]
        change
          __smtx_typeof
              (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_typeof (SmtTerm.Numeral (native_div_total runA runB))
        rw [typeof_div_total_eq, hATyInt, hBTyInt]
        rw [__smtx_typeof.eq_2]
        simp [native_ite, native_Teq]
      · have hARelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (SmtValue.Numeral runA) := by
          rw [hRunA] at hARel
          rw [show __eo_to_smt (Term.Numeral runA) =
              SmtTerm.Numeral runA by
            rfl] at hARel
          rw [__smtx_model_eval.eq_2] at hARel
          exact hARel
        have hAEval :
            __smtx_model_eval M (__eo_to_smt a) =
              SmtValue.Numeral runA :=
          smt_value_rel_numeral_eq
            (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
        rw [show
            __smtx_model_eval M
                (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_div_total
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_30]]
        rw [hAEval, hBEval]
        rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral runB) (Term.Numeral 0))
                  (Term.Numeral 0)
                  (__eo_zdiv (Term.Numeral runA) (Term.Numeral runB))) =
              SmtTerm.Numeral (native_div_total runA runB) by
          simp [__eo_eq, __eo_ite, __eo_zdiv, hNZ, native_ite,
            native_teq, hZeroRunBNe]
          rfl]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_div_total runA runB))
            (__smtx_model_eval M
              (SmtTerm.Numeral (native_div_total runA runB)))
        rw [__smtx_model_eval.eq_2]
        exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_mod_total_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b) := by
  intro hATrans hEvalTy
  have hModTotalNN :
      term_has_non_none_type
        (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases int_binop_args_of_non_none
      (op := SmtTerm.mod_total)
      (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (R := SmtType.Int)
      (typeof_mod_total_eq (__eo_to_smt a) (__eo_to_smt b))
      hModTotalNN with
    ⟨hATyInt, hBTyInt⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyInt]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hModTotalEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_div (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int
    rw [hAEoInt, hBEoInt]
    rfl
  let runATerm := __run_evaluate a
  let runBTerm := __run_evaluate b
  let runModTotal :=
    __eo_ite (__eo_eq runBTerm (Term.Numeral 0))
      runATerm (__eo_zmod runATerm runBTerm)
  have hRunModTotalNe : runModTotal ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
            runModTotal) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
          runModTotal ≠ Term.Stuck := by
    intro hMk
    cases hRun : runModTotal <;>
      simp [__eo_mk_apply, hRun] at hMk hRunModTotalNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
            runModTotal) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
            runModTotal) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunModTotalEoInt :
      __eo_typeof runModTotal = Term.UOp UserOp.Int := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)
        runModTotal hEvalEqTy
    exact hEq.symm.trans hModTotalEoType
  rcases eo_mod_total_args_shape_of_typeof_int
      runATerm runBTerm hRunModTotalNe hRunModTotalEoInt with
    ⟨runB, hRunB, hRunBShape⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
    change __eo_typeof runBTerm = Term.UOp UserOp.Int
    rw [hRunB]
    rfl
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.mod_total) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  have hBRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (SmtValue.Numeral runB) := by
    change __run_evaluate b = Term.Numeral runB at hRunB
    rw [hRunB] at hBRel
    rw [show __eo_to_smt (Term.Numeral runB) =
        SmtTerm.Numeral runB by
      rfl] at hBRel
    rw [__smtx_model_eval.eq_2] at hBRel
    exact hBRel
  have hBEval :
      __smtx_model_eval M (__eo_to_smt b) =
        SmtValue.Numeral runB :=
    smt_value_rel_numeral_eq
      (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
  change
    __smtx_typeof
        (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_ite (__eo_eq (__run_evaluate b) (Term.Numeral 0))
              (__run_evaluate a)
              (__eo_zmod (__run_evaluate a) (__run_evaluate b)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_ite (__eo_eq (__run_evaluate b) (Term.Numeral 0))
              (__run_evaluate a)
              (__eo_zmod (__run_evaluate a) (__run_evaluate b)))))
  change __run_evaluate b = Term.Numeral runB at hRunB
  rw [hRunB]
  cases hRunBShape with
  | inl hRunBZero =>
      subst runB
      have hRunAEoType :
          __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
        change
          __eo_typeof
              (__eo_ite (__eo_eq (__run_evaluate b) (Term.Numeral 0))
                (__run_evaluate a)
                (__eo_zmod (__run_evaluate a) (__run_evaluate b))) =
            Term.UOp UserOp.Int at hRunModTotalEoInt
        rw [hRunB] at hRunModTotalEoInt
        simpa [__eo_eq, __eo_ite, native_teq, native_ite]
          using hRunModTotalEoInt
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
          (Term.UOp UserOp.Int)
          (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
          hIntTypeNe hAEoInt hRunAEoType
      rcases run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.mod_total) a b rec hATransA hAProgTy with
        ⟨hASameTy, hARel⟩
      constructor
      · rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral 0) (Term.Numeral 0))
                  (__run_evaluate a)
                  (__eo_zmod (__run_evaluate a) (Term.Numeral 0))) =
              __eo_to_smt (__run_evaluate a) by
          simp [__eo_eq, __eo_ite, native_teq, native_ite]]
        rw [typeof_mod_total_eq, hATyInt, hBTyInt]
        simp [native_ite, native_Teq]
        rw [← hASameTy, hATyInt]
      · have hAEvalValueTy :
            __smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt a)) =
              SmtType.Int := by
          simpa [hATyInt] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt a) (by
                unfold term_has_non_none_type
                rw [hATyInt]
                simp)
        rcases int_value_canonical hAEvalValueTy with
          ⟨evalA, hAEval⟩
        rw [show
            __smtx_model_eval M
                (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_mod_total
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_31]]
        rw [hAEval, hBEval]
        rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral 0) (Term.Numeral 0))
                  (__run_evaluate a)
                  (__eo_zmod (__run_evaluate a) (Term.Numeral 0))) =
              __eo_to_smt (__run_evaluate a) by
          simp [__eo_eq, __eo_ite, native_teq, native_ite]]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_mod_total evalA 0))
            (__smtx_model_eval M (__eo_to_smt (__run_evaluate a)))
        have hModZero : native_mod_total evalA 0 = evalA := by
          simp [native_mod_total]
        rw [hModZero]
        rw [hAEval] at hARel
        exact hARel
  | inr hRunBNonzero =>
      rcases hRunBNonzero with ⟨runA, hRunA, hNZ⟩
      have hRunA' : __run_evaluate a = Term.Numeral runA := by
        simpa only [runATerm] using hRunA
      have hRunAEoType :
          __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
        rw [hRunA']
        rfl
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
          (Term.UOp UserOp.Int)
          (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
          hIntTypeNe hAEoInt hRunAEoType
      rcases run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.mod_total) a b rec hATransA hAProgTy with
        ⟨_hASameTy, hARel⟩
      have hRunBNe : runB ≠ 0 := by
        intro hZero
        subst runB
        simp [native_zeq] at hNZ
      have hZeroRunBNe : 0 ≠ runB := by
        intro hZero
        exact hRunBNe hZero.symm
      rw [hRunA']
      constructor
      · rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral runB) (Term.Numeral 0))
                  (Term.Numeral runA)
                  (__eo_zmod (Term.Numeral runA) (Term.Numeral runB))) =
              SmtTerm.Numeral (native_mod_total runA runB) by
          simp [__eo_eq, __eo_ite, __eo_zmod, hNZ, native_ite,
            native_teq, hZeroRunBNe]
          rfl]
        change
          __smtx_typeof
              (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_typeof (SmtTerm.Numeral (native_mod_total runA runB))
        rw [typeof_mod_total_eq, hATyInt, hBTyInt]
        rw [__smtx_typeof.eq_2]
        simp [native_ite, native_Teq]
      · have hARelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (SmtValue.Numeral runA) := by
          rw [hRunA'] at hARel
          rw [show __eo_to_smt (Term.Numeral runA) =
              SmtTerm.Numeral runA by
            rfl] at hARel
          rw [__smtx_model_eval.eq_2] at hARel
          exact hARel
        have hAEval :
            __smtx_model_eval M (__eo_to_smt a) =
              SmtValue.Numeral runA :=
          smt_value_rel_numeral_eq
            (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
        rw [show
            __smtx_model_eval M
                (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_mod_total
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_31]]
        rw [hAEval, hBEval]
        rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral runB) (Term.Numeral 0))
                  (Term.Numeral runA)
                  (__eo_zmod (Term.Numeral runA) (Term.Numeral runB))) =
              SmtTerm.Numeral (native_mod_total runA runB) by
          simp [__eo_eq, __eo_ite, __eo_zmod, hNZ, native_ite,
            native_teq, hZeroRunBNe]
          rfl]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_mod_total runA runB))
            (__smtx_model_eval M
              (SmtTerm.Numeral (native_mod_total runA runB)))
        rw [__smtx_model_eval.eq_2]
        exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_and_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) := by
  intro hATrans hEvalTy
  have hAndBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) :=
    has_bool_type_and_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    RuleProofs.eo_has_bool_type_and_left a b hAndBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    RuleProofs.eo_has_bool_type_and_right a b hAndBool
  have hATransA : RuleProofs.eo_has_smt_translation a :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBool : __eo_typeof a = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hAMatch.symm.trans hABool)
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hAndEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunAndNe :
      __eo_and (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
          (__eo_and (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_and (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunAndNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunAndEoBool :
      __eo_typeof (__eo_and (__run_evaluate a) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b)
        (__eo_and (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hAndEoBool
  rcases eo_and_args_boolean_of_typeof_bool
      (__run_evaluate a) (__run_evaluate b) hRunAndEoBool with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoBool : __eo_typeof (__run_evaluate a) = Term.Bool := by
    rw [hRunA]
    rfl
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunB]
    rfl
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool a
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hAEoBool hRunAEoBool
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool b
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBEoBool hRunBEoBool
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.and) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.and) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_and runA runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_and_eq, hATy, hBTy, __smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hARelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (SmtTerm.Boolean runA)) := by
      simpa [hRunA] using hARel
    have hBRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runB)) := by
      simpa [hRunB] using hBRel
    have hRelAnd :=
      smt_value_rel_model_eval_and_of_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (SmtTerm.Boolean runA))
        (__smtx_model_eval M (SmtTerm.Boolean runB))
        hARelBool hBRelBool
    simpa [__eo_and, __smtx_model_eval, __smtx_model_eval_and] using hRelAnd

private theorem run_evaluate_sound_apply_or_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) := by
  intro hATrans hEvalTy
  have hOrBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) :=
    has_bool_type_or_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    has_bool_type_or_left a b hOrBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    has_bool_type_or_right a b hOrBool
  have hATransA : RuleProofs.eo_has_smt_translation a :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBool : __eo_typeof a = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hAMatch.symm.trans hABool)
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hOrEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunOrNe :
      __eo_or (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
          (__eo_or (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_or (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunOrNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunOrEoBool :
      __eo_typeof (__eo_or (__run_evaluate a) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b)
        (__eo_or (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hOrEoBool
  rcases eo_or_args_boolean_of_typeof_bool
      (__run_evaluate a) (__run_evaluate b) hRunOrEoBool with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoBool : __eo_typeof (__run_evaluate a) = Term.Bool := by
    rw [hRunA]
    rfl
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunB]
    rfl
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool a
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hAEoBool hRunAEoBool
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool b
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBEoBool hRunBEoBool
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.or) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.or) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_or runA runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_or_eq, hATy, hBTy, __smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hARelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (SmtTerm.Boolean runA)) := by
      simpa [hRunA] using hARel
    have hBRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runB)) := by
      simpa [hRunB] using hBRel
    have hRelOr :=
      smt_value_rel_model_eval_or_of_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (SmtTerm.Boolean runA))
        (__smtx_model_eval M (SmtTerm.Boolean runB))
        hARelBool hBRelBool
    simpa [__eo_or, __smtx_model_eval, __smtx_model_eval_or] using hRelOr

private theorem run_evaluate_sound_apply_xor_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) := by
  intro hATrans hEvalTy
  have hXorBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) :=
    has_bool_type_xor_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    has_bool_type_xor_left a b hXorBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    has_bool_type_xor_right a b hXorBool
  have hATransA : RuleProofs.eo_has_smt_translation a :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBool : __eo_typeof a = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hAMatch.symm.trans hABool)
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hXorEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunXorNe :
      __eo_xor (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
          (__eo_xor (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_xor (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunXorNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunXorEoBool :
      __eo_typeof (__eo_xor (__run_evaluate a) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b)
        (__eo_xor (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hXorEoBool
  rcases eo_xor_args_boolean_of_typeof_bool
      (__run_evaluate a) (__run_evaluate b) hRunXorEoBool with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoBool : __eo_typeof (__run_evaluate a) = Term.Bool := by
    rw [hRunA]
    rfl
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunB]
    rfl
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool a
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hAEoBool hRunAEoBool
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool b
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBEoBool hRunBEoBool
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.xor) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.xor) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_xor runA runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_xor_eq, hATy, hBTy, __smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hARelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (SmtTerm.Boolean runA)) := by
      simpa [hRunA] using hARel
    have hBRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runB)) := by
      simpa [hRunB] using hBRel
    have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Boolean runA) := by
      simpa [__smtx_model_eval] using hARelBool
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Boolean runB) := by
      simpa [__smtx_model_eval] using hBRelBool
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean runA :=
      smt_value_rel_boolean_eq
        (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean runB :=
      smt_value_rel_boolean_eq
        (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_xor
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __eo_to_smt
            (__eo_xor (Term.Boolean runA) (Term.Boolean runB)) =
          SmtTerm.Boolean (native_xor runA runB) by
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Boolean (native_xor runA runB)) =
          SmtValue.Boolean (native_xor runA runB) by
      simp [__smtx_model_eval]]
    cases runA <;> cases runB <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_xor,
        __smtx_model_eval_not, __smtx_model_eval_eq, native_xor,
        native_not, native_veq]

private theorem run_evaluate_sound_apply_imp_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) := by
  intro hATrans hEvalTy
  have hImpBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) :=
    has_bool_type_imp_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    has_bool_type_imp_left a b hImpBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    has_bool_type_imp_right a b hImpBool
  have hATransA : RuleProofs.eo_has_smt_translation a :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBool : __eo_typeof a = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hAMatch.symm.trans hABool)
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hImpEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunImpNe :
      __eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b) ≠
        Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
          (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun :
        __eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunImpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunImpEoBool :
      __eo_typeof
          (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b)
        (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))
        hEvalEqTy
    exact hEq.symm.trans hImpEoBool
  rcases eo_or_args_boolean_of_typeof_bool
      (__eo_not (__run_evaluate a)) (__run_evaluate b)
      hRunImpEoBool with
    ⟨runNotA, runB, hRunNotA, hRunB⟩
  have hRunNotAEoBool : __eo_typeof (__eo_not (__run_evaluate a)) = Term.Bool := by
    rw [hRunNotA]
    rfl
  rcases eo_not_arg_boolean_of_typeof_bool
      (__run_evaluate a) hRunNotAEoBool with
    ⟨runA, hRunA⟩
  have hRunAEoBool : __eo_typeof (__run_evaluate a) = Term.Bool := by
    rw [hRunA]
    rfl
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunB]
    rfl
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool a
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hAEoBool hRunAEoBool
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool b
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBEoBool hRunBEoBool
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.imp) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.imp) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_or (native_not runA) runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_imp_eq, hATy, hBTy, __smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hARelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (SmtTerm.Boolean runA)) := by
      simpa [hRunA] using hARel
    have hBRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runB)) := by
      simpa [hRunB] using hBRel
    have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Boolean runA) := by
      simpa [__smtx_model_eval] using hARelBool
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Boolean runB) := by
      simpa [__smtx_model_eval] using hBRelBool
    have hRelImp :=
      smt_value_rel_model_eval_imp_of_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
        (SmtValue.Boolean runA)
        (SmtValue.Boolean runB)
        hARelValue hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_imp
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [show
        __eo_to_smt
            (__eo_or (__eo_not (Term.Boolean runA)) (Term.Boolean runB)) =
          SmtTerm.Boolean (native_or (native_not runA) runB) by
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Boolean (native_or (native_not runA) runB)) =
          SmtValue.Boolean (native_or (native_not runA) runB) by
      simp [__smtx_model_eval]]
    simpa [__smtx_model_eval_imp, __smtx_model_eval_not, __smtx_model_eval_or]
      using hRelImp

private theorem run_evaluate_sound_apply_str_concat_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b) := by
  intro hATrans hEvalTy
  have hConcatNN :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases smt_str_concat_args_of_non_none_local a b hConcatNN with
    ⟨T, hATy, hBTy, hConcatTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hOrigMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b) hATrans
  have hOrigEoSmtSeq :
      __eo_to_smt_type
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b)) =
        SmtType.Seq T := by
    rw [← hOrigMatch]
    exact hConcatTy
  rcases TranslationProofs.eo_to_smt_type_eq_seq hOrigEoSmtSeq with
    ⟨U, hOrigEoSeq, _hUSmt⟩
  have hRunConcatNe :
      __eo_concat (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b))
            (__eo_concat (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b))
          (__eo_concat (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_concat (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunConcatNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b))
            (__eo_concat (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b))
            (__eo_concat (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunConcatEoSeq :
      __eo_typeof (__eo_concat (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.Seq) U := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b)
        (__eo_concat (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hOrigEoSeq
  rcases eo_concat_args_string_of_typeof_seq
      (__run_evaluate a) (__run_evaluate b) U hRunConcatEoSeq with
    ⟨sx, sy, hRunA, hRunB, hUChar⟩
  subst U
  have hOrigEoSeqChar :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    simpa using hOrigEoSeq
  rcases eo_typeof_str_concat_args_of_seq_char a b hOrigEoSeqChar with
    ⟨hAEoSeqChar, hBEoSeqChar⟩
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoSmtChar :
      __eo_to_smt_type (__eo_typeof a) = SmtType.Seq SmtType.Char := by
    rw [hAEoSeqChar]
    simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq]
  have hBEoSmtChar :
      __eo_to_smt_type (__eo_typeof b) = SmtType.Seq SmtType.Char := by
    rw [hBEoSeqChar]
    simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq]
  have hATyChar :
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char :=
    hAMatch.trans hAEoSmtChar
  have hBTyChar :
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char :=
    hBMatch.trans hBEoSmtChar
  have hRunAEoSeqChar :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    rw [hRunA]
    rfl
  have hRunBEoSeqChar :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    rw [hRunB]
    rfl
  have hSeqCharNe :
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hSeqCharNe hAEoSeqChar hRunAEoSeqChar
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hSeqCharNe hBEoSeqChar hRunBEoSeqChar
  rcases run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.str_concat) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.str_concat) a) b rec
      hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hSxTy :
      __smtx_typeof (__eo_to_smt (Term.String sx)) =
        SmtType.Seq SmtType.Char := by
    have h := hASameTy
    rw [hRunA] at h
    exact h.symm.trans hATyChar
  have hSyTy :
      __smtx_typeof (__eo_to_smt (Term.String sy)) =
        SmtType.Seq SmtType.Char := by
    have h := hBSameTy
    rw [hRunB] at h
    exact h.symm.trans hBTyChar
  have hSxValid : native_string_valid sx = true :=
    native_string_valid_of_string_type hSxTy
  have hSyValid : native_string_valid sy = true :=
    native_string_valid_of_string_type hSyTy
  have hConcatValid :
      native_string_valid (native_str_concat sx sy) = true := by
    change native_string_valid (sx ++ sy) = true
    exact native_string_valid_append_local hSxValid hSyValid
  change
    __smtx_typeof (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_concat (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_concat (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.String (native_str_concat sx sy))
    rw [show
        __smtx_typeof
            (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) =
          SmtType.Seq SmtType.Char by
      simp [__smtx_typeof, __smtx_typeof_seq_op_2, hATyChar,
        hBTyChar, native_Teq, native_ite]]
    simp [__smtx_typeof, hConcatValid, native_ite]
  · have hSxEval :
        __smtx_model_eval M (__eo_to_smt (Term.String sx)) =
          SmtValue.Seq (native_pack_string sx) := by
      rw [show __eo_to_smt (Term.String sx) = SmtTerm.String sx by rfl]
      rw [__smtx_model_eval.eq_4]
    have hSyEval :
        __smtx_model_eval M (__eo_to_smt (Term.String sy)) =
          SmtValue.Seq (native_pack_string sy) := by
      rw [show __eo_to_smt (Term.String sy) = SmtTerm.String sy by rfl]
      rw [__smtx_model_eval.eq_4]
    have hARelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt (Term.String sx))) := by
      simpa [hRunA] using hARel
    have hBRelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String sy))) := by
      simpa [hRunB] using hBRel
    have hARelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Seq (native_pack_string sx)) := by
      simpa [hSxEval] using hARelString
    have hBRelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Seq (native_pack_string sy)) := by
      simpa [hSyEval] using hBRelString
    rcases smt_value_rel_seq_right_local hARelSeq with
      ⟨sxEval, hAEval, hASeqRel⟩
    rcases smt_value_rel_seq_right_local hBRelSeq with
      ⟨syEval, hBEval, hBSeqRel⟩
    have hASeqEq :
        sxEval = native_pack_string sx :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hASeqRel
    have hBSeqEq :
        syEval = native_pack_string sy :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hBSeqRel
    unfold RuleProofs.smt_value_rel
    rw [show
        __smtx_model_eval M
            (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_str_concat
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_80]]
    rw [hAEval, hBEval, hASeqEq, hBSeqEq]
    rw [show __eo_to_smt
          (__eo_concat (Term.String sx) (Term.String sy)) =
        SmtTerm.String (native_str_concat sx sy) by
      rfl]
    rw [__smtx_model_eval.eq_4]
    simp [__smtx_model_eval_str_concat, native_seq_concat,
      native_pack_string, native_str_concat, native_unpack_pack_seq_local,
      elem_typeof_pack_seq_local, List.map_append,
      RuleProofs.smtx_model_eval_eq_refl]

private theorem run_evaluate_sound_apply_str_to_lower_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_to_lower) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_to_lower) b) := by
  intro hATrans hEvalTy
  have hLowerNN :
      term_has_non_none_type (SmtTerm.str_to_lower (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  have hBTyChar :
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_lower)
      (typeof_str_to_lower_eq (__eo_to_smt b)) hLowerNN
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyChar]
    simp
  have hBEoSeqChar :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    eo_typeof_seq_char_of_smt_type_seq_char b hBTrans hBTyChar
  have hLowerEoSeqChar :
      __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_lower) b) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    change __eo_typeof_str_to_lower (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
    rw [hBEoSeqChar]
    rfl
  let runArg := __run_evaluate b
  let runLower :=
    __eo_ite (__eo_is_str runArg)
      (__str_case_conv_rec (__str_flatten (__str_nary_intro runArg))
        (Term.Boolean true))
      (__eo_mk_apply (Term.UOp UserOp.str_to_lower) runArg)
  have hRunLowerNe : runLower ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_lower) b))
            runLower) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.str_to_lower) b))
          runLower ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runLower <;>
      simp [__eo_mk_apply, hRun] at hMk hRunLowerNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_lower) b))
            runLower) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_lower) b))
            runLower) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunLowerEoSeqChar :
      __eo_typeof runLower =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.str_to_lower) b) runLower hEvalEqTy
    exact hEq.symm.trans hLowerEoSeqChar
  have hRunBEoSeqChar :
      __eo_typeof runArg =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    eo_str_to_lower_result_arg_typeof_seq_char runArg hRunLowerEoSeqChar
  have hSeqCharNe :
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ≠
        Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hSeqCharNe hBEoSeqChar hRunBEoSeqChar
  rcases run_evaluate_rec_apply_arg M (Term.UOp UserOp.str_to_lower) b rec
      hBTrans hBProgTy with
    ⟨hSameTy, hRel⟩
  have hSameTyRun :
      __smtx_typeof (__eo_to_smt b) =
        __smtx_typeof (__eo_to_smt runArg) := by
    simpa [runArg] using hSameTy
  have hRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt runArg)) := by
    simpa [runArg] using hRel
  change
    __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runLower) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runLower))
  by_cases hString : ∃ s : native_String, runArg = Term.String s
  · rcases hString with ⟨s, hs⟩
    have hRunStringTy :
        __smtx_typeof (__eo_to_smt (Term.String s)) =
          SmtType.Seq SmtType.Char := by
      rw [← hs]
      exact hSameTyRun.symm.trans hBTyChar
    have hValid : native_string_valid s = true :=
      native_string_valid_of_string_type hRunStringTy
    have hRunLowerString :
        runLower = Term.String (native_str_to_lower s) := by
      dsimp [runLower]
      rw [hs]
      exact str_to_lower_result_string hValid
    rw [hRunLowerString]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.String (native_str_to_lower s))
      rw [typeof_str_to_lower_eq]
      simp [__smtx_typeof, hBTyChar, native_ite, native_Teq,
        native_str_to_lower_valid hValid]
    · have hRelString :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [← hs]
        exact hRelRun
      have hRelLower :=
        smt_value_rel_model_eval_str_to_lower_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String s)))
          hRelString
      have hEvalLowerB :
          __smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt b)) =
            __smtx_model_eval_str_to_lower
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_90]
      have hEvalString :
          __smtx_model_eval M (__eo_to_smt (Term.String s)) =
            SmtValue.Seq (native_pack_string s) := by
        rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl]
        rw [__smtx_model_eval.eq_4]
      have hEvalLowerString :
          __smtx_model_eval M
              (__eo_to_smt (Term.String (native_str_to_lower s))) =
            __smtx_model_eval_str_to_lower
              (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [hEvalString]
        rw [show __eo_to_smt (Term.String (native_str_to_lower s)) =
          SmtTerm.String (native_str_to_lower s) by rfl]
        rw [__smtx_model_eval.eq_4]
        simp [__smtx_model_eval_str_to_lower,
          RuleProofs.native_unpack_string_pack_string]
      rw [hEvalLowerB, hEvalLowerString]
      exact hRelLower
  · have hNotString : ∀ s : native_String, runArg ≠ Term.String s := by
      intro s hs
      exact hString ⟨s, hs⟩
    have hRunArgNe : runArg ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hRunBEoSeqChar
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at hRunBEoSeqChar
      cases hRunBEoSeqChar
    have hRunLowerApply :
        runLower = Term.Apply (Term.UOp UserOp.str_to_lower) runArg := by
      dsimp [runLower]
      exact str_to_lower_result_non_string hNotString hRunArgNe
    rw [hRunLowerApply]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt runArg))
      have hRunTyChar :
          __smtx_typeof (__eo_to_smt runArg) =
            SmtType.Seq SmtType.Char :=
        hSameTyRun.symm.trans hBTyChar
      rw [typeof_str_to_lower_eq, typeof_str_to_lower_eq]
      simp [hBTyChar, hRunTyChar, native_ite, native_Teq]
    · have hRelLower :=
        smt_value_rel_model_eval_str_to_lower_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runArg))
          hRelRun
      have hEvalLowerB :
          __smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt b)) =
            __smtx_model_eval_str_to_lower
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_90]
      have hEvalLowerRun :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.UOp UserOp.str_to_lower) runArg)) =
            __smtx_model_eval_str_to_lower
              (__smtx_model_eval M (__eo_to_smt runArg)) := by
        change
          __smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt runArg)) =
            __smtx_model_eval_str_to_lower
              (__smtx_model_eval M (__eo_to_smt runArg))
        rw [__smtx_model_eval.eq_90]
      rw [hEvalLowerB, hEvalLowerRun]
      exact hRelLower

private theorem run_evaluate_sound_apply_str_to_upper_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_to_upper) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_to_upper) b) := by
  intro hATrans hEvalTy
  have hUpperNN :
      term_has_non_none_type (SmtTerm.str_to_upper (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  have hBTyChar :
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_upper)
      (typeof_str_to_upper_eq (__eo_to_smt b)) hUpperNN
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyChar]
    simp
  have hBEoSeqChar :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    eo_typeof_seq_char_of_smt_type_seq_char b hBTrans hBTyChar
  have hUpperEoSeqChar :
      __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_upper) b) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    change __eo_typeof_str_to_lower (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
    rw [hBEoSeqChar]
    rfl
  let runArg := __run_evaluate b
  let runUpper :=
    __eo_ite (__eo_is_str runArg)
      (__str_case_conv_rec (__str_flatten (__str_nary_intro runArg))
        (Term.Boolean false))
      (__eo_mk_apply (Term.UOp UserOp.str_to_upper) runArg)
  have hRunUpperNe : runUpper ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_upper) b))
            runUpper) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.str_to_upper) b))
          runUpper ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runUpper <;>
      simp [__eo_mk_apply, hRun] at hMk hRunUpperNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_upper) b))
            runUpper) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_upper) b))
            runUpper) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunUpperEoSeqChar :
      __eo_typeof runUpper =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.str_to_upper) b) runUpper hEvalEqTy
    exact hEq.symm.trans hUpperEoSeqChar
  have hRunBEoSeqChar :
      __eo_typeof runArg =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    eo_str_to_upper_result_arg_typeof_seq_char runArg hRunUpperEoSeqChar
  have hSeqCharNe :
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ≠
        Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hSeqCharNe hBEoSeqChar hRunBEoSeqChar
  rcases run_evaluate_rec_apply_arg M (Term.UOp UserOp.str_to_upper) b rec
      hBTrans hBProgTy with
    ⟨hSameTy, hRel⟩
  have hSameTyRun :
      __smtx_typeof (__eo_to_smt b) =
        __smtx_typeof (__eo_to_smt runArg) := by
    simpa [runArg] using hSameTy
  have hRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt runArg)) := by
    simpa [runArg] using hRel
  change
    __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runUpper) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runUpper))
  by_cases hString : ∃ s : native_String, runArg = Term.String s
  · rcases hString with ⟨s, hs⟩
    have hRunStringTy :
        __smtx_typeof (__eo_to_smt (Term.String s)) =
          SmtType.Seq SmtType.Char := by
      rw [← hs]
      exact hSameTyRun.symm.trans hBTyChar
    have hValid : native_string_valid s = true :=
      native_string_valid_of_string_type hRunStringTy
    have hRunUpperString :
        runUpper = Term.String (native_str_to_upper s) := by
      dsimp [runUpper]
      rw [hs]
      exact str_to_upper_result_string hValid
    rw [hRunUpperString]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.String (native_str_to_upper s))
      rw [typeof_str_to_upper_eq]
      simp [__smtx_typeof, hBTyChar, native_ite, native_Teq,
        native_str_to_upper_valid hValid]
    · have hRelString :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [← hs]
        exact hRelRun
      have hRelUpper :=
        smt_value_rel_model_eval_str_to_upper_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String s)))
          hRelString
      have hEvalUpperB :
          __smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt b)) =
            __smtx_model_eval_str_to_upper
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_91]
      have hEvalString :
          __smtx_model_eval M (__eo_to_smt (Term.String s)) =
            SmtValue.Seq (native_pack_string s) := by
        rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl]
        rw [__smtx_model_eval.eq_4]
      have hEvalUpperString :
          __smtx_model_eval M
              (__eo_to_smt (Term.String (native_str_to_upper s))) =
            __smtx_model_eval_str_to_upper
              (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [hEvalString]
        rw [show __eo_to_smt (Term.String (native_str_to_upper s)) =
          SmtTerm.String (native_str_to_upper s) by rfl]
        rw [__smtx_model_eval.eq_4]
        simp [__smtx_model_eval_str_to_upper,
          RuleProofs.native_unpack_string_pack_string]
      rw [hEvalUpperB, hEvalUpperString]
      exact hRelUpper
  · have hNotString : ∀ s : native_String, runArg ≠ Term.String s := by
      intro s hs
      exact hString ⟨s, hs⟩
    have hRunArgNe : runArg ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hRunBEoSeqChar
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at hRunBEoSeqChar
      cases hRunBEoSeqChar
    have hRunUpperApply :
        runUpper = Term.Apply (Term.UOp UserOp.str_to_upper) runArg := by
      dsimp [runUpper]
      exact str_to_upper_result_non_string hNotString hRunArgNe
    rw [hRunUpperApply]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt runArg))
      have hRunTyChar :
          __smtx_typeof (__eo_to_smt runArg) =
            SmtType.Seq SmtType.Char :=
        hSameTyRun.symm.trans hBTyChar
      rw [typeof_str_to_upper_eq, typeof_str_to_upper_eq]
      simp [hBTyChar, hRunTyChar, native_ite, native_Teq]
    · have hRelUpper :=
        smt_value_rel_model_eval_str_to_upper_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runArg))
          hRelRun
      have hEvalUpperB :
          __smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt b)) =
            __smtx_model_eval_str_to_upper
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_91]
      have hEvalUpperRun :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.UOp UserOp.str_to_upper) runArg)) =
            __smtx_model_eval_str_to_upper
              (__smtx_model_eval M (__eo_to_smt runArg)) := by
        change
          __smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt runArg)) =
            __smtx_model_eval_str_to_upper
              (__smtx_model_eval M (__eo_to_smt runArg))
        rw [__smtx_model_eval.eq_91]
      rw [hEvalUpperB, hEvalUpperRun]
      exact hRelUpper

private theorem run_evaluate_sound_apply_str_rev_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_rev) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_rev) b) := by
  intro hATrans hEvalTy
  have hRevNN :
      term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
      (typeof_str_rev_eq (__eo_to_smt b)) hRevNN with
    ⟨T, hBTySeq⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTySeq]
    simp
  rcases eo_typeof_seq_of_smt_type_seq b hBTrans hBTySeq with
    ⟨U, hBEoSeq, hUSmt⟩
  have hRevEoSeq :
      __eo_typeof (Term.Apply (Term.UOp UserOp.str_rev) b) =
        Term.Apply (Term.UOp UserOp.Seq) U := by
    change __eo_typeof_str_rev (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.Seq) U
    rw [hBEoSeq]
    rfl
  let runArg := __run_evaluate b
  let runRev :=
    __eo_ite (__eo_is_str runArg)
      (__str_nary_elim
        (__str_collect
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__str_nary_intro runArg)))))
      (__eo_mk_apply (Term.UOp UserOp.str_rev) runArg)
  have hRunRevNe : runRev ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_rev) b))
            runRev) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.str_rev) b))
          runRev ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runRev <;>
      simp [__eo_mk_apply, hRun] at hMk hRunRevNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_rev) b))
            runRev) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_rev) b))
            runRev) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunRevEoSeq :
      __eo_typeof runRev =
        Term.Apply (Term.UOp UserOp.Seq) U := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.str_rev) b) runRev hEvalEqTy
    exact hEq.symm.trans hRevEoSeq
  have hRunBEoSeq :
      __eo_typeof runArg = Term.Apply (Term.UOp UserOp.Seq) U :=
    eo_str_rev_result_arg_typeof_seq runArg U hRunRevEoSeq
  have hSeqNe :
      Term.Apply (Term.UOp UserOp.Seq) U ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.Seq) U)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hSeqNe hBEoSeq hRunBEoSeq
  rcases run_evaluate_rec_apply_arg M (Term.UOp UserOp.str_rev) b rec
      hBTrans hBProgTy with
    ⟨hSameTy, hRel⟩
  have hSameTyRun :
      __smtx_typeof (__eo_to_smt b) =
        __smtx_typeof (__eo_to_smt runArg) := by
    simpa [runArg] using hSameTy
  have hRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt runArg)) := by
    simpa [runArg] using hRel
  change
    __smtx_typeof (SmtTerm.str_rev (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runRev) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runRev))
  by_cases hString : ∃ s : native_String, runArg = Term.String s
  · rcases hString with ⟨s, hs⟩
    have hRunStringTy :
        __smtx_typeof (__eo_to_smt (Term.String s)) =
          SmtType.Seq T := by
      rw [← hs]
      exact hSameTyRun.symm.trans hBTySeq
    rcases smt_string_seq_type_inv hRunStringTy with ⟨hValid, hTChar⟩
    subst T
    have hRunRevString :
        runRev = Term.String s.reverse := by
      dsimp [runRev]
      rw [hs]
      exact str_rev_result_string
    rw [hRunRevString]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_rev (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.String s.reverse)
      rw [typeof_str_rev_eq]
      simp [__smtx_typeof_seq_op_1, hBTySeq, hTChar, __smtx_typeof,
        native_ite, native_string_valid_reverse_local hValid]
    · have hRelString :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [← hs]
        exact hRelRun
      have hRelRev :=
        smt_value_rel_model_eval_str_rev_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String s)))
          hRelString
      have hEvalRevB :
          __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt b)) =
            __smtx_model_eval_str_rev
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_88]
      have hEvalString :
          __smtx_model_eval M (__eo_to_smt (Term.String s)) =
            SmtValue.Seq (native_pack_string s) := by
        rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl]
        rw [__smtx_model_eval.eq_4]
      have hEvalRevString :
          __smtx_model_eval M (__eo_to_smt (Term.String s.reverse)) =
            __smtx_model_eval_str_rev
              (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [hEvalString]
        rw [show __eo_to_smt (Term.String s.reverse) =
          SmtTerm.String s.reverse by rfl]
        rw [__smtx_model_eval.eq_4]
        simp [__smtx_model_eval_str_rev, native_pack_string,
          native_unpack_pack_seq_local, elem_typeof_pack_seq_local,
          native_seq_rev]
      rw [hEvalRevB, hEvalRevString]
      exact hRelRev
  · have hNotString : ∀ s : native_String, runArg ≠ Term.String s := by
      intro s hs
      exact hString ⟨s, hs⟩
    have hRunArgNe : runArg ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hRunBEoSeq
      change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) U at hRunBEoSeq
      cases hRunBEoSeq
    have hRunRevApply :
        runRev = Term.Apply (Term.UOp UserOp.str_rev) runArg := by
      dsimp [runRev]
      exact str_rev_result_non_string hNotString hRunArgNe
    rw [hRunRevApply]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_rev (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.str_rev (__eo_to_smt runArg))
      have hRunTySeq :
          __smtx_typeof (__eo_to_smt runArg) = SmtType.Seq T :=
        hSameTyRun.symm.trans hBTySeq
      rw [typeof_str_rev_eq, typeof_str_rev_eq]
      simp [__smtx_typeof_seq_op_1, hBTySeq, hRunTySeq]
    · have hRelRev :=
        smt_value_rel_model_eval_str_rev_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runArg))
          hRelRun
      have hEvalRevB :
          __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt b)) =
            __smtx_model_eval_str_rev
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_88]
      have hEvalRevRun :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.UOp UserOp.str_rev) runArg)) =
            __smtx_model_eval_str_rev
              (__smtx_model_eval M (__eo_to_smt runArg)) := by
        change
          __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt runArg)) =
            __smtx_model_eval_str_rev
              (__smtx_model_eval M (__eo_to_smt runArg))
        rw [__smtx_model_eval.eq_88]
      rw [hEvalRevB, hEvalRevRun]
      exact hRelRev

private theorem run_evaluate_sound_apply_ubv_to_int_core
    (M : SmtModel) (hM : model_total_typed M)
    (x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.ubv_to_int) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.ubv_to_int) x) := by
  intro hATrans hEvalTy
  have hUbvToIntNN :
      term_has_non_none_type
        (SmtTerm.ubv_to_int (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_unop_ret_arg_of_non_none
      (op := SmtTerm.ubv_to_int) (ret := SmtType.Int)
      (by rw [__smtx_typeof.eq_131]) hUbvToIntNN with
    ⟨w, hxSmtTy⟩
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxSmtTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXEoBv :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hXMatch.symm.trans hxSmtTy)
  have hUbvToIntEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.ubv_to_int) x) =
        Term.UOp UserOp.Int := by
    change __eo_typeof__at_bvsize (__eo_typeof x) = Term.UOp UserOp.Int
    rw [hXEoBv]
    rfl
  let runToInt := __eo_to_z (__run_evaluate x)
  have hRunToIntNe : runToInt ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.ubv_to_int) x))
            runToInt) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.ubv_to_int) x))
          runToInt ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runToInt <;>
      simp [__eo_mk_apply, hRun] at hMk hRunToIntNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.ubv_to_int) x))
            runToInt) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.ubv_to_int) x))
            runToInt) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunToIntEoInt :
      __eo_typeof runToInt = Term.UOp UserOp.Int := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.ubv_to_int) x)
        runToInt hEvalEqTy
    exact hEq.symm.trans hUbvToIntEoType
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_smt_type_bitvec x w hXTrans hxSmtTy
  rcases run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.ubv_to_int) x rec hXTrans hXProgTy with
    ⟨hXSameTy, hXRel⟩
  have hRunXSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate x)) = SmtType.BitVec w := by
    rw [← hXSameTy]
    exact hxSmtTy
  cases hRunX : __run_evaluate x
  case Binary runW runN =>
    change
      __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt x)) =
          __smtx_typeof (__eo_to_smt runToInt) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ubv_to_int (__eo_to_smt x)))
          (__smtx_model_eval M (__eo_to_smt runToInt))
    rw [show runToInt = Term.Numeral runN by
      simp [runToInt, hRunX, __eo_to_z]]
    change
      __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt x)) =
          __smtx_typeof (SmtTerm.Numeral runN) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ubv_to_int (__eo_to_smt x)))
          (__smtx_model_eval M (SmtTerm.Numeral runN))
    constructor
    · rw [show
          __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt x)) =
            __smtx_typeof_bv_op_1_ret
              (__smtx_typeof (__eo_to_smt x)) SmtType.Int by
        rw [__smtx_typeof.eq_131]]
      rw [hxSmtTy]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_bv_op_1_ret, native_ite]
    · have hXRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt x))
            (SmtValue.Binary runW runN) := by
        rw [hRunX] at hXRel
        rw [show __eo_to_smt (Term.Binary runW runN) =
            SmtTerm.Binary runW runN by
          rfl] at hXRel
        rw [__smtx_model_eval.eq_5] at hXRel
        exact hXRel
      have hXEval :
          __smtx_model_eval M (__eo_to_smt x) =
            SmtValue.Binary runW runN :=
        smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt x)) runW runN hXRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.ubv_to_int (__eo_to_smt x)) =
            __smtx_model_eval_ubv_to_int
              (__smtx_model_eval M (__eo_to_smt x)) by
        rw [__smtx_model_eval.eq_131]]
      rw [hXEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral runN)
          (__smtx_model_eval M (SmtTerm.Numeral runN))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  all_goals
    rw [hRunX] at hRunXSmtTy
    simp at hRunXSmtTy

private theorem run_evaluate_sound_apply_ite_core
    (M : SmtModel) (hM : model_total_typed M)
    (c t e : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e) := by
  intro hATrans hEvalTy
  let whole :=
    Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e
  let runIte := __eo_ite (__run_evaluate c) (__run_evaluate t) (__run_evaluate e)
  have hIteNN :
      term_has_non_none_type
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation, whole] using hATrans
  rcases ite_args_of_non_none hIteNN with
    ⟨T, hCSmtBool, hTSmtTy, hESmtTy, hTNN⟩
  have hCTrans : RuleProofs.eo_has_smt_translation c := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hCSmtBool]
    simp
  have hTTrans : RuleProofs.eo_has_smt_translation t := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTSmtTy]
    exact hTNN
  have hETrans : RuleProofs.eo_has_smt_translation e := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hESmtTy]
    exact hTNN
  have hCMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation c hCTrans
  have hCEoBool : __eo_typeof c = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hCMatch.symm.trans hCSmtBool)
  have hWholeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation whole hATrans
  have hWholeTypeSmtNN :
      __eo_to_smt_type (__eo_typeof whole) ≠ SmtType.None := by
    rw [← hWholeMatch]
    exact hATrans
  have hWholeTypeNe : __eo_typeof whole ≠ Term.Stuck :=
    TranslationProofs.eo_term_ne_stuck_of_smt_type_non_none
      (__eo_typeof whole) hWholeTypeSmtNN
  have hOrigIteNe :
      __eo_typeof_ite (__eo_typeof c) (__eo_typeof t) (__eo_typeof e) ≠
        Term.Stuck := by
    simpa [whole] using hWholeTypeNe
  rcases eo_typeof_ite_args_of_ne_stuck
      (__eo_typeof c) (__eo_typeof t) (__eo_typeof e) hOrigIteNe with
    ⟨_hCType, hThenElseEoEq, hThenTypeNe⟩
  have hWholeTypeEqThen :
      __eo_typeof whole = __eo_typeof t := by
    change
      __eo_typeof_ite (__eo_typeof c) (__eo_typeof t) (__eo_typeof e) =
        __eo_typeof t
    rw [hCEoBool, ← hThenElseEoEq]
    exact eo_typeof_ite_bool_same_of_ne_stuck (__eo_typeof t) hThenTypeNe
  have hElseTypeNe : __eo_typeof e ≠ Term.Stuck := by
    rw [← hThenElseEoEq]
    exact hThenTypeNe
  have hRunIteNe : runIte ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq) whole) runIte) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq) whole) runIte ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runIte <;>
      simp [__eo_mk_apply, hRun] at hMk hRunIteNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) whole) runIte) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq) whole) runIte) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunIteEoType :
      __eo_typeof runIte = __eo_typeof whole := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq whole runIte hEvalEqTy
    exact hEq.symm
  rcases eo_ite_selected_type_of_typeof
      (__run_evaluate c) (__run_evaluate t) (__run_evaluate e)
      (__eo_typeof whole) hRunIteEoType hWholeTypeNe with
    ⟨runCond, hRunCond, hSelectedTy⟩
  have hRunCEoBool :
      __eo_typeof (__run_evaluate c) = Term.Bool := by
    rw [hRunCond]
    rfl
  have hCProgTy : __eo_typeof (__eo_prog_evaluate c) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool c
      (RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans)
      hCEoBool hRunCEoBool
  rcases (run_evaluate_rec_apply_apply_apply_arg1 M
      (Term.UOp UserOp.ite) c t e rec) hCTrans hCProgTy with
    ⟨_hCSameTy, hCRel⟩
  have hCRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt c))
        (SmtValue.Boolean runCond) := by
    rw [hRunCond] at hCRel
    simpa [__smtx_model_eval] using hCRel
  have hCEval :
      __smtx_model_eval M (__eo_to_smt c) =
        SmtValue.Boolean runCond :=
    smt_value_rel_boolean_eq
      (__smtx_model_eval M (__eo_to_smt c)) runCond hCRelValue
  cases runCond
  · have hRunEType :
        __eo_typeof (__run_evaluate e) = __eo_typeof e := by
      rw [hWholeTypeEqThen, hThenElseEoEq] at hSelectedTy
      exact hSelectedTy
    have hEProgTy : __eo_typeof (__eo_prog_evaluate e) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof e
        (__eo_typeof e)
        (RuleProofs.term_ne_stuck_of_has_smt_translation e hETrans)
        hElseTypeNe rfl hRunEType
    rcases (run_evaluate_rec_apply_apply_apply_arg3 M
        (Term.UOp UserOp.ite) c t e rec) hETrans hEProgTy with
      ⟨hESameTy, hERel⟩
    change
      __smtx_typeof
          (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) =
          __smtx_typeof (__eo_to_smt runIte) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)))
          (__smtx_model_eval M (__eo_to_smt runIte))
    dsimp [runIte]
    rw [hRunCond]
    constructor
    · change
        __smtx_typeof
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) =
          __smtx_typeof (__eo_to_smt (__run_evaluate e))
      calc
        __smtx_typeof
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) = T := by
          rw [typeof_ite_eq, hCSmtBool, hTSmtTy, hESmtTy]
          simp [__smtx_typeof_ite, native_ite, native_Teq]
        _ = __smtx_typeof (__eo_to_smt e) := hESmtTy.symm
        _ = __smtx_typeof (__eo_to_smt (__run_evaluate e)) := hESameTy
    · change
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_ite (Term.Boolean false) (__run_evaluate t)
                (__run_evaluate e))))
      simpa [__smtx_model_eval, __smtx_model_eval_ite, __eo_ite,
        native_ite, native_teq, hCEval] using hERel
  · have hRunTType :
        __eo_typeof (__run_evaluate t) = __eo_typeof t := by
      rw [hWholeTypeEqThen] at hSelectedTy
      exact hSelectedTy
    have hTProgTy : __eo_typeof (__eo_prog_evaluate t) = Term.Bool :=
      eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof t
        (__eo_typeof t)
        (RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans)
        hThenTypeNe rfl hRunTType
    rcases (run_evaluate_rec_apply_apply_apply_arg2 M
        (Term.UOp UserOp.ite) c t e rec) hTTrans hTProgTy with
      ⟨hTSameTy, hTRel⟩
    change
      __smtx_typeof
          (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) =
          __smtx_typeof (__eo_to_smt runIte) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)))
          (__smtx_model_eval M (__eo_to_smt runIte))
    dsimp [runIte]
    rw [hRunCond]
    constructor
    · change
        __smtx_typeof
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) =
          __smtx_typeof (__eo_to_smt (__run_evaluate t))
      calc
        __smtx_typeof
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) = T := by
          rw [typeof_ite_eq, hCSmtBool, hTSmtTy, hESmtTy]
          simp [__smtx_typeof_ite, native_ite, native_Teq]
        _ = __smtx_typeof (__eo_to_smt t) := hTSmtTy.symm
        _ = __smtx_typeof (__eo_to_smt (__run_evaluate t)) := hTSameTy
    · change
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_ite (Term.Boolean true) (__run_evaluate t)
                (__run_evaluate e))))
      simpa [__smtx_model_eval, __smtx_model_eval_ite, __eo_ite,
        native_ite, native_teq, hCEval] using hTRel

private theorem run_evaluate_sound_apply_int_to_bv_core
    (M : SmtModel) (hM : model_total_typed M)
    (n x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) x) := by
  intro hATrans hEvalTy
  have hIntToBvNN :
      term_has_non_none_type
        (SmtTerm.int_to_bv (__eo_to_smt n) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases int_to_bv_args_of_non_none hIntToBvNN with
    ⟨i, hnSmt, hxSmtTy, hi0⟩
  have hnTerm : n = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
  subst n
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxSmtTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hXMatch.symm.trans hxSmtTy)
  have hIntToBvEoType :
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral i) := by
    change
      __eo_typeof_int_to_bv (Term.UOp UserOp.Int) (Term.Numeral i)
          (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral i)
    rw [hXEoInt]
    rfl
  let runToBv := __eo_to_bin (Term.Numeral i) (__run_evaluate x)
  have hRunToBvNe : runToBv ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x))
            runToBv) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x))
          runToBv ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runToBv <;>
      simp [__eo_mk_apply, hRun] at hMk hRunToBvNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x))
            runToBv) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x))
            runToBv) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunToBvEoBv :
      __eo_typeof runToBv =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral i) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x)
        runToBv hEvalEqTy
    exact hEq.symm.trans hIntToBvEoType
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_smt_type_int x hXTrans hxSmtTy
  rcases run_evaluate_rec_apply_arg M
      (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x rec
      hXTrans hXProgTy with
    ⟨hXSameTy, hXRel⟩
  have hRunXSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate x)) = SmtType.Int := by
    rw [← hXSameTy]
    exact hxSmtTy
  cases hRunX : __run_evaluate x
  case Numeral runN =>
    have hRunToBvEq :
        runToBv =
          Term.Binary i (native_mod_total runN (native_int_pow2 i)) := by
      have hToBin :=
        eo_to_bin_numeral_eq_of_typeof_bitvec runN i i
          (by simpa [runToBv, hRunX] using hRunToBvEoBv)
      simpa [runToBv, hRunX] using hToBin
    change
      __smtx_typeof
          (SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt x)) =
          __smtx_typeof (__eo_to_smt runToBv) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt x)))
          (__smtx_model_eval M (__eo_to_smt runToBv))
    rw [hRunToBvEq]
    change
      __smtx_typeof
          (SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt x)) =
          __smtx_typeof
            (SmtTerm.Binary i
              (native_mod_total runN (native_int_pow2 i))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt x)))
          (__smtx_model_eval M
            (SmtTerm.Binary i
              (native_mod_total runN (native_int_pow2 i))))
    constructor
    · rw [typeof_int_to_bv_eq, hxSmtTy]
      simp [__smtx_typeof_int_to_bv, native_ite, hi0]
      rw [smtx_typeof_binary_mod_of_nonneg _ _ hi0]
    · have hXRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt x))
            (SmtValue.Numeral runN) := by
        rw [hRunX] at hXRel
        rw [show __eo_to_smt (Term.Numeral runN) =
            SmtTerm.Numeral runN by
          rfl] at hXRel
        rw [__smtx_model_eval.eq_2] at hXRel
        exact hXRel
      have hXEval :
          __smtx_model_eval M (__eo_to_smt x) =
            SmtValue.Numeral runN :=
        smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt x)) runN hXRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt x)) =
            __smtx_model_eval_int_to_bv
              (SmtValue.Numeral i)
              (__smtx_model_eval M (__eo_to_smt x)) by
        rw [__smtx_model_eval.eq_130, __smtx_model_eval.eq_2]]
      rw [hXEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Binary i
            (native_mod_total runN (native_int_pow2 i)))
          (__smtx_model_eval M
            (SmtTerm.Binary i
              (native_mod_total runN (native_int_pow2 i))))
      rw [__smtx_model_eval.eq_5]
      exact RuleProofs.smt_value_rel_refl _
  case Binary runW runN =>
    rw [hRunX] at hRunXSmtTy
    change __smtx_typeof (SmtTerm.Binary runW runN) = SmtType.Int at hRunXSmtTy
    unfold __smtx_typeof at hRunXSmtTy
    cases hOk :
        native_and (native_zleq 0 runW)
          (native_zeq runN (native_mod_total runN (native_int_pow2 runW))) <;>
      simp [hOk, native_ite] at hRunXSmtTy
  all_goals
    exfalso
    apply hRunToBvNe
    simp [runToBv, hRunX, __eo_to_bin]

private theorem run_evaluate_sound_apply_extract_core
    (M : SmtModel) (hM : model_total_typed M)
    (hi lo x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) := by
  intro hATrans hEvalTy
  have hExtNN :
      term_has_non_none_type
        (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases extract_args_of_non_none hExtNN with
    ⟨i, j, w, hHiSmt, hLoSmt, hxSmtTy, hj0, hji, hiw⟩
  have hHiTerm : hi = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral hi i hHiSmt
  have hLoTerm : lo = Term.Numeral j :=
    TranslationProofs.eo_to_smt_eq_numeral lo j hLoSmt
  subst hi
  subst lo
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxSmtTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXEoBv :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hXMatch.symm.trans hxSmtTy)
  have hjNonneg : 0 <= j := by
    simpa [native_zleq, SmtEval.native_zleq] using hj0
  have hLowSuccPos : native_zlt 0 (j + 1) = true := by
    have h : 0 < j + 1 := Int.lt_add_one_of_le hjNonneg
    simpa [native_zlt, SmtEval.native_zlt] using h
  have hWidthNonneg :
      native_zleq 0 (native_zplus (native_zplus i (native_zneg j)) 1) =
        true := by
    have hjiInt : j <= i := by
      simpa [native_zleq, SmtEval.native_zleq] using hji
    have hSub : 0 <= i + -j := by
      simpa [Int.sub_eq_add_neg] using (Int.sub_nonneg.mpr hjiInt)
    have hNonneg : 0 <= i + -j + 1 :=
      Int.add_nonneg hSub (by decide)
    simpa [native_zleq, SmtEval.native_zleq, native_zplus,
      SmtEval.native_zplus, native_zneg, SmtEval.native_zneg,
      Int.add_assoc] using hNonneg
  have hWidthAssoc :
      native_zplus (native_zplus i 1) (native_zneg j) =
        native_zplus (native_zplus i (native_zneg j)) 1 := by
    simp [native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg, Int.add_assoc, Int.add_comm, Int.add_left_comm]
  have hExtractEoType :
      __eo_typeof
          (Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j)) x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral
            (native_zplus (native_zplus i (native_zneg j)) 1)) := by
    change
      __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral i)
        (Term.UOp UserOp.Int) (Term.Numeral j) (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral
            (native_zplus (native_zplus i (native_zneg j)) 1))
    rw [hXEoBv]
    simp [__eo_typeof_extract, __eo_add, __eo_neg, __eo_gt, __eo_requires,
      __eo_mk_apply, hLowSuccPos, hiw, native_ite, native_teq,
      native_not, native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg]
  let runExt :=
    __eo_extract (__run_evaluate x) (Term.Numeral j) (Term.Numeral i)
  have hRunExtNe : runExt ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply
                (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j))
                x))
            runExt) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j))
              x))
          runExt ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runExt <;>
      simp [__eo_mk_apply, hRun] at hMk hRunExtNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply
                (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j))
                x))
            runExt) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply
                (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j))
                x))
            runExt) =
        Term.Bool at hEvalTy
    rw [evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunExtEoBv :
      __eo_typeof runExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral
            (native_zplus (native_zplus i (native_zneg j)) 1)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply
          (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j)) x)
        runExt hEvalEqTy
    exact hEq.symm.trans hExtractEoType
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_smt_type_bitvec x w hXTrans hxSmtTy
  rcases run_evaluate_rec_apply_arg M
      (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j)) x rec
      hXTrans hXProgTy with
    ⟨_hXSameTy, hXRel⟩
  rcases eo_extract_literal_arg_binary_of_typeof_bitvec
      (__run_evaluate x) i j
      (native_zplus (native_zplus i (native_zneg j)) 1)
      hj0 hji hRunExtEoBv with
    ⟨runW, runN, hRunX, _hWidthEq, hRunExtEq⟩
  have hRunExtEq' :
      runExt =
        Term.Binary (native_zplus (native_zplus i (native_zneg j)) 1)
          (native_mod_total (native_binary_extract runW runN i j)
            (native_int_pow2
              (native_zplus (native_zplus i (native_zneg j)) 1))) := by
    simpa [runExt] using hRunExtEq
  have hXRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt x))
        (SmtValue.Binary runW runN) := by
    rw [hRunX] at hXRel
    rw [show __eo_to_smt (Term.Binary runW runN) =
        SmtTerm.Binary runW runN by
      rfl] at hXRel
    rw [__smtx_model_eval.eq_5] at hXRel
    exact hXRel
  have hXEval :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary runW runN :=
    smt_value_rel_binary_eq
      (__smtx_model_eval M (__eo_to_smt x)) runW runN hXRelValue
  change
    __smtx_typeof
        (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral j)
          (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt runExt) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral j)
            (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt runExt))
  rw [hRunExtEq']
  change
    __smtx_typeof
        (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral j)
          (__eo_to_smt x)) =
        __smtx_typeof
          (SmtTerm.Binary
            (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract runW runN i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral j)
            (__eo_to_smt x)))
        (__smtx_model_eval M
          (SmtTerm.Binary
            (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract runW runN i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1)))))
  constructor
  · rw [typeof_extract_eq, hxSmtTy]
    simp [__smtx_typeof_extract, native_ite, hj0, hji, hiw]
    rw [smtx_typeof_binary_mod_of_nonneg _ _ hWidthNonneg]
  · rw [show
        __smtx_model_eval M
            (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral j)
              (__eo_to_smt x)) =
          __smtx_model_eval_extract
            (SmtValue.Numeral i) (SmtValue.Numeral j)
            (__smtx_model_eval M (__eo_to_smt x)) by
      rw [__smtx_model_eval.eq_36, __smtx_model_eval.eq_2,
        __smtx_model_eval.eq_2]]
    rw [hXEval]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary
          (native_zplus (native_zplus i 1) (native_zneg j))
          (native_mod_total (native_binary_extract runW runN i j)
            (native_int_pow2
              (native_zplus (native_zplus i 1) (native_zneg j)))))
        (__smtx_model_eval M
          (SmtTerm.Binary
            (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract runW runN i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1)))))
    rw [__smtx_model_eval.eq_5]
    rw [hWidthAssoc]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_active_apply_core
    (M : SmtModel) (hM : model_total_typed M)
    (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          RunEvaluateSoundGoal M A) :
  __run_evaluate (Term.Apply f x) ≠ Term.Apply f x ->
  RunEvaluateSoundGoal M (Term.Apply f x) := by
  intro hActive hATrans hEvalTy
  cases f with
  | UOp op =>
      match op with
      | UserOp.not =>
          exact run_evaluate_sound_apply_not_core M hM x rec hATrans hEvalTy
      | UserOp.bvnot =>
          exact run_evaluate_sound_apply_bvnot_core M hM x rec hATrans hEvalTy
      | UserOp.bvneg =>
          exact run_evaluate_sound_apply_bvneg_core M hM x rec hATrans hEvalTy
      | UserOp.__eoo_neg_2 =>
          exact run_evaluate_sound_apply_uneg_core M hM x rec hATrans hEvalTy
      | UserOp.abs =>
          exact run_evaluate_sound_apply_abs_core M hM x rec hATrans hEvalTy
      | UserOp.int_pow2 =>
          exact run_evaluate_sound_apply_int_pow2_core M hM x rec hATrans hEvalTy
      | UserOp.int_ispow2 =>
          exact run_evaluate_sound_apply_int_ispow2_core M hM x rec hATrans hEvalTy
      | UserOp._at_bvsize =>
          exact run_evaluate_sound_apply_at_bvsize_core M hM x rec hATrans hEvalTy
      | UserOp.str_to_lower =>
          exact run_evaluate_sound_apply_str_to_lower_core M hM x rec hATrans hEvalTy
      | UserOp.str_to_upper =>
          exact run_evaluate_sound_apply_str_to_upper_core M hM x rec hATrans hEvalTy
      | UserOp.str_rev =>
          exact run_evaluate_sound_apply_str_rev_core M hM x rec hATrans hEvalTy
      | UserOp.ubv_to_int =>
          exact run_evaluate_sound_apply_ubv_to_int_core M hM x rec hATrans hEvalTy
      | UserOp.bvnego =>
          exact False.elim (hActive rfl)
      | UserOp.bvredand =>
          exact False.elim (hActive rfl)
      | UserOp.bvredor =>
          exact False.elim (hActive rfl)
      | _ =>
          first
            | exact False.elim (hActive rfl)
            | sorry
  | UOp1 op a =>
      cases op
      case «repeat» =>
        exact run_evaluate_sound_apply_repeat_core M hM a x rec
          hATrans hEvalTy
      case zero_extend =>
        exact run_evaluate_sound_apply_zero_extend_core M hM a x rec
          hATrans hEvalTy
      case sign_extend =>
        exact run_evaluate_sound_apply_sign_extend_core M hM a x rec
          hATrans hEvalTy
      case int_to_bv =>
        exact run_evaluate_sound_apply_int_to_bv_core M hM a x rec
          hATrans hEvalTy
      all_goals
        exact False.elim (hActive rfl)
  | UOp2 op a b =>
      cases op
      case extract =>
        exact run_evaluate_sound_apply_extract_core M hM a b x rec
          hATrans hEvalTy
      all_goals
        exact False.elim (hActive rfl)
  | Apply g y =>
      cases g with
      | UOp op =>
          match op with
          | UserOp.and =>
              exact run_evaluate_sound_apply_and_core M hM y x rec hATrans hEvalTy
          | UserOp.or =>
              exact run_evaluate_sound_apply_or_core M hM y x rec hATrans hEvalTy
          | UserOp.imp =>
              exact run_evaluate_sound_apply_imp_core M hM y x rec hATrans hEvalTy
          | UserOp.xor =>
              exact run_evaluate_sound_apply_xor_core M hM y x rec hATrans hEvalTy
          | UserOp.str_concat =>
              exact run_evaluate_sound_apply_str_concat_core M hM y x rec hATrans hEvalTy
          | UserOp.plus =>
              exact run_evaluate_sound_apply_plus_core M hM y x rec hATrans hEvalTy
          | UserOp.neg =>
              exact run_evaluate_sound_apply_neg_core M hM y x rec hATrans hEvalTy
          | UserOp.mult =>
              exact run_evaluate_sound_apply_mult_core M hM y x rec hATrans hEvalTy
          | UserOp.div =>
              exact run_evaluate_sound_apply_div_core M hM y x rec hATrans hEvalTy
          | UserOp.mod =>
              exact run_evaluate_sound_apply_mod_core M hM y x rec hATrans hEvalTy
          | UserOp.div_total =>
              exact run_evaluate_sound_apply_div_total_core M hM y x rec hATrans hEvalTy
          | UserOp.mod_total =>
              exact run_evaluate_sound_apply_mod_total_core M hM y x rec hATrans hEvalTy
          | UserOp.bvand =>
              exact run_evaluate_sound_apply_bvand_core M hM y x rec hATrans hEvalTy
          | UserOp.bvor =>
              exact run_evaluate_sound_apply_bvor_core M hM y x rec hATrans hEvalTy
          | UserOp.bvxor =>
              exact run_evaluate_sound_apply_bvxor_core M hM y x rec hATrans hEvalTy
          | UserOp.bvadd =>
              exact run_evaluate_sound_apply_bvadd_core M hM y x rec hATrans hEvalTy
          | UserOp.bvmul =>
              exact run_evaluate_sound_apply_bvmul_core M hM y x rec hATrans hEvalTy
          | UserOp.bvsub =>
              exact run_evaluate_sound_apply_bvsub_core M hM y x rec hATrans hEvalTy
          | UserOp.bvsdiv =>
              exact False.elim (hActive rfl)
          | UserOp.bvsrem =>
              exact False.elim (hActive rfl)
          | UserOp.bvsmod =>
              exact False.elim (hActive rfl)
          | UserOp.bvnand =>
              exact False.elim (hActive rfl)
          | UserOp.bvnor =>
              exact False.elim (hActive rfl)
          | UserOp.bvxnor =>
              exact False.elim (hActive rfl)
          | UserOp.bvcomp =>
              exact False.elim (hActive rfl)
          | UserOp.bvuaddo =>
              exact False.elim (hActive rfl)
          | UserOp.bvsaddo =>
              exact False.elim (hActive rfl)
          | UserOp.bvumulo =>
              exact False.elim (hActive rfl)
          | UserOp.bvsmulo =>
              exact False.elim (hActive rfl)
          | UserOp.bvusubo =>
              exact False.elim (hActive rfl)
          | UserOp.bvssubo =>
              exact False.elim (hActive rfl)
          | UserOp.bvsdivo =>
              exact False.elim (hActive rfl)
          | UserOp.bvultbv =>
              exact False.elim (hActive rfl)
          | UserOp.bvsltbv =>
              exact False.elim (hActive rfl)
          | _ =>
              sorry
      | Apply h z =>
          cases h with
          | UOp op =>
              match op with
              | UserOp.ite =>
                  exact run_evaluate_sound_apply_ite_core M hM z y x rec
                    hATrans hEvalTy
              | _ =>
                  first
                    | exact False.elim (hActive rfl)
                    | sorry
          | _ =>
              exact False.elim (hActive rfl)
      | _ =>
          exact False.elim (hActive rfl)
  | _ =>
      exact False.elim (hActive rfl)

private theorem run_evaluate_sound_apply
    (M : SmtModel) (hM : model_total_typed M)
    (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply f x) := by
  intro hATrans hEvalTy
  by_cases hRun : __run_evaluate (Term.Apply f x) = Term.Apply f x
  · exact run_evaluate_sound_of_eq_self M _ hRun hATrans hEvalTy
  · exact run_evaluate_sound_active_apply_core M hM f x rec hRun hATrans hEvalTy

private theorem run_evaluate_sound_uop2_at_bv_core
    (M : SmtModel) (hM : model_total_typed M)
    (n m : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.UOp2 UserOp2._at_bv n m) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.UOp2 UserOp2._at_bv n m) := by
  intro hATrans hEvalTy
  have hTranslate :
      __eo_to_smt (Term.UOp2 UserOp2._at_bv n m) =
        __eo_to_smt__at_bv (__eo_to_smt n) (__eo_to_smt m) := by
    rfl
  have hAtNN :
      __smtx_typeof (__eo_to_smt__at_bv (__eo_to_smt n) (__eo_to_smt m)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation, hTranslate] using hATrans
  rcases TranslationProofs.eo_to_smt_at_bv_of_non_none hAtNN with
    ⟨value, width, hn, hm, hWidthNonneg, _hSmtAt⟩
  have hnTerm : n = Term.Numeral value :=
    TranslationProofs.eo_to_smt_eq_numeral n value hn
  have hmTerm : m = Term.Numeral width :=
    TranslationProofs.eo_to_smt_eq_numeral m width hm
  subst n
  subst m
  cases hBound : native_zleq width 4294967296
  · exfalso
    have hRunStuck :
        __run_evaluate
            (Term.UOp2 UserOp2._at_bv (Term.Numeral value)
              (Term.Numeral width)) =
          Term.Stuck := by
      simp [__run_evaluate, __eo_to_bin, hBound, native_ite]
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.UOp2 UserOp2._at_bv (Term.Numeral value)
                (Term.Numeral width)))
            (__run_evaluate
              (Term.UOp2 UserOp2._at_bv (Term.Numeral value)
                (Term.Numeral width)))) =
        Term.Bool at hEvalTy
    rw [hRunStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  · have hRun :
        __run_evaluate
            (Term.UOp2 UserOp2._at_bv (Term.Numeral value)
              (Term.Numeral width)) =
          Term.Binary width
            (native_mod_total value (native_int_pow2 width)) := by
      simp [__run_evaluate, __eo_to_bin, __eo_mk_binary, hWidthNonneg, hBound,
        native_ite]
    rw [hRun]
    change
      __smtx_typeof
          (__eo_to_smt__at_bv (SmtTerm.Numeral value)
            (SmtTerm.Numeral width)) =
          __smtx_typeof
            (SmtTerm.Binary width
              (native_mod_total value (native_int_pow2 width))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt__at_bv (SmtTerm.Numeral value)
              (SmtTerm.Numeral width)))
          (__smtx_model_eval M
            (SmtTerm.Binary width
              (native_mod_total value (native_int_pow2 width))))
    simp [__eo_to_smt__at_bv, hWidthNonneg, native_ite,
      RuleProofs.smt_value_rel_refl]

private theorem run_evaluate_sound_core
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ A : Term, RunEvaluateSoundGoal M A
  | Term.Apply f x =>
      run_evaluate_sound_apply M hM
        f x (fun A _hA => run_evaluate_sound_core M hM A)
  | Term.Stuck => by
      intro hATrans _hEvalTy
      exact False.elim
        (RuleProofs.term_ne_stuck_of_has_smt_translation _ hATrans rfl)
  | Term.UOp _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp1 _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2.extract _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_bv n m =>
      run_evaluate_sound_uop2_at_bv_core M hM
        n m (fun A _hA => run_evaluate_sound_core M hM A)
  | Term.UOp2 UserOp2.re_loop _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_quantifiers_skolemize _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_const _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp3 _ _ _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.__eo_List =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.__eo_List_nil =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.__eo_List_cons =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Bool =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Boolean _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Numeral _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Rational _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.String _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Binary _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Type =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.FunType =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Var _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.DatatypeType _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.DatatypeTypeRef _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.DtcAppType _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.DtCons _ _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.DtSel _ _ _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.USort _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UConst _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl

/--
Semantic soundness target for the generated evaluator.

The command-level `evaluate` rule is premise-free and emits
`A = __run_evaluate A`.  The large theorem to prove is that, whenever the
checker accepts that emitted equality as Boolean and the input term has an SMT
translation, `__run_evaluate A` has the same SMT type as `A` and evaluates to
the same SMT value.
-/
theorem run_evaluate_sound
    (M : SmtModel) (hM : model_total_typed M) (A : Term) :
  RuleProofs.eo_has_smt_translation A ->
  __eo_typeof (__eo_prog_evaluate A) = Term.Bool ->
  __smtx_typeof (__eo_to_smt A) =
      __smtx_typeof (__eo_to_smt (__run_evaluate A)) ∧
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt A))
      (__smtx_model_eval M (__eo_to_smt (__run_evaluate A))) :=
by
  exact run_evaluate_sound_core M hM A

theorem run_evaluate_properties
    (M : SmtModel) (hM : model_total_typed M) (A : Term) :
  RuleProofs.eo_has_smt_translation A ->
  __eo_typeof (__eo_prog_evaluate A) = Term.Bool ->
  StepRuleProperties M [] (__eo_prog_evaluate A) :=
by
  intro hATrans hEvalTy
  have hProg : __eo_prog_evaluate A ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hEvalTy
  have hProgEq := eo_prog_evaluate_eq_of_ne_stuck A hProg
  rcases run_evaluate_sound M hM A hATrans hEvalTy with
    ⟨hSameTy, hEvalRel⟩
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A)
          (__run_evaluate A)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type A (__run_evaluate A)
      hSameTy hATrans
  refine ⟨?_, ?_⟩
  · intro _hTrue
    rw [hProgEq]
    exact RuleProofs.eo_interprets_eq_of_rel M A (__run_evaluate A)
      hEqBool hEvalRel
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool

theorem cmd_step_evaluate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.evaluate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.evaluate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.evaluate args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.evaluate args premises ≠
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
              have hATransPair : eoHasSmtTranslation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                  using hATransPair.1
              have hEvalTy :
                  __eo_typeof (__eo_prog_evaluate a1) = Term.Bool := by
                change __eo_typeof (__eo_prog_evaluate a1) = Term.Bool
                  at hResultTy
                exact hResultTy
              simpa [premiseTermList] using
                run_evaluate_properties M hM a1 hATrans hEvalTy
