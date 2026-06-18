import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.RuleSupport.StringSupport
import Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-! ### Core math: two equal-length unequal lists differ at an in-bounds index. -/

private theorem list_diff_at_index :
    ∀ (xs ys : List SmtValue), xs.length = ys.length → xs ≠ ys →
      ∃ i : Nat, i < xs.length ∧ (xs.drop i).take 1 ≠ (ys.drop i).take 1
  | [], [], _, hne => absurd rfl hne
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, hne => by
      by_cases hxy : x = y
      · subst hxy
        have htl : xs ≠ ys := fun h => hne (by rw [h])
        have hlen' : xs.length = ys.length := by simpa using hlen
        obtain ⟨i, hi, hdiff⟩ := list_diff_at_index xs ys hlen' htl
        refine ⟨i + 1, ?_, ?_⟩
        · simpa using Nat.succ_lt_succ hi
        · simpa using hdiff
      · refine ⟨0, by simp, ?_⟩
        simp only [List.drop_zero, List.take_succ_cons, List.take_zero]
        intro h
        exact hxy (by simpa using h)

/-- For an in-bounds (Nat) index, `native_seq_extract` returns the length-1 slice there. -/
private theorem native_seq_extract_one_nat (xs : List SmtValue) (j : Nat)
    (hj : j < xs.length) :
    native_seq_extract xs (Int.ofNat j) 1 = (xs.drop j).take 1 := by
  have e1 : decide ((Int.ofNat j : native_Int) < 0) = false :=
    decide_eq_false (show ¬ ((j : Int) < 0) by omega)
  have e2 : decide ((1 : native_Int) ≤ 0) = false := by decide
  have e3 : decide ((Int.ofNat j : native_Int) ≥ Int.ofNat xs.length) = false :=
    decide_eq_false (show ¬ ((j : Int) ≥ (xs.length : Int)) by omega)
  have h1 : (1 : Int) ≤ (xs.length : Int) - (j : Int) := by omega
  have hmin : min (1 : native_Int) (Int.ofNat xs.length - Int.ofNat j) = 1 :=
    Int.min_eq_left h1
  have htn : (Int.ofNat j : native_Int).toNat = j := rfl
  have htake : (min (1 : native_Int) (Int.ofNat xs.length - Int.ofNat j)).toNat = 1 := by
    rw [hmin]; exact Int.toNat_one
  simp only [native_seq_extract]
  rw [e1, e2, e3, htake, htn]
  simp

/-- Out of bounds (negative or `≥ len`), `native_seq_extract` of length 1 is empty. -/
private theorem native_seq_extract_one_oob (xs : List SmtValue) (i : native_Int)
    (h : i < 0 ∨ i ≥ Int.ofNat xs.length) :
    native_seq_extract xs i 1 = [] := by
  simp only [native_seq_extract]
  split
  · rfl
  · rename_i hc
    exfalso
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
    obtain ⟨⟨hlt0, _⟩, hge⟩ := hc
    rcases h with h | h
    · exact hlt0 h
    · exact hge h

private theorem cmd_step_string_ext_one_eq
    (s : CState) (n : CIndex) :
    __eo_cmd_step_proven s CRule.string_ext CArgList.nil (CIndexList.cons n CIndexList.nil) =
      __eo_prog_string_ext (Proof.pf (__eo_state_proven_nth s n)) := by
  rfl

/-- From the deq_diff being Int-typed, extract equal Seq element types. -/
private theorem string_ext_deq_diff_int_imp_seq
    (a b : Term)
    (h : __eo_typeof__at_strings_deq_diff (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int) :
    ∃ A : Term, __eo_typeof a = Term.Apply (Term.UOp UserOp.Seq) A ∧
      __eo_typeof b = Term.Apply (Term.UOp UserOp.Seq) A := by
  cases hTA : __eo_typeof a with
  | Apply fA TA =>
    cases fA with
    | UOp opA =>
      cases opA with
      | Seq =>
        cases hTB : __eo_typeof b with
        | Apply fB TB =>
          cases fB with
          | UOp opB =>
            cases opB with
            | Seq =>
              rw [hTA, hTB] at h
              simp only [__eo_typeof__at_strings_deq_diff] at h
              have hEq : __eo_requires (__eo_eq TA TB) (Term.Boolean true)
                  (Term.UOp UserOp.Int) ≠ Term.Stuck := by
                rw [h]; simp
              have hBA : TB = TA :=
                RuleProofs.eq_of_requires_eq_true_not_stuck TA TB
                  (Term.UOp UserOp.Int) hEq
              subst TB
              exact ⟨TA, rfl, rfl⟩
            | _ => rw [hTA, hTB] at h; simp [__eo_typeof__at_strings_deq_diff] at h
          | _ => rw [hTA, hTB] at h; simp [__eo_typeof__at_strings_deq_diff] at h
        | _ => rw [hTA, hTB] at h; simp [__eo_typeof__at_strings_deq_diff] at h
      | _ => rw [hTA] at h; simp [__eo_typeof__at_strings_deq_diff] at h
    | _ => rw [hTA] at h; simp [__eo_typeof__at_strings_deq_diff] at h
  | _ => rw [hTA] at h; simp [__eo_typeof__at_strings_deq_diff] at h

private theorem eo_mk_apply_eq (x y : Term)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_mk_apply x y = Term.Apply x y := by
  cases x <;> cases y <;> simp_all [__eo_mk_apply]

private theorem eo_to_smt_stuck_none : __eo_to_smt Term.Stuck = SmtTerm.None := rfl

private theorem ne_stuck_of_smt_typeof_seq (t : Term) (As : SmtType)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Seq As) : t ≠ Term.Stuck := by
  intro hs
  rw [hs, eo_to_smt_stuck_none, TranslationProofs.smtx_typeof_none] at h
  cases h

/-- `__str_mk_ext_deq` is non-stuck only when its 4th arg is a `Seq` type. -/
private theorem str_mk_ext_deq_ne_stuck_imp_seq
    (a b k T : Term)
    (h : __str_mk_ext_deq a b k T ≠ Term.Stuck) :
    ∃ A : Term, T = Term.Apply (Term.UOp UserOp.Seq) A := by
  by_cases ha : a = Term.Stuck
  · subst a; simp [__str_mk_ext_deq] at h
  by_cases hb : b = Term.Stuck
  · subst b; simp [__str_mk_ext_deq, ha] at h
  by_cases hkS : k = Term.Stuck
  · subst k; simp [__str_mk_ext_deq, ha, hb] at h
  cases hT : T with
  | Apply fT TT =>
    cases fT with
    | UOp opT =>
      cases opT with
      | Seq => exact ⟨TT, rfl⟩
      | _ => simp [__str_mk_ext_deq, ha, hb, hkS, hT] at h
    | _ => simp [__str_mk_ext_deq, ha, hb, hkS, hT] at h
  | _ => simp [__str_mk_ext_deq, ha, hb, hkS, hT] at h

/-- The deq subterm of the `string_ext` conclusion. -/
private def stringExtDeq (a b A : Term) : Term :=
  __str_mk_ext_deq a b
    (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)
    (Term.Apply (Term.UOp UserOp.Seq) A)

/-- The first disjunct of the `string_ext` conclusion. -/
private def stringExtD1 (a b : Term) : Term :=
  Term.Apply Term.not
    (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.UOp UserOp.str_len) a))
      (Term.Apply (Term.UOp UserOp.str_len) b))

/-- The bounds conjunct of the `string_ext` conclusion. -/
private def stringExtBounds (a b : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.leq) (Term.Numeral 0))
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.lt)
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
          (Term.Apply (Term.UOp UserOp.str_len) a)))
      (Term.Boolean true))

/-- Explicit (mk_apply-resolved) form of the `string_ext` conclusion. -/
private theorem prog_string_ext_explicit
    (a b A : Term)
    (hATy : __eo_typeof a = Term.Apply (Term.UOp UserOp.Seq) A)
    (hDeqNeStuck : stringExtDeq a b A ≠ Term.Stuck) :
    __eo_prog_string_ext
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b))) =
      Term.Apply (Term.Apply (Term.UOp UserOp.or) (stringExtD1 a b))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.or)
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) (stringExtDeq a b A))
              (stringExtBounds a b)))
          (Term.Boolean false)) := by
  have hDeq' : __str_mk_ext_deq a b
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)
      (Term.Apply (Term.UOp UserOp.Seq) A) ≠ Term.Stuck := hDeqNeStuck
  simp only [__eo_prog_string_ext, stringExtD1, stringExtBounds, stringExtDeq]
  rw [hATy]
  rw [eo_mk_apply_eq (Term.UOp UserOp.and) _ (by simp) hDeq']
  rw [eo_mk_apply_eq (Term.Apply (Term.UOp UserOp.and)
      (__str_mk_ext_deq a b
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)
        (Term.Apply (Term.UOp UserOp.Seq) A))) _ (by simp) (by simp)]
  rw [eo_mk_apply_eq (Term.UOp UserOp.or) _ (by simp) (by simp)]
  rw [eo_mk_apply_eq _ (Term.Boolean false) (by simp) (by simp)]
  rw [eo_mk_apply_eq ((Term.UOp UserOp.or).Apply
      ((Term.UOp UserOp.not).Apply
        (((Term.UOp UserOp.eq).Apply ((Term.UOp UserOp.str_len).Apply a)).Apply
          ((Term.UOp UserOp.str_len).Apply b)))) _ (by simp) (by simp)]

/-- From the result being Bool, extract equal Seq element types for `a` and `b`. -/
private theorem string_ext_result_imp_seq_types
    (a b : Term)
    (hResultTy :
      __eo_typeof
          (__eo_prog_string_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool) :
    ∃ A : Term, __eo_typeof a = Term.Apply (Term.UOp UserOp.Seq) A ∧
      __eo_typeof b = Term.Apply (Term.UOp UserOp.Seq) A := by
  -- the conclusion is not Stuck, so the deq subterm is not Stuck
  have hConclNeStuck := term_ne_stuck_of_typeof_bool hResultTy
  -- the deq subterm
  have hDeqNeStuck0 :
      __str_mk_ext_deq a b
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)
        (__eo_typeof a) ≠ Term.Stuck := by
    intro hDeq
    apply hConclNeStuck
    simp only [__eo_prog_string_ext]
    rw [hDeq]
    simp [__eo_mk_apply]
  rcases str_mk_ext_deq_ne_stuck_imp_seq a b
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)
      (__eo_typeof a) hDeqNeStuck0 with ⟨A, hA⟩
  refine ⟨A, hA, ?_⟩
  have hDeqNeStuck : stringExtDeq a b A ≠ Term.Stuck := by
    rw [stringExtDeq, ← hA]; exact hDeqNeStuck0
  -- explicit form of the conclusion
  rw [prog_string_ext_explicit a b A hA hDeqNeStuck] at hResultTy
  -- reduce the typeof to its component form.
  change
    __eo_typeof_or
        (__eo_typeof_not
          (__eo_typeof_eq (__eo_typeof_str_len (__eo_typeof a))
            (__eo_typeof_str_len (__eo_typeof b))))
        (__eo_typeof_or
          (__eo_typeof_or (__eo_typeof (stringExtDeq a b A))
            (__eo_typeof_or
              (__eo_typeof_lt (Term.UOp UserOp.Int)
                (__eo_typeof__at_strings_deq_diff (__eo_typeof a) (__eo_typeof b)))
              (__eo_typeof_or
                (__eo_typeof_lt
                  (__eo_typeof__at_strings_deq_diff (__eo_typeof a) (__eo_typeof b))
                  (__eo_typeof_str_len (__eo_typeof a)))
                Term.Bool)))
          Term.Bool) =
      Term.Bool at hResultTy
  -- The `leq 0 k` component forces the deq_diff index to be Int.
  have hkInt : __eo_typeof__at_strings_deq_diff (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int := by
    rw [hA] at hResultTy ⊢
    -- if not Int, the `lt`/`leq` components are Stuck and the `or` is Stuck.
    cases hkc : __eo_typeof__at_strings_deq_diff (Term.Apply (Term.UOp UserOp.Seq) A)
        (__eo_typeof b) with
    | UOp op =>
      cases op with
      | Int => rfl
      | _ =>
        exfalso; rw [hkc] at hResultTy
        simp [__eo_typeof_or, __eo_typeof_or, __eo_typeof_lt, __eo_typeof_str_len,
          __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
          SmtEval.native_not, native_not] at hResultTy
    | _ =>
      exfalso; rw [hkc] at hResultTy
      simp [__eo_typeof_or, __eo_typeof_or, __eo_typeof_lt, __eo_typeof_str_len,
        __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
        SmtEval.native_not, native_not] at hResultTy
  rcases string_ext_deq_diff_int_imp_seq a b hkInt with ⟨A', hA'a, hA'b⟩
  rw [hA] at hA'a
  have : A' = A := by
    have := hA'a; simp at this; exact this.symm
  rw [this] at hA'b
  exact hA'b


/-- Bundle of EO/SMT typing facts for a `string_ext` instance. -/
private theorem string_ext_smt_types
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))
    (hResultTy :
      __eo_typeof
          (__eo_prog_string_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool) :
    ∃ A : Term,
      let As := __eo_to_smt_type A
      __eo_typeof a = Term.Apply (Term.UOp UserOp.Seq) A ∧
        __eo_typeof b = Term.Apply (Term.UOp UserOp.Seq) A ∧
        __smtx_typeof (__eo_to_smt a) = SmtType.Seq As ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Seq As ∧
        As ≠ SmtType.None ∧
        RuleProofs.eo_has_smt_translation a ∧
        RuleProofs.eo_has_smt_translation b := by
  rcases string_ext_result_imp_seq_types a b hResultTy with ⟨A, hATy, hBTy⟩
  have hEqBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq a) b) :=
    RuleProofs.eo_has_bool_type_not_arg _ hPremBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hEqBool with
    ⟨hSame, hANonNone⟩
  have hATrans : RuleProofs.eo_has_smt_translation a := hANonNone
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    rw [RuleProofs.eo_has_smt_translation]; rw [← hSame]; exact hANonNone
  have hSmtARaw :
      __smtx_typeof (__eo_to_smt a) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) A) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      a _ (__eo_to_smt a) rfl hATrans hATy
  have hSeqNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) A) ≠ SmtType.None := by
    rw [← hSmtARaw]; exact hATrans
  have hSeqTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) A) =
        SmtType.Seq (__eo_to_smt_type A) := by
    rw [TranslationProofs.eo_to_smt_type_seq] at hSeqNonNone ⊢
    generalize hAt : __eo_to_smt_type A = As at hSeqNonNone ⊢
    cases As <;> simp_all [__smtx_typeof_guard, native_ite, native_Teq]
  have hANonNone' : __eo_to_smt_type A ≠ SmtType.None := by
    intro hN
    rw [TranslationProofs.eo_to_smt_type_seq, hN] at hSeqNonNone
    simp [__smtx_typeof_guard, native_ite, native_Teq] at hSeqNonNone
  have hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type A) :=
    hSmtARaw.trans hSeqTy
  have hSmtB : __smtx_typeof (__eo_to_smt b) = SmtType.Seq (__eo_to_smt_type A) := by
    rw [← hSame]; exact hSmtA
  exact ⟨A, hATy, hBTy, hSmtA, hSmtB, hANonNone', hATrans, hBTrans⟩

/-- The SMT translation of the deq-diff index. -/
private theorem eo_to_smt_deq_diff_eq (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b) =
      SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int
        (SmtTerm.not
          (SmtTerm.eq
            (SmtTerm.str_substr (__eo_to_smt a) (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
              (SmtTerm.Numeral 1))
            (SmtTerm.str_substr (__eo_to_smt b) (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
              (SmtTerm.Numeral 1))))
        native_nat_zero := by
  rfl

/-- The deq-diff index translates to an `Int`-typed SMT term. -/
private theorem deq_diff_smt_typeof_int
    (a b : Term) (A : Term)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type A))
    (hSmtB : __smtx_typeof (__eo_to_smt b) = SmtType.Seq (__eo_to_smt_type A)) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) =
      SmtType.Int := by
  rw [eo_to_smt_deq_diff_eq, smtx_typeof_choice_nth_term_eq]
  have hVarInt :
      __smtx_typeof (SmtTerm.Var (native_string_lit "@x") SmtType.Int) = SmtType.Int := by
    rw [smtx_typeof_var_term_eq]; rfl
  have hNum1 : __smtx_typeof (SmtTerm.Numeral 1) = SmtType.Int := by rw [__smtx_typeof.eq_2]
  have hSub :
      __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt a)
          (SmtTerm.Var (native_string_lit "@x") SmtType.Int) (SmtTerm.Numeral 1)) =
        SmtType.Seq (__eo_to_smt_type A) := by
    rw [typeof_str_substr_eq, hSmtA, hVarInt, hNum1]; rfl
  have hSubB :
      __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt b)
          (SmtTerm.Var (native_string_lit "@x") SmtType.Int) (SmtTerm.Numeral 1)) =
        SmtType.Seq (__eo_to_smt_type A) := by
    rw [typeof_str_substr_eq, hSmtB, hVarInt, hNum1]; rfl
  have hBodyBool :
      __smtx_typeof
        (SmtTerm.not
          (SmtTerm.eq
            (SmtTerm.str_substr (__eo_to_smt a) (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
              (SmtTerm.Numeral 1))
            (SmtTerm.str_substr (__eo_to_smt b) (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
              (SmtTerm.Numeral 1)))) = SmtType.Bool := by
    rw [typeof_not_eq, typeof_eq_eq, hSub, hSubB]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
  simp only [__smtx_typeof_choice_nth, hBodyBool, native_Teq]
  rfl

/-- The SMT typeof of `str_len a` is `Int` when `a` is a sequence. -/
private theorem str_len_smt_typeof_int
    (a A : Term)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type A)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) a)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.str_len (__eo_to_smt a)) = SmtType.Int
  rw [typeof_str_len_eq, hSmtA]
  simp [__smtx_typeof_seq_op_1_ret]

/-- A `leq`/`lt` between two `Int`-typed terms is Boolean-typed. -/
private theorem eo_has_bool_type_leq_of_int_args
    (x y : Term)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y) := by
  rw [RuleProofs.eo_has_bool_type]
  change __smtx_typeof (SmtTerm.leq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
  rw [typeof_leq_eq, hX, hY]
  simp [__smtx_typeof_arith_overload_op_2_ret]

private theorem eo_has_bool_type_lt_of_int_args
    (x y : Term)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) := by
  rw [RuleProofs.eo_has_bool_type]
  change __smtx_typeof (SmtTerm.lt (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
  rw [typeof_lt_eq, hX, hY]
  simp [__smtx_typeof_arith_overload_op_2_ret]

/-- `Numeral n` has SMT type `Int`. -/
private theorem numeral_smt_typeof_int (n : native_Int) :
    __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Int
  rw [__smtx_typeof.eq_2]

/-- SMT typeof of `str_substr a k 1` is `Seq As` when `a : Seq As`. -/
private theorem str_substr_smt_typeof
    (a k : Term) (As : SmtType)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq As)
    (hSmtK : __smtx_typeof (__eo_to_smt k) = SmtType.Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) a) k)
            (Term.Numeral 1))) = SmtType.Seq As := by
  change __smtx_typeof (SmtTerm.str_substr (__eo_to_smt a) (__eo_to_smt k)
    (SmtTerm.Numeral 1)) = SmtType.Seq As
  rw [typeof_str_substr_eq, hSmtA, hSmtK]
  simp [__smtx_typeof_str_substr, __smtx_typeof]

/-- `Seq As` typeable means `As` is well-formed. -/
private theorem wf_elem_of_seq_typeof
    (a : Term) (As : SmtType)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq As) :
    __smtx_type_wf As = true := by
  have hNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type; rw [hSmtA]; simp
  have hWf : __smtx_type_wf (SmtType.Seq As) = true :=
    Smtm.smt_term_seq_type_wf_of_non_none (__eo_to_smt a) hNN hSmtA
  have hParts : native_inhabited_type As = true ∧
      __smtx_type_wf_rec As native_reflist_nil = true := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      SmtEval.native_and] using hWf
  cases As <;>
    simp_all [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      SmtEval.native_and, native_inhabited_type]

/-- SMT typeof of `seq_nth a k` is `As` when `a : Seq As`. -/
private theorem seq_nth_smt_typeof
    (a k : Term) (As : SmtType)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq As)
    (hSmtK : __smtx_typeof (__eo_to_smt k) = SmtType.Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) a) k)) = As := by
  change __smtx_typeof (SmtTerm.seq_nth (__eo_to_smt a) (__eo_to_smt k)) = As
  rw [typeof_seq_nth_eq, hSmtA, hSmtK]
  simp [__smtx_typeof_seq_nth, __smtx_typeof_guard_wf,
    wf_elem_of_seq_typeof a As hSmtA, native_ite]

/-- Reduce the deq subterm to its substr/seq_nth normal form. -/
private theorem stringExtDeq_eq (a b A : Term)
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    stringExtDeq a b A =
      if A = Term.UOp UserOp.Char then
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) a)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
              (Term.Numeral 1)))
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) b)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
              (Term.Numeral 1))))
      else
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) a)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) b)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))) := by
  unfold stringExtDeq __str_mk_ext_deq
  cases a with
  | Stuck => exact absurd rfl ha
  | _ =>
    cases b with
    | Stuck => exact absurd rfl hb
    | _ =>
      cases A with
      | UOp op =>
        cases op with
        | Char => simp
        | _ => simp [Term.UOp.injEq]
      | _ => simp
      all_goals simp

/-- The deq conjunct is Boolean-typed. -/
private theorem stringExtDeq_bool
    (a b A : Term)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type A))
    (hSmtB : __smtx_typeof (__eo_to_smt b) = SmtType.Seq (__eo_to_smt_type A))
    (hAsNonNone : __eo_to_smt_type A ≠ SmtType.None)
    (hKInt :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) =
        SmtType.Int) :
    RuleProofs.eo_has_bool_type (stringExtDeq a b A) := by
  have ha : a ≠ Term.Stuck := ne_stuck_of_smt_typeof_seq a _ hSmtA
  have hb : b ≠ Term.Stuck := ne_stuck_of_smt_typeof_seq b _ hSmtB
  rw [stringExtDeq_eq a b A ha hb]
  by_cases hChar : A = Term.UOp UserOp.Char
  · subst hChar
    simp only [if_pos rfl]
    apply RuleProofs.eo_has_bool_type_not_of_bool_arg
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [str_substr_smt_typeof a _ _ hSmtA hKInt,
        str_substr_smt_typeof b _ _ hSmtB hKInt]
    · rw [str_substr_smt_typeof a _ _ hSmtA hKInt]; simp
  · rw [if_neg hChar]
    apply RuleProofs.eo_has_bool_type_not_of_bool_arg
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [seq_nth_smt_typeof a _ _ hSmtA hKInt, seq_nth_smt_typeof b _ _ hSmtB hKInt]
    · rw [seq_nth_smt_typeof a _ _ hSmtA hKInt]; exact hAsNonNone

private theorem typed___eo_prog_string_ext_impl
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))
    (hResultTy :
      __eo_typeof
          (__eo_prog_string_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_string_ext
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) := by
  rcases string_ext_smt_types a b hPremBool hResultTy with
    ⟨A, hATy, hBTy, hSmtA, hSmtB, hAsNonNone, hATrans, hBTrans⟩
  -- common facts
  have hLenA : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) a)) =
      SmtType.Int := str_len_smt_typeof_int a A hSmtA
  have hLenB : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) b)) =
      SmtType.Int := str_len_smt_typeof_int b A hSmtB
  have hKInt :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) =
        SmtType.Int := deq_diff_smt_typeof_int a b A hSmtA hSmtB
  -- deq term is non-stuck
  have hDeqBool : RuleProofs.eo_has_bool_type (stringExtDeq a b A) :=
    stringExtDeq_bool a b A hSmtA hSmtB hAsNonNone hKInt
  have hDeqNeStuck : stringExtDeq a b A ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation _
      (RuleProofs.eo_has_smt_translation_of_has_bool_type _ hDeqBool)
  -- rewrite the conclusion to explicit form
  rw [prog_string_ext_explicit a b A hATy hDeqNeStuck]
  -- bool types of the pieces
  have hD1Bool : RuleProofs.eo_has_bool_type (stringExtD1 a b) := by
    apply RuleProofs.eo_has_bool_type_not_of_bool_arg
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLenA, hLenB]
    · rw [hLenA]; simp
  have hLeqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) (Term.Numeral 0))
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) :=
    eo_has_bool_type_leq_of_int_args _ _ (numeral_smt_typeof_int 0) hKInt
  have hLtBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.lt)
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
          (Term.Apply (Term.UOp UserOp.str_len) a)) :=
    eo_has_bool_type_lt_of_int_args _ _ hKInt hLenA
  have hBoundsBool : RuleProofs.eo_has_bool_type (stringExtBounds a b) := by
    unfold stringExtBounds
    apply RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hLeqBool
    apply RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hLtBool
    exact RuleProofs.eo_has_bool_type_true
  -- assemble
  apply RuleProofs.eo_has_bool_type_or_of_bool_args _ _ hD1Bool
  apply RuleProofs.eo_has_bool_type_or_of_bool_args
  · exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hDeqBool hBoundsBool
  · exact RuleProofs.eo_has_bool_type_false

/-- The chosen witness of a satisfiable choice body satisfies the body
    (copied from `Exists_string_length`). -/
private theorem native_eval_tchoice_body_true_of_exists
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (hSat : ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true) :
    __smtx_model_eval (native_model_push M s T
      (native_eval_tchoice M s T body)) body =
      SmtValue.Boolean true := by
  classical
  change
    __smtx_model_eval
      (native_model_push M s T
        (if hSat' : ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true then
          Classical.choose hSat'
        else if hTy : ∃ v : SmtValue, __smtx_typeof_value v = T ∧
            __smtx_value_canonical_bool v then
          Classical.choose hTy
        else SmtValue.NotValue)) body = SmtValue.Boolean true
  simp [hSat]
  exact (Classical.choose_spec hSat).2.2

private theorem facts___eo_prog_string_ext_impl
    (M : SmtModel) (hM : model_total_typed M) (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))
    (hResultTy :
      __eo_typeof
          (__eo_prog_string_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool)
    (hPremTrue :
      eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)) true) :
    eo_interprets M
      (__eo_prog_string_ext
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) true := by
  -- SOUNDNESS HOLDS; one architecture-level prerequisite blocks full closure (see the
  -- block comment above `cmd_step_string_ext_properties`).  The disjunction reduces to
  --   (or (not (= (str_len a) (str_len b))) (or (and deq-at-k bounds) false))
  -- with `k = @strings_deq_diff a b`.  When `len a = len b` and `a \u2260 b`, the choice body
  -- `not (= (str.substr a @x 1) (str.substr b @x 1))` is satisfiable (list_diff_at_index),
  -- so the chosen witness `k` makes the chars differ (deq-at-k) and lies in `[0, len a)`
  -- (native_seq_extract_one_oob: out-of-bounds slices are empty, hence equal -> body
  -- false).  The blocker: the body, evaluated under `native_model_push M "@x" Int v`,
  -- must agree with the conclusion's `str_substr`/`seq_nth`, evaluated under `M`.  That
  -- requires `@x` to be FRESH in `__eo_to_smt a` / `__eo_to_smt b`, i.e. premise
  -- closedness -- a hypothesis NOT threaded to this layer (it is the same gap as
  -- `re_unfold_pos`; closedness is established only for the final checker state).
  sorry


/-
`string_ext` IS sound and provable.  Soundness: the premise is `(not (= s t))`,
and the conclusion is

    (or (not (= (str_len s) (str_len t)))
        (and (deq-at-k s t) (and (0 <= k) (and (k < str_len s) true))))

where `k = @strings_deq_diff s t` translates (Spec.lean:360) to the Hilbert choice
`choice_nth "@x" Int (not (= (str.substr s @x 1) (str.substr t @x 1))) 0`.
If `len s ≠ len t` the first disjunct holds.  Otherwise `s ≠ t` with equal lengths,
so the lists differ at some in-bounds index (`list_diff_at_index`), hence the choice
body is satisfiable and `native_eval_tchoice_body_true_of_exists`
(Exists_string_length.lean) makes the chosen `k` satisfy the body, i.e. the chars at
`k` differ (deq-at-k).  The bounds `0 ≤ k < len s` follow because the body is FALSE
for any out-of-bounds index (`native_seq_extract_one_oob`: both length-1 substrings
are empty, hence equal), so the witness must be in range.

STATUS.  Everything below is fully proven EXCEPT one architecture-level prerequisite
inside `facts___eo_prog_string_ext_impl` (a single, documented `sorry`):
  • DONE: the math core (`list_diff_at_index`, `native_seq_extract_one_nat/_oob`),
    the full typing chain (`typed___eo_prog_string_ext_impl`, so both
    `eo_has_bool_type` and `has_smt_translation` of the conclusion), the choice
    soundness lemma (`native_eval_tchoice_body_true_of_exists`), and this entire
    case-analysis scaffold wiring the helpers.
  • REMAINING GAP (`@x`-FRESHNESS / premise closedness): the soundness argument
    relates the choice `body` — evaluated under `native_model_push M "@x" Int v` —
    to the conclusion's `str_substr s/t` — evaluated under `M`.  Reconciling them
    needs `eval (push M "@x" Int v) (smt s) = eval M (smt s)` (and likewise `t`),
    i.e. `@x` is not free in `__eo_to_smt s`/`t`.  That follows from premise
    closedness, but closedness is NOT threaded to the rule-property layer
    (`AllHaveBoolType`/`model_total_typed`/`cmdTranslationOk` carry typing+totality,
    not closedness; `__eo_state_is_closed` is established only for the FINAL checker
    state).  This is the SAME blocker as `re_unfold_pos`; closing it requires
    threading a `checkerClosedInvariant` through the soundness chain, after which
    `Closed.Support.smt_model_eval_eq_of_*closed* + model_agrees_on_globals_push`
    discharge the freshness equation.
-/
theorem cmd_step_string_ext_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_ext args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_ext args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_ext args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.string_ext args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n premises =>
          cases premises with
          | nil =>
              have hPremBoolState :
                  RuleProofs.eo_has_bool_type (__eo_state_proven_nth s n) :=
                hPremisesBool (__eo_state_proven_nth s n) (by simp [premiseTermList])
              cases hp : __eo_state_proven_nth s n with
              | Apply f pArg =>
                  cases f with
                  | UOp op =>
                      cases op with
                      | not =>
                          cases pArg with
                          | Apply fEq b =>
                              cases fEq with
                              | Apply gEq a =>
                                  cases gEq with
                                  | UOp opEq =>
                                      by_cases hOpEq : opEq = UserOp.eq
                                      · subst opEq
                                        have hPremBool :
                                            RuleProofs.eo_has_bool_type
                                              (Term.Apply Term.not
                                                (Term.Apply (Term.Apply Term.eq a) b)) := by
                                          simpa [hp] using hPremBoolState
                                        have hResultTyAB :
                                            __eo_typeof
                                                (__eo_prog_string_ext
                                                  (Proof.pf
                                                    (Term.Apply Term.not
                                                      (Term.Apply (Term.Apply Term.eq a) b)))) =
                                              Term.Bool := by
                                          simpa [cmd_step_string_ext_one_eq, hp] using hResultTy
                                        refine ⟨?_, ?_⟩
                                        · intro hPremTrue
                                          have hStatePremTrue :
                                              eo_interprets M (__eo_state_proven_nth s n) true :=
                                            hPremTrue (__eo_state_proven_nth s n)
                                              (by simp [premiseTermList])
                                          have hThisPremTrue :
                                              eo_interprets M
                                                (Term.Apply Term.not
                                                  (Term.Apply (Term.Apply Term.eq a) b)) true :=
                                            by simpa [hp] using hStatePremTrue
                                          simpa [cmd_step_string_ext_one_eq, hp] using
                                            facts___eo_prog_string_ext_impl M hM a b
                                              hPremBool hResultTyAB hThisPremTrue
                                        · simpa [cmd_step_string_ext_one_eq, hp] using
                                            RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                              (typed___eo_prog_string_ext_impl a b
                                                hPremBool hResultTyAB)
                                      · have hBad :
                                            __eo_cmd_step_proven s CRule.string_ext
                                                CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                              Term.Stuck := by
                                          rw [cmd_step_string_ext_one_eq, hp]
                                          simp [__eo_prog_string_ext, hOpEq]
                                        exact False.elim (hProg hBad)
                                  | _ =>
                                      have hBad :
                                          __eo_cmd_step_proven s CRule.string_ext
                                              CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                            Term.Stuck := by
                                        rw [cmd_step_string_ext_one_eq, hp]
                                        simp [__eo_prog_string_ext]
                                      exact False.elim (hProg hBad)
                              | _ =>
                                  have hBad :
                                      __eo_cmd_step_proven s CRule.string_ext
                                          CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                        Term.Stuck := by
                                    rw [cmd_step_string_ext_one_eq, hp]
                                    simp [__eo_prog_string_ext]
                                  exact False.elim (hProg hBad)
                          | _ =>
                              have hBad :
                                  __eo_cmd_step_proven s CRule.string_ext
                                      CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                    Term.Stuck := by
                                rw [cmd_step_string_ext_one_eq, hp]
                                simp [__eo_prog_string_ext]
                              exact False.elim (hProg hBad)
                      | _ =>
                          have hBad :
                              __eo_cmd_step_proven s CRule.string_ext
                                  CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                Term.Stuck := by
                            rw [cmd_step_string_ext_one_eq, hp]
                            simp [__eo_prog_string_ext]
                          exact False.elim (hProg hBad)
                  | _ =>
                      have hBad :
                          __eo_cmd_step_proven s CRule.string_ext
                              CArgList.nil (CIndexList.cons n CIndexList.nil) =
                            Term.Stuck := by
                        rw [cmd_step_string_ext_one_eq, hp]
                        simp [__eo_prog_string_ext]
                      exact False.elim (hProg hBad)
              | _ =>
                  have hBad :
                      __eo_cmd_step_proven s CRule.string_ext
                          CArgList.nil (CIndexList.cons n CIndexList.nil) =
                        Term.Stuck := by
                    rw [cmd_step_string_ext_one_eq, hp]
                    simp [__eo_prog_string_ext]
                  exact False.elim (hProg hBad)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
