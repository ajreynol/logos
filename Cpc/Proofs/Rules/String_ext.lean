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
      SmtTerm.seq_diff (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

/-- The deq-diff index translates to an `Int`-typed SMT term. -/
private theorem deq_diff_smt_typeof_int
    (a b : Term) (A : Term)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type A))
    (hSmtB : __smtx_typeof (__eo_to_smt b) = SmtType.Seq (__eo_to_smt_type A)) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) =
      SmtType.Int := by
  rw [eo_to_smt_deq_diff_eq, typeof_seq_diff_eq, hSmtA, hSmtB]
  simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq]

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

/-! ### Value-level semantics of `seq_diff` (the deq-diff index).

`@strings_deq_diff a b` translates (Spec.lean) to `SmtTerm.seq_diff (smt a) (smt b)`,
whose evaluation `native_eval_seq_diff_ssm` selects, via `Classical.choose`, some index
at which the two evaluated sequence VALUES disagree (counting a missing element past the
end of the shorter sequence as a disagreement), or `-1` when they are equal.  No model
push / fresh variable is involved, so the rule's soundness needs no premise-closedness
hypothesis.  The lemmas below characterise that index. -/

/-- `native_not (native_veq a b) = true` iff the two values differ. -/
private theorem native_not_veq_true_iff (a b : SmtValue) :
    SmtEval.native_not (native_veq a b) = true ↔ a ≠ b := by
  simp [SmtEval.native_not, native_veq, decide_eq_false_iff_not]

/-- Two equal-length unequal lists differ in their `getD` at some index. -/
private theorem getD_diff_of_ne (d : SmtValue) :
    ∀ xs ys : List SmtValue, xs.length = ys.length → xs ≠ ys →
      ∃ i, xs.getD i d ≠ ys.getD i d
  | [], [], _, hne => absurd rfl hne
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, hne => by
      by_cases hxy : x = y
      · subst hxy
        have htl : xs ≠ ys := fun h => hne (by rw [h])
        obtain ⟨i, hi⟩ := getD_diff_of_ne d xs ys (by simpa using hlen) htl
        exact ⟨i + 1, by simpa using hi⟩
      · exact ⟨0, by simpa using hxy⟩

/-- `getD` past the end of a list is the default. -/
private theorem getD_ge (d : SmtValue) (l : List SmtValue) (i : Nat)
    (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- For an in-bounds index, the length-1 slice is the singleton of that element. -/
private theorem take1_drop_eq (d : SmtValue) (l : List SmtValue) (j : Nat)
    (h : j < l.length) : (l.drop j).take 1 = [l.getD j d] := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons, List.take_zero,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/- Generic characterisation of the `seq_diff` choice, abstracting the (inaccessible,
macro-generated) recursive indexing function as `g`.  Given a differing `getD` index, the
result is `Numeral (Int.ofNat j)` for some index `j` at which the two sequences differ. -/
open Classical in
private theorem dite_seqdiff_spec (g : SmtSeq → Nat → SmtValue)
    (s1 s2 : SmtSeq)
    (hg : ∀ s i, g s i = (native_unpack_seq s).getD i SmtValue.NotValue)
    (hex : ∃ i, (native_unpack_seq s1).getD i SmtValue.NotValue
        ≠ (native_unpack_seq s2).getD i SmtValue.NotValue) :
    ∃ j : Nat,
      (if h : ∃ i, SmtEval.native_not (native_veq (g s1 i) (g s2 i)) = true
         then SmtValue.Numeral (Int.ofNat (Classical.choose h))
         else SmtValue.Numeral (-1))
        = SmtValue.Numeral (Int.ofNat j)
      ∧ (native_unpack_seq s1).getD j SmtValue.NotValue
          ≠ (native_unpack_seq s2).getD j SmtValue.NotValue := by
  have hex' : ∃ i, SmtEval.native_not (native_veq (g s1 i) (g s2 i)) = true := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by rw [native_not_veq_true_iff, hg, hg]; exact hi⟩
  rw [dif_pos hex']
  refine ⟨Classical.choose hex', rfl, ?_⟩
  have hspec := Classical.choose_spec hex'
  rw [native_not_veq_true_iff, hg, hg] at hspec
  exact hspec

/-- Evaluating `seq_diff` on two differing sequence values yields a `Numeral` index at
which the underlying lists differ.  The inaccessible recursive indexer is captured by
unification and shown equal to list `getD` by induction in place. -/
private theorem seq_diff_pick (s1 s2 : SmtSeq)
    (hex : ∃ i, (native_unpack_seq s1).getD i SmtValue.NotValue
        ≠ (native_unpack_seq s2).getD i SmtValue.NotValue) :
    ∃ j : Nat,
      __smtx_model_eval_seq_diff (SmtValue.Seq s1) (SmtValue.Seq s2)
        = SmtValue.Numeral (Int.ofNat j)
      ∧ (native_unpack_seq s1).getD j SmtValue.NotValue
          ≠ (native_unpack_seq s2).getD j SmtValue.NotValue := by
  simp only [__smtx_model_eval_seq_diff]
  refine dite_seqdiff_spec _ s1 s2 ?_ hex
  intro s i
  induction i generalizing s with
  | zero => cases s <;> rfl
  | succ n ih => cases s with
    | empty T => rfl
    | cons v vs => simpa using ih vs

/-- `seq.nth` on a value reduces to list `getD` at the (nonneg) index. -/
private theorem ssm_seq_nth_ofNat (d : SmtValue) :
    ∀ (s : SmtSeq) (j : Nat),
      __smtx_ssm_seq_nth s (Int.ofNat j) d = (native_unpack_seq s).getD j d
  | SmtSeq.empty T, j => by simp [__smtx_ssm_seq_nth, native_unpack_seq]
  | SmtSeq.cons v vs, 0 => by simp [__smtx_ssm_seq_nth, native_unpack_seq]
  | SmtSeq.cons v vs, (j + 1) => by
      have hne : (Int.ofNat (j + 1)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have hidx : native_zplus (Int.ofNat (j + 1)) (native_zneg 1) = Int.ofNat j := by
        simp only [native_zplus, native_zneg]; push_cast; ring
      have ih := ssm_seq_nth_ofNat d vs j
      simp [__smtx_ssm_seq_nth, hne, hidx, ih, native_unpack_seq, List.getD_cons_succ]

/-- In bounds, `getD` does not depend on the default. -/
private theorem getD_lt_eq (d d' : SmtValue) (l : List SmtValue) (j : Nat)
    (h : j < l.length) : l.getD j d = l.getD j d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h, Option.getD_some, Option.getD_some]

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
  rcases string_ext_smt_types a b hPremBool hResultTy with
    \u27e8A, hATy, hBTy, hSmtA, hSmtB, hAsNonNone, hATrans, hBTrans\u27e9
  -- canonical evaluations of `a` and `b`
  have hAvalTy : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
      SmtType.Seq (__eo_to_smt_type A) :=
    smt_model_eval_preserves_type M hM (__eo_to_smt a) (SmtType.Seq (__eo_to_smt_type A))
      hSmtA (seq_ne_none _) (type_inhabited_seq _)
  have hBvalTy : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) =
      SmtType.Seq (__eo_to_smt_type A) :=
    smt_model_eval_preserves_type M hM (__eo_to_smt b) (SmtType.Seq (__eo_to_smt_type A))
      hSmtB (seq_ne_none _) (type_inhabited_seq _)
  rcases seq_value_canonical hAvalTy with \u27e8s1, hAEval\u27e9
  rcases seq_value_canonical hBvalTy with \u27e8s2, hBEval\u27e9
  have hElem1 : __smtx_elem_typeof_seq_value s1 = __eo_to_smt_type A :=
    elem_typeof_seq_value_of_typeof_seq_value
      (by simpa [hAEval, __smtx_typeof_value] using hAvalTy)
  have hElem2 : __smtx_elem_typeof_seq_value s2 = __eo_to_smt_type A :=
    elem_typeof_seq_value_of_typeof_seq_value
      (by simpa [hBEval, __smtx_typeof_value] using hBvalTy)
  -- typing facts of the conclusion's components (mirroring the typing lemma)
  have hKInt :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) =
        SmtType.Int := deq_diff_smt_typeof_int a b A hSmtA hSmtB
  have hDeqBool : RuleProofs.eo_has_bool_type (stringExtDeq a b A) :=
    stringExtDeq_bool a b A hSmtA hSmtB hAsNonNone hKInt
  have hDeqNeStuck : stringExtDeq a b A \u2260 Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation _
      (RuleProofs.eo_has_smt_translation_of_has_bool_type _ hDeqBool)
  have hLenA : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) a)) =
      SmtType.Int := str_len_smt_typeof_int a A hSmtA
  have hD1Bool : RuleProofs.eo_has_bool_type (stringExtD1 a b) := by
    apply RuleProofs.eo_has_bool_type_not_of_bool_arg
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    \u00b7 rw [hLenA, str_len_smt_typeof_int b A hSmtB]
    \u00b7 rw [hLenA]; simp
  have hBoundsBool : RuleProofs.eo_has_bool_type (stringExtBounds a b) := by
    unfold stringExtBounds
    apply RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      (eo_has_bool_type_leq_of_int_args _ _ (numeral_smt_typeof_int 0) hKInt)
    apply RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      (eo_has_bool_type_lt_of_int_args _ _ hKInt hLenA)
    exact RuleProofs.eo_has_bool_type_true
  have hRHSBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.or)
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) (stringExtDeq a b A))
              (stringExtBounds a b)))
          (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args _ _
      (RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hDeqBool hBoundsBool)
      RuleProofs.eo_has_bool_type_false
  -- the premise `(not (= a b))` forces the two sequence values to differ
  have hABne : SmtValue.Seq s1 \u2260 SmtValue.Seq s2 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremTrue
    cases hPremTrue with
    | intro_true _ hEval =>
        have hEval' :
            __smtx_model_eval_not
              (__smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b))) = SmtValue.Boolean true := hEval
        rw [hAEval, hBEval] at hEval'
        intro hEq
        rw [hEq] at hEval'
        simp [__smtx_model_eval_eq, __smtx_model_eval_not, native_veq,
          SmtEval.native_not] at hEval'
  -- rewrite the conclusion to its explicit disjunction form
  rw [prog_string_ext_explicit a b A hATy hDeqNeStuck]
  by_cases hLen : (native_unpack_seq s1).length = (native_unpack_seq s2).length
  \u00b7 -- equal lengths: establish the second disjunct
    have hxsne : native_unpack_seq s1 \u2260 native_unpack_seq s2 := by
      intro hEq
      apply hABne
      rw [\u2190 native_pack_unpack_seq s1, \u2190 native_pack_unpack_seq s2, hElem1, hElem2, hEq]
    obtain \u27e8i0, hi0\u27e9 := getD_diff_of_ne SmtValue.NotValue _ _ hLen hxsne
    obtain \u27e8j, hKval0, hjDiff\u27e9 := seq_diff_pick s1 s2 \u27e8i0, hi0\u27e9
    have hjLt : j < (native_unpack_seq s1).length := by
      by_contra hge
      push_neg at hge
      exact hjDiff (by rw [getD_ge _ _ _ hge, getD_ge _ _ _ (hLen \u25b8 hge)])
    have hjLt2 : j < (native_unpack_seq s2).length := hLen \u25b8 hjLt
    have hKEval :
        __smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
          = SmtValue.Numeral (Int.ofNat j) := by
      rw [eo_to_smt_deq_diff_eq]
      show __smtx_model_eval_seq_diff (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b)) = _
      rw [hAEval, hBEval, hKval0]
    apply RuleProofs.eo_interprets_or_right_intro M hM _ _ hD1Bool
    apply RuleProofs.eo_interprets_or_left_intro M hM _ _ _
      RuleProofs.eo_has_bool_type_false
    apply RuleProofs.eo_interprets_and_intro
    \u00b7 -- the deq conjunct: the elements at index `j` differ
      apply RuleProofs.eo_interprets_of_bool_eval M _ true hDeqBool
      rw [stringExtDeq_eq a b A
        (ne_stuck_of_smt_typeof_seq a _ hSmtA) (ne_stuck_of_smt_typeof_seq b _ hSmtB)]
      by_cases hChar : A = Term.UOp UserOp.Char
      \u00b7 rw [if_pos hChar]
        show __smtx_model_eval_not
          (__smtx_model_eval_eq
            (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))
              (SmtValue.Numeral 1))
            (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))
              (SmtValue.Numeral 1))) = SmtValue.Boolean true
        rw [hAEval, hBEval, hKEval]
        have hne :
            SmtValue.Seq (native_pack_seq (__eo_to_smt_type A)
                ((native_unpack_seq s1).drop j |>.take 1))
              \u2260 SmtValue.Seq (native_pack_seq (__eo_to_smt_type A)
                ((native_unpack_seq s2).drop j |>.take 1)) := by
          rw [take1_drop_eq SmtValue.NotValue _ _ hjLt,
            take1_drop_eq SmtValue.NotValue _ _ hjLt2]
          intro h
          exact hjDiff (by simpa using native_pack_seq_inj _ (by injection h))
        simp only [__smtx_model_eval_str_substr, hElem1, hElem2,
          native_seq_extract_one_nat _ _ hjLt, native_seq_extract_one_nat _ _ hjLt2,
          __smtx_model_eval_eq, __smtx_model_eval_not, native_veq,
          decide_eq_false hne, SmtEval.native_not, Bool.not_false]
      \u00b7 rw [if_neg hChar]
        show __smtx_model_eval_not
          (__smtx_model_eval_eq
            (__smtx_seq_nth M (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))))
            (__smtx_seq_nth M (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))))
          = SmtValue.Boolean true
        rw [hAEval, hBEval, hKEval]
        have hnth1 : __smtx_seq_nth M (SmtValue.Seq s1) (SmtValue.Numeral (Int.ofNat j))
            = (native_unpack_seq s1).getD j SmtValue.NotValue := by
          rw [__smtx_seq_nth, ssm_seq_nth_ofNat]; exact getD_lt_eq _ _ _ _ hjLt
        have hnth2 : __smtx_seq_nth M (SmtValue.Seq s2) (SmtValue.Numeral (Int.ofNat j))
            = (native_unpack_seq s2).getD j SmtValue.NotValue := by
          rw [__smtx_seq_nth, ssm_seq_nth_ofNat]; exact getD_lt_eq _ _ _ _ hjLt2
        rw [hnth1, hnth2]
        simp only [__smtx_model_eval_eq, __smtx_model_eval_not, native_veq,
          decide_eq_false hjDiff, SmtEval.native_not, Bool.not_false]
    \u00b7 -- the bounds conjunct: `0 \u2264 j < len a`
      unfold stringExtBounds
      apply RuleProofs.eo_interprets_and_intro
      \u00b7 apply RuleProofs.eo_interprets_of_bool_eval M _ true
          (eo_has_bool_type_leq_of_int_args _ _ (numeral_smt_typeof_int 0) hKInt)
        show __smtx_model_eval_leq (SmtValue.Numeral 0)
            (__smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))
            = SmtValue.Boolean true
        rw [hKEval]
        simp only [__smtx_model_eval_leq, native_zleq,
          decide_eq_true (by positivity : (0 : native_Int) \u2264 Int.ofNat j)]
      \u00b7 apply RuleProofs.eo_interprets_and_intro
        \u00b7 apply RuleProofs.eo_interprets_of_bool_eval M _ true
            (eo_has_bool_type_lt_of_int_args _ _ hKInt hLenA)
          show __smtx_model_eval_lt
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))
              (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt a)))
              = SmtValue.Boolean true
          rw [hKEval, hAEval]
          have hlt : (Int.ofNat j) < native_seq_len (native_unpack_seq s1) := by
            rw [native_seq_len]; exact_mod_cast hjLt
          simp only [__smtx_model_eval_str_len, __smtx_model_eval_lt, native_zlt,
            decide_eq_true hlt]
        \u00b7 exact RuleProofs.eo_interprets_true M
  \u00b7 -- unequal lengths: establish the first disjunct
    apply RuleProofs.eo_interprets_or_left_intro M hM _ _ _ hRHSBool
    apply RuleProofs.eo_interprets_of_bool_eval M _ true hD1Bool
    show __smtx_model_eval_not
      (__smtx_model_eval_eq
        (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt a)))
        (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt b))))
      = SmtValue.Boolean true
    rw [hAEval, hBEval]
    have hne : SmtValue.Numeral (native_seq_len (native_unpack_seq s1))
        \u2260 SmtValue.Numeral (native_seq_len (native_unpack_seq s2)) := by
      rw [native_seq_len, native_seq_len]
      intro h
      exact hLen (by exact_mod_cast (SmtValue.Numeral.inj h))
    simp only [__smtx_model_eval_str_len, __smtx_model_eval_eq, native_veq,
      decide_eq_false hne, __smtx_model_eval_not, SmtEval.native_not, Bool.not_false]


/-
`string_ext` is sound and fully proven.  The premise is `(not (= a b))` and the
conclusion is

    (or (not (= (str_len a) (str_len b)))
        (or (and (deq-at-k a b) (and (0 <= k) (and (k < str_len a) true))) false))

where `k = @strings_deq_diff a b` translates (Spec.lean) to `seq_diff (smt a) (smt b)`,
whose evaluation directly selects (via `Classical.choose`) some index at which the two
already-evaluated sequence VALUES disagree, or `-1` when equal.  No model push / fresh
variable is involved, so no premise-closedness hypothesis is needed.

Proof (`facts___eo_prog_string_ext_impl`): the premise makes the evaluated values
`a, b` differ.  If their lengths differ, the first disjunct `(not (= (str_len a)
(str_len b)))` holds.  Otherwise the underlying lists differ at some index
(`getD_diff_of_ne`), so `seq_diff` (`seq_diff_pick`) returns an index `j` at which the
elements differ; `j` is in bounds (`getD_ge`), giving the deq conjunct (chars/elements
at `j` differ) and the bounds `0 ≤ j < len a`.
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
