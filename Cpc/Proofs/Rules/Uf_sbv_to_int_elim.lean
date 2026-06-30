import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.TypePreservation.BitVec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

/-! ## Term abbreviations -/

private abbrev sbvToIntTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.sbv_to_int) t

private abbrev ubvToIntTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.ubv_to_int) t

private abbrev extractTerm (hi lo t : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract hi lo) t

private abbrev bvOneZeroTerm : Term :=
  Term.UOp2 UserOp2._at_bv (Term.Numeral 0) (Term.Numeral 1)

private abbrev negTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y

private abbrev eqTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev iteTerm (c a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) a) b

private abbrev bvsizeTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_bvsize) t

private abbrev intPow2Term (w : Term) : Term :=
  Term.Apply (Term.UOp UserOp.int_pow2) w

/-- The body of the rule's conclusion (the equation proven by the rule). -/
private abbrev ufSbvToIntElimBody (t wm n : Term) : Term :=
  eqTerm (sbvToIntTerm t)
    (iteTerm (eqTerm (extractTerm wm wm t) bvOneZeroTerm)
      (ubvToIntTerm t)
      (negTerm (ubvToIntTerm t) n))

/-! ## Program reduction and guard handling -/

/-- When all args are non-stuck and both premises have the expected shape, the
    program reduces to the requires-guarded conclusion. -/
private theorem prog_uf_sbv_to_int_elim_eq
    (t wm n wm2 t2 n2 t3 : Term)
    (hT : t ≠ Term.Stuck) (hWm : wm ≠ Term.Stuck) (hN : n ≠ Term.Stuck) :
    __eo_prog_uf_sbv_to_int_elim t wm n
      (Proof.pf (eqTerm wm2 (negTerm (bvsizeTerm t2) (Term.Numeral 1))))
      (Proof.pf (eqTerm n2 (intPow2Term (bvsizeTerm t3)))) =
      __eo_requires
        (__eo_and
          (__eo_and (__eo_and (__eo_eq wm wm2) (__eo_eq t t2)) (__eo_eq n n2))
          (__eo_eq t t3))
        (Term.Boolean true) (ufSbvToIntElimBody t wm n) := by
  unfold __eo_prog_uf_sbv_to_int_elim
  split
  · exact absurd rfl hT
  · exact absurd rfl hWm
  · exact absurd rfl hN
  · rename_i heq1 heq2
    injection heq1 with heq1
    injection heq2 with heq2
    simp only [eqTerm, negTerm, bvsizeTerm, intPow2Term,
      Term.Apply.injEq, true_and, and_true] at heq1 heq2
    obtain ⟨hwm2, ht2⟩ := heq1
    obtain ⟨hn2, ht3⟩ := heq2
    subst hwm2; subst ht2; subst hn2; subst ht3
    rfl
  · rename_i hcontra
    exact (hcontra wm2 t2 n2 t3 rfl rfl).elim

/-- A non-stuck program forces all three args to be non-stuck. -/
private theorem args_ne_stuck_of_prog_not_stuck
    (t wm n p1 p2 : Term)
    (h : __eo_prog_uf_sbv_to_int_elim t wm n (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck) :
    t ≠ Term.Stuck ∧ wm ≠ Term.Stuck ∧ n ≠ Term.Stuck := by
  refine ⟨?_, ?_, ?_⟩
  · intro hT; subst t; simp [__eo_prog_uf_sbv_to_int_elim] at h
  · intro hWm; subst wm; cases t <;> simp [__eo_prog_uf_sbv_to_int_elim] at h
  · intro hN; subst n
    cases t <;> cases wm <;> simp [__eo_prog_uf_sbv_to_int_elim] at h

/-- A non-stuck program forces both premises to be equalities of the expected
    shape. -/
private theorem shape_of_prog_uf_sbv_to_int_elim_not_stuck
    (t wm n p1 p2 : Term)
    (hT : t ≠ Term.Stuck) (hWm : wm ≠ Term.Stuck) (hN : n ≠ Term.Stuck)
    (h : __eo_prog_uf_sbv_to_int_elim t wm n (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck) :
    ∃ wm2 t2 n2 t3 : Term,
      p1 = eqTerm wm2 (negTerm (bvsizeTerm t2) (Term.Numeral 1)) ∧
      p2 = eqTerm n2 (intPow2Term (bvsizeTerm t3)) := by
  unfold __eo_prog_uf_sbv_to_int_elim at h
  split at h
  · exact absurd rfl hT
  · exact absurd rfl hWm
  · exact absurd rfl hN
  · rename_i lwm lt2 ln lt3 _ _ _ heq1 heq2
    injection heq1 with heq1
    injection heq2 with heq2
    exact ⟨lwm, lt2, ln, lt3, heq1, heq2⟩
  · exact absurd rfl h

private theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x; simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y; simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

/-- Stuck-or-Boolean dichotomy for `__eo_eq`. -/
private theorem eo_eq_stuck_or_bool (a b : Term) :
    __eo_eq a b = Term.Stuck ∨
      ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
  by_cases ha : a = Term.Stuck
  · subst a; exact Or.inl (by simp [__eo_eq])
  · by_cases hb : b = Term.Stuck
    · subst b; exact Or.inl (by simp [__eo_eq])
    · exact Or.inr ⟨native_teq b a, by simp [__eo_eq]⟩

/-- From the four-way conjunction guard being non-stuck, recover the four
    equalities. -/
private theorem eqs_of_requires_and4_eq_true_not_stuck
    (x1 x2 y1 y2 z1 z2 w1 w2 B : Term) :
    __eo_requires
        (__eo_and
          (__eo_and (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2)) (__eo_eq z1 z2))
          (__eo_eq w1 w2))
        (Term.Boolean true) B ≠ Term.Stuck ->
    x2 = x1 ∧ y2 = y1 ∧ z2 = z1 ∧ w2 = w1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hProg'
  have hAnd :
      __eo_and
        (__eo_and (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2)) (__eo_eq z1 z2))
        (__eo_eq w1 w2) = Term.Boolean true := hProg'.1
  -- Each leaf must be `Boolean true`.
  rcases eo_eq_stuck_or_bool x1 x2 with hX | ⟨bx, hX⟩
  · simp [__eo_and, hX] at hAnd
  rcases eo_eq_stuck_or_bool y1 y2 with hY | ⟨by1, hY⟩
  · simp [__eo_and, hX, hY] at hAnd
  rcases eo_eq_stuck_or_bool z1 z2 with hZ | ⟨bz, hZ⟩
  · simp [__eo_and, hX, hY, hZ] at hAnd
  rcases eo_eq_stuck_or_bool w1 w2 with hW | ⟨bw, hW⟩
  · simp [__eo_and, hX, hY, hZ, hW] at hAnd
  cases bx <;> cases by1 <;> cases bz <;> cases bw <;>
    simp [__eo_and, hX, hY, hZ, hW, native_and] at hAnd
  exact ⟨eq_of_eo_eq_true x1 x2 hX, eq_of_eo_eq_true y1 y2 hY,
    eq_of_eo_eq_true z1 z2 hZ, eq_of_eo_eq_true w1 w2 hW⟩

/-- Discharge the guard when all leaves are reflexive. -/
private theorem requires_and4_eq_self_true_body
    (t wm n body : Term)
    (hT : t ≠ Term.Stuck) (hWm : wm ≠ Term.Stuck) (hN : n ≠ Term.Stuck) :
    __eo_requires
        (__eo_and
          (__eo_and (__eo_and (__eo_eq wm wm) (__eo_eq t t)) (__eo_eq n n))
          (__eo_eq t t))
        (Term.Boolean true) body = body := by
  simp [__eo_requires, __eo_and,
    eo_eq_self_true_of_ne_stuck wm hWm, eo_eq_self_true_of_ne_stuck t hT,
    eo_eq_self_true_of_ne_stuck n hN, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and]

/-! ## SMT-level facts -/

/-- Stable rewrite for typing SMT signed bit-vector-to-int terms. -/
private theorem smtx_typeof_sbv_to_int_term_eq (x : SmtTerm) :
    __smtx_typeof (SmtTerm.sbv_to_int x) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof x) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_int_pow2_term_eq (x : SmtTerm) :
    __smtx_typeof (SmtTerm.int_pow2 x) = SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- From an EO bit-vector type with a numeral width, get the SMT type. -/
private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x1 : Term) (w : native_Int) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    native_zleq 0 w = true ∧
      __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat w) := by
  intro hX1Trans hX1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type
          (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
      (__eo_to_smt x1) rfl hX1Trans hX1Type
  cases hNonneg : native_zleq 0 w <;>
    simp [__eo_to_smt_type, hNonneg] at hSmtType
  · exact False.elim (hX1Trans hSmtType)
  · exact ⟨rfl, hSmtType⟩

/-! ## The crux arithmetic: `native_binary_uts` versus the sign bit -/

private theorem native_int_pow2_pos_of_nonneg
    {w : native_Int} (hw : 0 <= w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [native_int_pow2, native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

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
  rw [native_int_pow2, native_int_pow2, native_zexp_total, native_zexp_total]
  simp [hnotW, hnotP]
  rw [hNat]
  have hSub : (w - 1).toNat + 1 - 1 = (w - 1).toNat :=
    Nat.add_sub_cancel (w - 1).toNat 1
  rw [hSub]
  rw [← Nat.succ_eq_add_one]
  rw [Int.pow_succ]
  rw [Int.mul_comm]

/--
The key arithmetic lemma.  For a payload `n` canonical for width `w` (so
`0 <= n < 2^w`), let `q := n / 2^(w-1)` be the sign bit.  Then:
* `q = 0` exactly when `native_binary_uts w n = n`, and
* `q = 1` exactly when `native_binary_uts w n = n - 2^w`.

We return the value of `q` together with both arithmetic identities.
-/
private theorem sign_bit_and_uts_of_canonical
    {w n : native_Int}
    (hwpos : 0 < w)
    (hCanon :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    (native_div_total n (native_int_pow2 (w - 1)) = 0 ∧
        native_binary_uts w n = n) ∨
      (native_div_total n (native_int_pow2 (w - 1)) = 1 ∧
        native_binary_uts w n = n - native_int_pow2 w) := by
  have hw0 : native_zleq 0 w = true := by
    have : 0 <= w := Int.le_of_lt hwpos
    simpa [native_zleq, SmtEval.native_zleq] using this
  let p := native_int_pow2 (w - 1)
  let q := native_div_total n p
  let r := native_mod_total n p
  have hpPos : 0 < p := by
    have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
    have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
    exact native_int_pow2_pos_of_nonneg hwp0
  have hRange := bitvec_payload_range_of_canonical hw0 hCanon
  have hPow : native_int_pow2 w = 2 * p := by
    simpa [p] using native_int_pow2_succ_pred (w := w) hwpos
  have hqNonneg : 0 <= q := Int.ediv_nonneg hRange.1 (Int.le_of_lt hpPos)
  have hqLt2 : q < 2 := by
    have hlt : n < 2 * p := by simpa [hPow] using hRange.2
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
  have hRRange : 0 <= r ∧ r < p := by
    constructor
    · simpa [r, native_mod_total] using Int.emod_nonneg n (Int.ne_of_gt hpPos)
    · simpa [r, native_mod_total] using Int.emod_lt_of_pos n hpPos
  have hRMod : native_mod_total r p = r := by
    simpa [native_mod_total] using Int.emod_eq_of_lt hRRange.1 hRRange.2
  rcases hqCases with hq | hq
  · -- sign bit 0: uts = n
    refine Or.inl ⟨hq, ?_⟩
    have hnEq : n = r := by
      rw [hq] at hDivMod; simp at hDivMod; exact hDivMod.symm
    rw [native_binary_uts]
    change native_zplus (native_zmult 2 (native_mod_total n p)) (native_zneg n) = n
    rw [hnEq]
    change native_zplus (native_zmult 2 (native_mod_total r p)) (native_zneg r) = r
    rw [hRMod]
    simp only [native_zplus, native_zmult, native_zneg]
    omega
  · -- sign bit 1: uts = n - 2^w
    refine Or.inr ⟨hq, ?_⟩
    have hnEq : n = p + r := by
      rw [hq] at hDivMod; simp at hDivMod; exact hDivMod.symm
    have hPAddMod : native_mod_total (p + r) p = r := by
      have hRModInt : r % p = r := by simpa [native_mod_total] using hRMod
      have hPModInt : p % p = 0 := Int.emod_eq_zero_of_dvd ⟨1, by simp⟩
      change (p + r) % p = r
      rw [Int.add_emod, hPModInt, hRModInt]
      simpa using hRModInt
    rw [native_binary_uts]
    change native_zplus (native_zmult 2 (native_mod_total n p)) (native_zneg n)
      = n - native_int_pow2 w
    rw [hnEq, hPAddMod, hPow]
    simp only [native_zplus, native_zmult, native_zneg]
    omega

/-- The width-1 extract payload (the sign bit), expressed via `native_div_total`. -/
private theorem extract_sign_bit_payload
    (w n wm : native_Int) :
    native_mod_total
        (native_binary_extract w n wm wm)
        (native_int_pow2 (native_zplus (native_zplus wm 1) (native_zneg wm)))
      = native_mod_total (native_div_total n (native_int_pow2 wm)) 2 := by
  have hExp : native_zplus (native_zplus wm 1) (native_zneg wm) = 1 := by
    simp only [native_zplus, native_zneg]; omega
  rw [hExp]
  have hPow1 : native_int_pow2 (1 : native_Int) = 2 := by native_decide
  rw [hPow1, native_binary_extract]

theorem cmd_step_uf_sbv_to_int_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_sbv_to_int_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_sbv_to_int_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_sbv_to_int_elim args premises) :=
by
  sorry
