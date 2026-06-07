import Cpc.Proofs.Translation.Full

open Eo
open SmtEval
open Smtm
open TranslationProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

def native_eo_to_smt_uop_indices_safe : Term -> native_Bool
  | Term.Apply f x =>
    native_and (native_eo_to_smt_uop_indices_safe f) (native_eo_to_smt_uop_indices_safe x)
  | Term.UOp1 _ x =>
    native_and (native_eo_to_smt_closed x) (native_eo_to_smt_uop_indices_safe x)
  | Term.UOp2 _ x y =>
    native_and
      (native_and (native_eo_to_smt_closed x) (native_eo_to_smt_closed y))
      (native_and (native_eo_to_smt_uop_indices_safe x) (native_eo_to_smt_uop_indices_safe y))
  | Term.UOp3 _ x y z =>
    native_and
      (native_and (native_and (native_eo_to_smt_closed x) (native_eo_to_smt_closed y)) (native_eo_to_smt_closed z))
      (native_and
        (native_and (native_eo_to_smt_uop_indices_safe x) (native_eo_to_smt_uop_indices_safe y))
        (native_eo_to_smt_uop_indices_safe z))
  | _ => true

def NativeEoToSmtUOpIndicesSafe (x : Term) : Prop :=
  native_eo_to_smt_uop_indices_safe x = true

private theorem native_and_eq_true_intro {a b : native_Bool} :
    a = true ->
    b = true ->
    native_and a b = true := by
  intro ha hb
  cases a <;> cases b <;> simp [native_and] at ha hb ⊢

private theorem native_and_left_eq_true {a b : native_Bool} :
    native_and a b = true -> a = true := by
  intro h
  cases a <;> cases b <;> simp [native_and] at h ⊢

private theorem native_and_right_eq_true {a b : native_Bool} :
    native_and a b = true -> b = true := by
  intro h
  cases a <;> cases b <;> simp [native_and] at h ⊢

private theorem native_eo_to_smt_uop_indices_safe_apply_intro
    {f x : Term}
    (hf : native_eo_to_smt_uop_indices_safe f = true)
    (hx : native_eo_to_smt_uop_indices_safe x = true) :
    native_eo_to_smt_uop_indices_safe (Term.Apply f x) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hf, hx, native_and]

private theorem native_eo_to_smt_uop_indices_safe_uop1_intro
    {op : UserOp1} {x : Term}
    (hc : native_eo_to_smt_closed x = true)
    (hs : native_eo_to_smt_uop_indices_safe x = true) :
    native_eo_to_smt_uop_indices_safe (Term.UOp1 op x) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hc, hs, native_and]

private theorem native_eo_to_smt_uop_indices_safe_uop2_intro
    {op : UserOp2} {x y : Term}
    (hxc : native_eo_to_smt_closed x = true)
    (hyc : native_eo_to_smt_closed y = true)
    (hxs : native_eo_to_smt_uop_indices_safe x = true)
    (hys : native_eo_to_smt_uop_indices_safe y = true) :
    native_eo_to_smt_uop_indices_safe (Term.UOp2 op x y) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hxc, hyc, hxs, hys,
    native_and]

private theorem native_eo_to_smt_uop_indices_safe_uop3_intro
    {op : UserOp3} {x y z : Term}
    (hxc : native_eo_to_smt_closed x = true)
    (hyc : native_eo_to_smt_closed y = true)
    (hzc : native_eo_to_smt_closed z = true)
    (hxs : native_eo_to_smt_uop_indices_safe x = true)
    (hys : native_eo_to_smt_uop_indices_safe y = true)
    (hzs : native_eo_to_smt_uop_indices_safe z = true) :
    native_eo_to_smt_uop_indices_safe (Term.UOp3 op x y z) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hxc, hyc, hzc, hxs, hys, hzs,
    native_and]

private theorem native_eo_to_smt_closed_of_guard_type_non_none
    {x : Term} {body : SmtTerm}
    (h :
      __smtx_typeof (native_eo_to_smt_guard_closed x body) ≠
        SmtType.None) :
    native_eo_to_smt_closed x = true := by
  cases hx : native_eo_to_smt_closed x
  · exfalso
    apply h
    simp [native_eo_to_smt_guard_closed, native_ite, hx,
      TranslationProofs.smtx_typeof_none]
  · rfl

private theorem guard_body_type_non_none_of_guard_type_non_none
    {x : Term} {body : SmtTerm}
    (h :
      __smtx_typeof (native_eo_to_smt_guard_closed x body) ≠
        SmtType.None) :
    __smtx_typeof body ≠ SmtType.None := by
  intro hBody
  cases hx : native_eo_to_smt_closed x
  · exact h (by
      simp [native_eo_to_smt_guard_closed, native_ite, hx,
        TranslationProofs.smtx_typeof_none])
  · exact h (by
      simpa [native_eo_to_smt_guard_closed, native_ite, hx] using hBody)

private theorem native_eo_to_smt_closed_of_nat_valid
    {x : Term}
    (h : __eo_to_smt_nat_is_valid x = true) :
    native_eo_to_smt_closed x = true := by
  cases x <;> simp [__eo_to_smt_nat_is_valid, native_eo_to_smt_closed,
    native_eo_to_smt_closed_rec] at h ⊢

private theorem native_eo_to_smt_uop_indices_safe_of_nat_valid
    {x : Term}
    (h : __eo_to_smt_nat_is_valid x = true) :
    native_eo_to_smt_uop_indices_safe x = true := by
  cases x <;> simp [__eo_to_smt_nat_is_valid,
    native_eo_to_smt_uop_indices_safe] at h ⊢

private theorem native_eo_to_smt_closed_rec_nil_of_closed
    {x : Term}
    (h : native_eo_to_smt_closed x = true) :
    native_eo_to_smt_closed_rec x [] = true := by
  simpa [native_eo_to_smt_closed] using h

private theorem native_eo_to_smt_closed_of_smt_numeral
    {x : Term} {n : native_Int}
    (h : __eo_to_smt x = SmtTerm.Numeral n) :
    native_eo_to_smt_closed x = true := by
  have hx : x = Term.Numeral n := eo_to_smt_eq_numeral x n h
  subst x
  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec]

private theorem native_eo_to_smt_uop_indices_safe_of_smt_numeral
    {x : Term} {n : native_Int}
    (h : __eo_to_smt x = SmtTerm.Numeral n) :
    native_eo_to_smt_uop_indices_safe x = true := by
  have hx : x = Term.Numeral n := eo_to_smt_eq_numeral x n h
  subst x
  simp [native_eo_to_smt_uop_indices_safe]

private theorem smt_typeof_non_none_of_eq_non_none
    {x : Term} {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hNone
  exact hT (h.symm.trans hNone)

private theorem smtx_typeof_at_purify_arg_non_none
    {x : SmtTerm}
    (h : __smtx_typeof (SmtTerm._at_purify x) ≠ SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  intro hx
  exact h (by simpa [__smtx_typeof] using hx)

private theorem smtx_typeof_guard_body_non_none_of_non_none
    {T U : SmtType}
    (h : __smtx_typeof_guard T U ≠ SmtType.None) :
    U ≠ SmtType.None := by
  intro hU
  cases T <;> simp [__smtx_typeof_guard, native_ite, hU] at h

private theorem smtx_typeof_guard_wf_body_non_none_of_non_none
    {T U : SmtType}
    (h : __smtx_typeof_guard_wf T U ≠ SmtType.None) :
  U ≠ SmtType.None := by
  intro hU
  have hEq := Smtm.smtx_typeof_guard_wf_of_non_none T U h
  exact h (by simpa [hEq] using hU)

private theorem smtx_apply_arg_non_none_of_any_non_none
    {f x : SmtTerm}
    (h : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  cases f
  case DtSel s d i j =>
    let R := __smtx_ret_typeof_sel s d i j
    have hBody :
        __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R)
            (__smtx_typeof x) ≠ SmtType.None :=
      smtx_typeof_guard_wf_body_non_none_of_non_none (T := R) (by
        simpa [__smtx_typeof, R] using h)
    rcases typeof_apply_non_none_cases hBody with
      ⟨A, _B, _hHead, hArg, hA, _hB⟩
    rw [hArg]
    exact hA
  case DtTester s d i =>
    let D := SmtType.Datatype s d
    let C := __smtx_typeof_dt_cons_rec D (__smtx_dt_substitute s d d) i
    have hBody :
        __smtx_typeof_apply (SmtType.FunType D SmtType.Bool)
            (__smtx_typeof x) ≠ SmtType.None :=
      smtx_typeof_guard_body_non_none_of_non_none (T := C) (by
        simpa [__smtx_typeof, D, C] using h)
    rcases typeof_apply_non_none_cases hBody with
      ⟨A, _B, _hHead, hArg, hA, _hB⟩
    rw [hArg]
    exact hA
  all_goals
    exact smtx_apply_arg_non_none_of_non_special_non_none
      _ _ (by intro s d i j hSel; cases hSel)
      (by intro s d i hTester; cases hTester) h

private theorem native_eo_to_smt_uop_indices_safe_of_dt_sel_translation
    {x : Term} {s : native_String} {d : SmtDatatype}
    {i j : native_Nat}
    (h : __eo_to_smt x = SmtTerm.DtSel s d i j) :
    native_eo_to_smt_uop_indices_safe x = true := by
  rcases eo_to_smt_eq_dt_sel_cases x s d i j h with hSel | hPurify
  · rcases hSel with ⟨d0, _hd, hx, _hReserved⟩
    subst x
    simp [native_eo_to_smt_uop_indices_safe]
  · rcases hPurify with ⟨z, hx, _hz⟩
    subst x
    exfalso
    change
      native_eo_to_smt_guard_closed z
          (SmtTerm._at_purify (__eo_to_smt z)) =
        SmtTerm.DtSel s d i j at h
    cases hzClosed : native_eo_to_smt_closed z <;>
      simp [native_eo_to_smt_guard_closed, native_ite, hzClosed] at h

private theorem native_eo_to_smt_closed_of_dt_cons_translation
    {x : Term} {s : native_String} {d : SmtDatatype} {i : native_Nat}
    (h : __eo_to_smt x = SmtTerm.DtCons s d i) :
    native_eo_to_smt_closed x = true := by
  rcases eo_to_smt_eq_dt_cons_cases x s d i h with hCons | hTuple
  · rcases hCons with ⟨d0, _hd, hx, _hReserved⟩
    subst x
    simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec]
  · rcases hTuple with ⟨_hs, _hd, _hi, hx⟩
    subst x
    simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec]

private theorem native_eo_to_smt_uop_indices_safe_of_dt_cons_translation
    {x : Term} {s : native_String} {d : SmtDatatype} {i : native_Nat}
    (h : __eo_to_smt x = SmtTerm.DtCons s d i) :
    native_eo_to_smt_uop_indices_safe x = true := by
  rcases eo_to_smt_eq_dt_cons_cases x s d i h with hCons | hTuple
  · rcases hCons with ⟨d0, _hd, hx, _hReserved⟩
    subst x
    simp [native_eo_to_smt_uop_indices_safe]
  · rcases hTuple with ⟨_hs, _hd, _hi, hx⟩
    subst x
    simp [native_eo_to_smt_uop_indices_safe]

private theorem native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
    {f x : Term}
    (ihf :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe f = true)
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.Apply f x) = true := by
  by_cases hSelWitness :
      ∃ s d i j, __eo_to_smt f = SmtTerm.DtSel s d i j
  · rcases hSelWitness with ⟨s, d, i, j, hSel⟩
    exact native_eo_to_smt_uop_indices_safe_apply_intro
      (native_eo_to_smt_uop_indices_safe_of_dt_sel_translation hSel)
      (ihx (smtx_apply_arg_non_none_of_any_non_none h))
  · have hSel :
        ∀ s d i j, __eo_to_smt f ≠ SmtTerm.DtSel s d i j := by
      intro s d i j hEq
      exact hSelWitness ⟨s, d, i, j, hEq⟩
    have hTester :
        ∀ s d i, __eo_to_smt f ≠ SmtTerm.DtTester s d i := by
      intro s d i hEq
      exact eo_to_smt_ne_dt_tester f s d i hEq
    exact native_eo_to_smt_uop_indices_safe_apply_intro
      (ihf
        (smtx_apply_head_non_none_of_non_special_non_none
          (__eo_to_smt f) (__eo_to_smt x) hSel hTester h))
      (ihx
        (smtx_apply_arg_non_none_of_non_special_non_none
          (__eo_to_smt f) (__eo_to_smt x) hSel hTester h))

private theorem native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
    {f x : Term}
    (ihf :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe f = true)
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (hTranslate :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (h :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.Apply f x) = true := by
  have hApply :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
        SmtType.None := by
    simpa [hTranslate] using h
  exact native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
    (f := f) (x := x) ihf ihx hApply

private theorem native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
    {op : UserOp1} {x : Term} {n : native_Int}
    (hx : __eo_to_smt x = SmtTerm.Numeral n) :
    native_eo_to_smt_uop_indices_safe (Term.UOp1 op x) = true :=
  native_eo_to_smt_uop_indices_safe_uop1_intro
    (native_eo_to_smt_closed_of_smt_numeral hx)
    (native_eo_to_smt_uop_indices_safe_of_smt_numeral hx)

private theorem native_eo_to_smt_uop_indices_safe_uop2_of_smt_numerals
    {op : UserOp2} {x y : Term} {m n : native_Int}
    (hx : __eo_to_smt x = SmtTerm.Numeral m)
    (hy : __eo_to_smt y = SmtTerm.Numeral n) :
    native_eo_to_smt_uop_indices_safe (Term.UOp2 op x y) = true :=
  native_eo_to_smt_uop_indices_safe_uop2_intro
    (native_eo_to_smt_closed_of_smt_numeral hx)
    (native_eo_to_smt_closed_of_smt_numeral hy)
    (native_eo_to_smt_uop_indices_safe_of_smt_numeral hx)
    (native_eo_to_smt_uop_indices_safe_of_smt_numeral hy)

private theorem native_eo_to_smt_uop_indices_safe_of_type_valid_rec :
    ∀ {refs : List native_String} {T : Term},
      eo_type_valid_rec refs T ->
      native_eo_to_smt_closed T = true ∧
        native_eo_to_smt_uop_indices_safe T = true
  | refs, Term.Bool, _ => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.USort i, _ => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.UOp op, h => by
      cases op <;> simp [eo_type_valid_rec,
        native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe] at h ⊢
  | refs, Term.DatatypeType s d, h => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.DatatypeTypeRef s, h => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.DtcAppType T U, h => by
      rcases h with ⟨hT, hU⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hUc', hTs, hUs,
        native_and]
  | refs, Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, native_and]
  | refs, Term.Apply (Term.UOp UserOp.Seq) T, h => by
      have hT : eo_type_valid_rec [] T := by
        simpa [eo_type_valid_rec] using h
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, native_and]
  | refs, Term.Apply (Term.UOp UserOp.Set) T, h => by
      have hT : eo_type_valid_rec [] T := by
        simpa [eo_type_valid_rec] using h
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, native_and]
  | refs, Term.Apply (Term.Apply Term.FunType T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U) with ⟨hT, hU⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, hUc', hUs,
        native_and]
  | refs, Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U) with ⟨hT, hU⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, hUc', hUs,
        native_and]
  | refs, Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U ∧
          __smtx_type_wf
            (__eo_to_smt_type_tuple (__eo_to_smt_type T)
              (__eo_to_smt_type U)) = true) with ⟨hT, hU, _⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, hUc', hUs,
        native_and]
  | refs, Term.Apply f x, h => by
      cases f with
      | UOp op =>
          cases op with
          | Int =>
              exfalso
              simp [eo_type_valid_rec] at h
          | Real =>
              exfalso
              simp [eo_type_valid_rec] at h
          | Char =>
              exfalso
              simp [eo_type_valid_rec] at h
          | UnitTuple =>
              exfalso
              simp [eo_type_valid_rec] at h
          | BitVec =>
              cases x with
              | Numeral n =>
                  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                    native_eo_to_smt_uop_indices_safe, native_and]
              | _ =>
                  exfalso
                  simp [eo_type_valid_rec] at h
          | Seq =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using h
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                ⟨hxc, hxs⟩
              have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
              simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                native_eo_to_smt_uop_indices_safe, hxc', hxs, native_and]
          | Set =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using h
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                ⟨hxc, hxs⟩
              have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
              simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                native_eo_to_smt_uop_indices_safe, hxc', hxs, native_and]
          | _ =>
              exfalso
              simp [eo_type_valid_rec] at h
      | Apply g y =>
          cases g with
          | FunType =>
              rcases (by simpa [eo_type_valid_rec] using h :
                eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hy with
                ⟨hyc, hys⟩
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                ⟨hxc, hxs⟩
              have hyc' := native_eo_to_smt_closed_rec_nil_of_closed hyc
              have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
              simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                native_eo_to_smt_uop_indices_safe, hyc', hys, hxc', hxs,
                native_and]
          | UOp op =>
              cases op with
              | Array =>
                  rcases (by simpa [eo_type_valid_rec] using h :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with
                    ⟨hy, hx⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hy with
                    ⟨hyc, hys⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                    ⟨hxc, hxs⟩
                  have hyc' := native_eo_to_smt_closed_rec_nil_of_closed hyc
                  have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
                  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                    native_eo_to_smt_uop_indices_safe, hyc', hys, hxc', hxs,
                    native_and]
              | Tuple =>
                  rcases (by simpa [eo_type_valid_rec] using h :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x ∧
                      __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y)
                          (__eo_to_smt_type x)) = true) with
                    ⟨hy, hx, _⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hy with
                    ⟨hyc, hys⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                    ⟨hxc, hxs⟩
                  have hyc' := native_eo_to_smt_closed_rec_nil_of_closed hyc
                  have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
                  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                    native_eo_to_smt_uop_indices_safe, hyc', hys, hxc', hxs,
                    native_and]
              | _ =>
                  exfalso
                  simp [eo_type_valid_rec] at h
          | _ =>
              exfalso
              simp [eo_type_valid_rec] at h
      | _ =>
          exfalso
          simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List_nil, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List_cons, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Boolean b, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Numeral n, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Rational q, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.String s, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Binary w n, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Type, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Stuck, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.FunType, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Var name T, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.DtCons s d i, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.DtSel s d i j, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.UConst i T, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.UOp1 op x, h => by
      cases op <;> exfalso <;> simp [eo_type_valid_rec] at h
  | refs, Term.UOp2 op x y, h => by
      cases op <;> exfalso <;> simp [eo_type_valid_rec] at h
  | refs, Term.UOp3 op x y z, h => by
      cases op <;> exfalso <;> simp [eo_type_valid_rec] at h

private theorem native_eo_to_smt_uop_indices_safe_of_type_valid
    {T : Term} :
    eo_type_valid T ->
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true := by
  intro h
  cases T with
  | UOp op =>
      cases op <;> simp [eo_type_valid, eo_type_valid_rec,
        native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe] at h ⊢
  | _ =>
      exact native_eo_to_smt_uop_indices_safe_of_type_valid_rec
        (refs := []) h

private theorem native_eo_to_smt_uop_indices_safe_of_smt_type_wf
    {T : Term}
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true :=
  native_eo_to_smt_uop_indices_safe_of_type_valid
    (eo_type_valid_of_smt_wf T hWf)

private theorem native_eo_to_smt_uop_indices_safe_of_typed_list_elem_type_non_none
    (root : Term)
    (ih :
      ∀ x : Term,
        sizeOf x < sizeOf root ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe x = true) :
    ∀ xs : Term,
      sizeOf xs < sizeOf root ->
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe xs = true := by
  let rec go : ∀ xs : Term,
      sizeOf xs < sizeOf root ->
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe xs = true
    | xs, hLt, h => by
        cases xs
        case Apply f tail =>
          cases f
          case UOp op =>
            cases op
            case _at__at_TypedList_nil =>
              have hWf : __smtx_type_wf (__eo_to_smt_type tail) = true := by
                by_cases hWf : __smtx_type_wf (__eo_to_smt_type tail) = true
                · exact hWf
                · exfalso
                  apply h
                  simp [__eo_to_smt_typed_list_elem_type, native_ite, hWf]
              rcases native_eo_to_smt_uop_indices_safe_of_smt_type_wf
                  (T := tail) hWf with
                ⟨_tailClosed, tailSafe⟩
              exact native_eo_to_smt_uop_indices_safe_apply_intro
                (by simp [native_eo_to_smt_uop_indices_safe]) tailSafe
            all_goals
              exfalso
              apply h
              simp [__eo_to_smt_typed_list_elem_type]
          case Apply g head =>
            cases g
            case UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                let headTy := __smtx_typeof (__eo_to_smt head)
                let tailTy := __eo_to_smt_typed_list_elem_type tail
                have hGuard : native_Teq headTy tailTy = true := by
                  by_cases hGuard : native_Teq headTy tailTy = true
                  · exact hGuard
                  · exfalso
                    apply h
                    simp [__eo_to_smt_typed_list_elem_type, headTy, tailTy,
                      native_ite, hGuard]
                have hHeadTyNN : headTy ≠ SmtType.None := by
                  change
                    (native_ite (native_Teq headTy tailTy) headTy
                        SmtType.None) ≠
                      SmtType.None at h
                  rw [hGuard] at h
                  exact h
                have hTailTyNN : tailTy ≠ SmtType.None := by
                  intro hTailNone
                  have hHeadEqTail : headTy = tailTy := by
                    simpa [native_Teq] using hGuard
                  exact hHeadTyNN (by rw [hHeadEqTail, hTailNone])
                have hHeadLt : sizeOf head < sizeOf root := by
                  simp at hLt
                  omega
                have hTailLt : sizeOf tail < sizeOf root := by
                  simp at hLt
                  omega
                exact native_eo_to_smt_uop_indices_safe_apply_intro
                  (native_eo_to_smt_uop_indices_safe_apply_intro
                    (by simp [native_eo_to_smt_uop_indices_safe])
                    (ih head hHeadLt (by simpa [headTy] using hHeadTyNN)))
                  (go tail hTailLt (by simpa [tailTy] using hTailTyNN))
              all_goals
                exfalso
                apply h
                simp [__eo_to_smt_typed_list_elem_type]
            all_goals
              exfalso
              apply h
              simp [__eo_to_smt_typed_list_elem_type]
          all_goals
            exfalso
            apply h
            simp [__eo_to_smt_typed_list_elem_type]
        all_goals
          exfalso
          apply h
          simp [__eo_to_smt_typed_list_elem_type]
  exact go

private theorem native_eo_to_smt_uop_indices_safe_of_apply_distinct_non_none
    {xs : Term}
    (root : Term)
    (ih :
      ∀ x : Term,
        sizeOf x < sizeOf root ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe x = true)
    (hLt : sizeOf xs < sizeOf root)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp UserOp.distinct) xs) = true := by
  change
    __smtx_typeof
        (native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct xs)) ≠
      SmtType.None at h
  have hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    intro hElemNone
    apply h
    simp [native_ite, hElemNone, native_Teq,
      TranslationProofs.smtx_typeof_none]
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (by simp [native_eo_to_smt_uop_indices_safe])
    (native_eo_to_smt_uop_indices_safe_of_typed_list_elem_type_non_none
      root ih xs hLt hElemNN)

private theorem smtx_typeof_not_arg_bool_of_non_none
    {t : SmtTerm}
    (h : __smtx_typeof (SmtTerm.not t) ≠ SmtType.None) :
    __smtx_typeof t = SmtType.Bool := by
  have hNotBool : __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
    rw [typeof_not_eq]
    by_cases hArg : native_Teq (__smtx_typeof t) SmtType.Bool = true
    · simp [native_ite, hArg]
    · exfalso
      apply h
      rw [typeof_not_eq]
      simp [native_ite, hArg, TranslationProofs.smtx_typeof_none]
  exact smtx_typeof_not_arg_bool t hNotBool

private theorem native_eo_to_smt_uop_indices_safe_of_var_list_exists_bool
    (root : Term) :
    ∀ xs body,
      sizeOf xs < sizeOf root ->
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
        native_eo_to_smt_uop_indices_safe xs = true := by
  let rec go : ∀ xs body,
      sizeOf xs < sizeOf root ->
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
        native_eo_to_smt_uop_indices_safe xs = true
    | xs, body, hLt, hBool => by
        cases xs
        case __eo_List_nil =>
          simp [native_eo_to_smt_uop_indices_safe]
        case Apply f tail =>
          cases f
          case Apply g head =>
            cases g
            case __eo_List_cons =>
              cases head
              case Var name T =>
                cases name
                case String s =>
                  have hExistsTy :
                      __smtx_typeof
                          (SmtTerm.exists s (__eo_to_smt_type T)
                            (__eo_to_smt_exists tail body)) =
                        SmtType.Bool := by
                    simpa [__eo_to_smt_exists] using hBool
                  have hExistsNN :
                      term_has_non_none_type
                        (SmtTerm.exists s (__eo_to_smt_type T)
                          (__eo_to_smt_exists tail body)) := by
                    unfold term_has_non_none_type
                    rw [hExistsTy]
                    simp
                  have hTailBool :
                      __smtx_typeof (__eo_to_smt_exists tail body) =
                        SmtType.Bool := by
                    simpa using exists_body_bool_of_non_none hExistsNN
                  have hTailLt : sizeOf tail < sizeOf root := by
                    simp at hLt
                    omega
                  exact native_eo_to_smt_uop_indices_safe_apply_intro
                    (native_eo_to_smt_uop_indices_safe_apply_intro
                      (by simp [native_eo_to_smt_uop_indices_safe])
                      (by simp [native_eo_to_smt_uop_indices_safe]))
                    (go tail body hTailLt hTailBool)
                all_goals
                  exfalso
                  have hNone := hBool
                  simp [__eo_to_smt_exists,
                    TranslationProofs.smtx_typeof_none] at hNone
              all_goals
                exfalso
                have hNone := hBool
                simp [__eo_to_smt_exists,
                  TranslationProofs.smtx_typeof_none] at hNone
            all_goals
              exfalso
              have hNone := hBool
              simp [__eo_to_smt_exists,
                TranslationProofs.smtx_typeof_none] at hNone
          all_goals
            exfalso
            have hNone := hBool
            simp [__eo_to_smt_exists,
              TranslationProofs.smtx_typeof_none] at hNone
        all_goals
          exfalso
          have hNone := hBool
          simp [__eo_to_smt_exists,
            TranslationProofs.smtx_typeof_none] at hNone
  exact go

private theorem native_eo_to_smt_uop_indices_safe_of_apply_exists_non_none
    {xs F : Term}
    (root : Term)
    (ih :
      ∀ x : Term,
        sizeOf x < sizeOf root ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe x = true)
    (hXsLt : sizeOf xs < sizeOf root)
    (hFLt : sizeOf F < sizeOf root)
    (h :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) F)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) F) = true := by
  cases xs
  case __eo_List_nil =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name
          case String s =>
            have hChain :
                __smtx_typeof
                    (__eo_to_smt_exists
                      (Term.Apply
                        (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T)) tail)
                      (__eo_to_smt F)) =
                  SmtType.Bool := by
              have hExistsNN :
                  term_has_non_none_type
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt F))) := by
                unfold term_has_non_none_type
                change
                  __smtx_typeof
                      (SmtTerm.exists s (__eo_to_smt_type T)
                        (__eo_to_smt_exists tail (__eo_to_smt F))) ≠
                    SmtType.None at h
                exact h
              simpa [__eo_to_smt_exists] using
                exists_term_typeof_of_non_none hExistsNN
            have hFBool :
                __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
              eo_to_smt_exists_body_bool_of_bool
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) tail)
                (__eo_to_smt F) hChain
            have hFNN : __smtx_typeof (__eo_to_smt F) ≠ SmtType.None := by
              rw [hFBool]
              simp
            exact native_eo_to_smt_uop_indices_safe_apply_intro
              (native_eo_to_smt_uop_indices_safe_apply_intro
                (by simp [native_eo_to_smt_uop_indices_safe])
                (native_eo_to_smt_uop_indices_safe_of_var_list_exists_bool
                  root
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) tail)
                  (__eo_to_smt F) hXsLt hChain))
              (ih F hFLt hFNN)
          all_goals
            exfalso
            apply h
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact TranslationProofs.smtx_typeof_none
        all_goals
          exfalso
          apply h
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      all_goals
        exfalso
        apply h
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    all_goals
      exfalso
      apply h
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  all_goals
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

private theorem native_eo_to_smt_uop_indices_safe_of_apply_forall_non_none
    {xs F : Term}
    (root : Term)
    (ih :
      ∀ x : Term,
        sizeOf x < sizeOf root ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe x = true)
    (hXsLt : sizeOf xs < sizeOf root)
    (hFLt : sizeOf F < sizeOf root)
    (h :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) = true := by
  cases xs
  case __eo_List_nil =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name
          case String s =>
            have hChain :
                __smtx_typeof
                    (__eo_to_smt_exists
                      (Term.Apply
                        (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T)) tail)
                      (SmtTerm.not (__eo_to_smt F))) =
                  SmtType.Bool := by
              apply smtx_typeof_not_arg_bool_of_non_none
              change
                __smtx_typeof
                    (SmtTerm.not
                      (SmtTerm.exists s (__eo_to_smt_type T)
                        (__eo_to_smt_exists tail
                          (SmtTerm.not (__eo_to_smt F))))) ≠
                  SmtType.None at h
              simpa [__eo_to_smt_exists] using h
            have hNotF :
                __smtx_typeof (SmtTerm.not (__eo_to_smt F)) =
                  SmtType.Bool :=
              eo_to_smt_exists_body_bool_of_bool
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) tail)
                (SmtTerm.not (__eo_to_smt F)) hChain
            have hFBool : __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
              smtx_typeof_not_arg_bool (__eo_to_smt F) hNotF
            have hFNN : __smtx_typeof (__eo_to_smt F) ≠ SmtType.None := by
              rw [hFBool]
              simp
            exact native_eo_to_smt_uop_indices_safe_apply_intro
              (native_eo_to_smt_uop_indices_safe_apply_intro
                (by simp [native_eo_to_smt_uop_indices_safe])
                (native_eo_to_smt_uop_indices_safe_of_var_list_exists_bool
                  root
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) tail)
                  (SmtTerm.not (__eo_to_smt F)) hXsLt hChain))
              (ih F hFLt hFNN)
          all_goals
            exfalso
            apply h
            change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
            rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
            simp [native_ite, native_Teq]
        all_goals
          exfalso
          apply h
          change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
          rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
          simp [native_ite, native_Teq]
      all_goals
        exfalso
        apply h
        change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
        rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
        simp [native_ite, native_Teq]
    all_goals
      exfalso
      apply h
      change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
      rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
      simp [native_ite, native_Teq]
  all_goals
    exfalso
    apply h
    change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
    rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
    simp [native_ite, native_Teq]

private theorem native_eo_to_smt_uop_indices_safe_of_seq_empty_non_none
    {T : Term}
    (h :
      __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) ≠
        SmtType.None) :
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true := by
  cases hTy : __eo_to_smt_type T
  case Seq A =>
    have hSeqNN : __smtx_typeof (SmtTerm.seq_empty A) ≠ SmtType.None := by
      intro hNone
      apply h
      simpa [__eo_to_smt_seq_empty, hTy] using hNone
    have hGuard :
        __smtx_typeof_guard_wf (SmtType.Seq A) (SmtType.Seq A) ≠
          SmtType.None := by
      unfold __smtx_typeof at hSeqNN
      exact hSeqNN
    have hWfSeq :=
      smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Seq A) (SmtType.Seq A) hGuard
    have hWf : __smtx_type_wf (__eo_to_smt_type T) = true := by
      simpa [hTy] using hWfSeq
    exact native_eo_to_smt_uop_indices_safe_of_smt_type_wf hWf
  all_goals
    exfalso
    apply h
    simp [__eo_to_smt_seq_empty, hTy, TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_uop_indices_safe_of_set_empty_non_none
    {T : Term}
    (h :
      __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) ≠
        SmtType.None) :
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true := by
  cases hTy : __eo_to_smt_type T
  case Set A =>
    have hSetNN : __smtx_typeof (SmtTerm.set_empty A) ≠ SmtType.None := by
      intro hNone
      apply h
      simpa [__eo_to_smt_set_empty, hTy] using hNone
    have hGuard :
        __smtx_typeof_guard_wf (SmtType.Set A) (SmtType.Set A) ≠
          SmtType.None := by
      unfold __smtx_typeof at hSetNN
      exact hSetNN
    have hWfSet :=
      smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Set A) (SmtType.Set A) hGuard
    have hWf : __smtx_type_wf (__eo_to_smt_type T) = true := by
      simpa [hTy] using hWfSet
    exact native_eo_to_smt_uop_indices_safe_of_smt_type_wf hWf
  all_goals
    exfalso
    apply h
    simp [__eo_to_smt_set_empty, hTy, TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_uop_indices_safe_of_uop1_non_none
    {op : UserOp1} {x : Term}
    (ih :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h : __smtx_typeof (__eo_to_smt (Term.UOp1 op x)) ≠ SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.UOp1 op x) = true := by
  cases op
  case _at_purify =>
    have hxClosed :
        native_eo_to_smt_closed x = true :=
      native_eo_to_smt_closed_of_guard_type_non_none h
    have hBody :
        __smtx_typeof (SmtTerm._at_purify (__eo_to_smt x)) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none h
    have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None :=
      smtx_typeof_at_purify_arg_non_none hBody
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed (ih hxNN)
  case seq_empty =>
    rcases native_eo_to_smt_uop_indices_safe_of_seq_empty_non_none h with
      ⟨hxClosed, hxSafe⟩
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed hxSafe
  case _at_strings_stoi_non_digit =>
    have hxClosed :
        native_eo_to_smt_closed x = true :=
      native_eo_to_smt_closed_of_guard_type_non_none h
    have hBody :
        __smtx_typeof
            (SmtTerm.str_indexof_re (__eo_to_smt x)
              (SmtTerm.re_comp
                (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
                  (SmtTerm.String (native_string_lit "9"))))
              (SmtTerm.Numeral 0)) ≠ SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none h
    have hArgs :=
      str_indexof_re_args_of_non_none
        (t1 := __eo_to_smt x)
        (t2 :=
          SmtTerm.re_comp
            (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
              (SmtTerm.String (native_string_lit "9"))))
        (t3 := SmtTerm.Numeral 0) hBody
    have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None :=
      smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp)
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed (ih hxNN)
  case set_empty =>
    rcases native_eo_to_smt_uop_indices_safe_of_set_empty_non_none h with
      ⟨hxClosed, hxSafe⟩
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed hxSafe
  all_goals
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

private theorem native_eo_to_smt_uop_indices_safe_of_apply_repeat_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.repeat idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.repeat idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases repeat_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, w, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.repeat) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_zero_extend_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases zero_extend_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, w, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.zero_extend) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_sign_extend_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases sign_extend_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, w, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.sign_extend) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_rotate_left_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases rotate_left_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, w, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.rotate_left) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_rotate_right_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases rotate_right_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, w, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.rotate_right) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_int_to_bv_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases int_to_bv_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.int_to_bv) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem smt_re_exp_args_of_non_none
    {a x : SmtTerm}
    (h : __smtx_typeof (SmtTerm.re_exp a x) ≠ SmtType.None) :
    ∃ n : native_Int,
      a = SmtTerm.Numeral n ∧ __smtx_typeof x = SmtType.RegLan := by
  rw [typeof_re_exp_eq] at h
  cases a <;> simp [__smtx_typeof_re_exp] at h
  case Numeral n =>
    cases hx : __smtx_typeof x <;> simp [hx] at h
    by_cases hn : native_zleq 0 n = true
    · exact ⟨n, rfl, rfl⟩
    · exfalso
      cases hz : native_zleq 0 n <;> simp [hz] at hn h
      exact h rfl

private theorem native_eo_to_smt_uop_indices_safe_of_apply_re_exp_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases smt_re_exp_args_of_non_none h with ⟨n, hIdx, hxTy⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.re_exp) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_at_bit_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x) = true := by
  change
    __smtx_typeof
        (SmtTerm.eq
          (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
            (__eo_to_smt x))
          (SmtTerm.Binary 1 1)) ≠
      SmtType.None at h
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x)))
          (__smtx_typeof (SmtTerm.Binary 1 1)) ≠
        SmtType.None := by
    simpa [typeof_eq_eq] using h
  have hEqArgs := smtx_typeof_eq_non_none hEqNN
  have hExtNN :
      term_has_non_none_type
        (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
          (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hEqArgs.2
  rcases extract_args_of_non_none hExtNN with
    ⟨i, _j, w, hIdx, _hIdx', hxTy, _hj0, _hji, _hiw⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1._at_bit) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_guarded_uop1_apply_non_none
    {op : UserOp1} {idx x : Term} {body : SmtTerm}
    (ihIdx :
      __smtx_typeof (__eo_to_smt idx) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe idx = true)
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (hBodyArgs :
      __smtx_typeof body ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt idx) ≠ SmtType.None ∧
          __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (h :
      __smtx_typeof (native_eo_to_smt_guard_closed idx body) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 op idx) x) = true := by
  have hIdxClosed :
      native_eo_to_smt_closed idx = true :=
    native_eo_to_smt_closed_of_guard_type_non_none h
  have hBody :
      __smtx_typeof body ≠ SmtType.None :=
    guard_body_type_non_none_of_guard_type_non_none h
  rcases hBodyArgs hBody with ⟨hIdxNN, hxNN⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_intro
      hIdxClosed (ihIdx hIdxNN))
    (ihx hxNN)

private theorem native_eo_to_smt_strings_stoi_result_args_non_none
    {idx x : Term}
    (h :
      __smtx_typeof
          (SmtTerm.str_to_int
            (SmtTerm.str_substr (__eo_to_smt idx) (SmtTerm.Numeral 0)
              (__eo_to_smt x))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt idx) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  let sub :=
    SmtTerm.str_substr (__eo_to_smt idx) (SmtTerm.Numeral 0)
      (__eo_to_smt x)
  have hSubSeq :
      __smtx_typeof sub = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
      (typeof_str_to_int_eq sub) (by
        unfold term_has_non_none_type
        simpa [sub] using h)
  have hSubNN : term_has_non_none_type sub := by
    unfold term_has_non_none_type
    rw [hSubSeq]
    simp
  rcases str_substr_args_of_non_none hSubNN with
    ⟨T, hIdxSeq, _hStart, hxInt⟩
  exact
    ⟨smt_typeof_non_none_of_eq_non_none hIdxSeq (by simp),
      smt_typeof_non_none_of_eq_non_none hxInt (by simp)⟩

private theorem native_eo_to_smt_strings_itos_result_args_non_none
    {idx x : Term}
    (h :
      __smtx_typeof
          (SmtTerm.mod (__eo_to_smt idx)
            (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt idx) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  have hModNN :
      term_has_non_none_type
        (SmtTerm.mod (__eo_to_smt idx)
          (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x))) := by
    unfold term_has_non_none_type
    exact h
  have hArgs :=
    int_binop_args_of_non_none (op := SmtTerm.mod) (R := SmtType.Int)
      (typeof_mod_eq (__eo_to_smt idx)
        (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x)))
      hModNN
  have hMulNN :
      term_has_non_none_type
        (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hArgs.2]
    simp
  have hMulArgs :=
    int_binop_args_of_non_none (op := SmtTerm.multmult) (R := SmtType.Int)
      (typeof_multmult_eq (SmtTerm.Numeral 10) (__eo_to_smt x))
      hMulNN
  exact
    ⟨smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp),
      smt_typeof_non_none_of_eq_non_none hMulArgs.2 (by simp)⟩

private theorem native_eo_to_smt_uop_indices_safe_of_apply_is_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.is idx) x) = true := by
  change
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx))
          (__eo_to_smt x)) ≠
      SmtType.None at h
  cases hIdx : __eo_to_smt idx
  case DtCons s d i =>
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      simpa [__eo_to_smt_tester, hIdx] using h
    have hxTy :
        __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s d :=
      dt_tester_arg_datatype_of_non_none hApplyNN
    exact native_eo_to_smt_uop_indices_safe_apply_intro
      (native_eo_to_smt_uop_indices_safe_uop1_intro
        (native_eo_to_smt_closed_of_dt_cons_translation hIdx)
        (native_eo_to_smt_uop_indices_safe_of_dt_cons_translation hIdx))
      (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))
  all_goals
    exfalso
    apply h
    simp [__eo_to_smt_tester, hIdx, typeof_apply_none_eq]

private theorem native_eo_to_smt_uop_indices_safe_of_apply_tuple_select_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) = true := by
  change
    __smtx_typeof
        (__eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt x))
          (__eo_to_smt idx) (__eo_to_smt x)) ≠
      SmtType.None at h
  cases hxTy : __smtx_typeof (__eo_to_smt x)
  case Datatype s d =>
    cases hIdx : __eo_to_smt idx
    case Numeral n =>
      by_cases hGuard :
          native_and (native_streq s (native_string_lit "@Tuple"))
              (native_zleq 0 n) =
            true
      · exact native_eo_to_smt_uop_indices_safe_apply_intro
          (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
            (op := UserOp1.tuple_select) hIdx)
          (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))
      · exfalso
        apply h
        simp [__eo_to_smt_tuple_select, hxTy, hIdx, native_ite, hGuard]
    all_goals
      exfalso
      apply h
      simp [__eo_to_smt_tuple_select, hxTy, hIdx,
        TranslationProofs.smtx_typeof_none]
  all_goals
    exfalso
    apply h
    simp [__eo_to_smt_tuple_select, hxTy,
      TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_uop_indices_safe_of_guarded_uop2_non_none
    {op : UserOp2} {x y : Term} {body : SmtTerm}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (ihy :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe y = true)
    (hBodyArgs :
      __smtx_typeof body ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
          __smtx_typeof (__eo_to_smt y) ≠ SmtType.None)
    (h :
      __smtx_typeof
          (native_eo_to_smt_guard_closed x
            (native_eo_to_smt_guard_closed y body)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.UOp2 op x y) = true := by
  have hxClosed :
      native_eo_to_smt_closed x = true :=
    native_eo_to_smt_closed_of_guard_type_non_none h
  have hInner :
      __smtx_typeof (native_eo_to_smt_guard_closed y body) ≠
        SmtType.None :=
    guard_body_type_non_none_of_guard_type_non_none h
  have hyClosed :
      native_eo_to_smt_closed y = true :=
    native_eo_to_smt_closed_of_guard_type_non_none hInner
  have hBody :
      __smtx_typeof body ≠ SmtType.None :=
    guard_body_type_non_none_of_guard_type_non_none hInner
  rcases hBodyArgs hBody with ⟨hxNN, hyNN⟩
  exact native_eo_to_smt_uop_indices_safe_uop2_intro
    hxClosed hyClosed (ihx hxNN) (ihy hyNN)

private theorem native_eo_to_smt_array_deq_diff_args_non_none
    {x y : Term}
    (h :
      __smtx_typeof
          (__eo_to_smt_array_deq_diff (__eo_to_smt x)
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
            (__smtx_typeof (__eo_to_smt y))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
  constructor
  · intro hxNone
    apply h
    simp [__eo_to_smt_array_deq_diff, hxNone,
      TranslationProofs.smtx_typeof_none]
  · intro hyNone
    apply h
    cases hx : __smtx_typeof (__eo_to_smt x) <;>
      simp [__eo_to_smt_array_deq_diff, hyNone,
        TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_sets_deq_diff_args_non_none
    {x y : Term}
    (h :
      __smtx_typeof
          (__eo_to_smt_sets_deq_diff (__eo_to_smt x)
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
            (__smtx_typeof (__eo_to_smt y))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
  constructor
  · intro hxNone
    apply h
    simp [__eo_to_smt_sets_deq_diff, hxNone,
      TranslationProofs.smtx_typeof_none]
  · intro hyNone
    apply h
    cases hx : __smtx_typeof (__eo_to_smt x) <;>
      simp [__eo_to_smt_sets_deq_diff, hyNone,
        TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_strings_deq_diff_args_non_none
    {x y : Term}
    (h :
      __smtx_typeof
          (SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int
            (SmtTerm.not
              (SmtTerm.eq
                (SmtTerm.str_substr (__eo_to_smt x)
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                  (SmtTerm.Numeral 1))
                (SmtTerm.str_substr (__eo_to_smt y)
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                  (SmtTerm.Numeral 1))))
            native_nat_zero) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
  let one := SmtTerm.Numeral 1
  let idx := SmtTerm.Var (native_string_lit "@x") SmtType.Int
  let xSub := SmtTerm.str_substr (__eo_to_smt x) idx one
  let ySub := SmtTerm.str_substr (__eo_to_smt y) idx one
  let body := SmtTerm.not (SmtTerm.eq xSub ySub)
  have hChoiceNN :
      term_has_non_none_type
        (SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int body 0) := by
    unfold term_has_non_none_type
    simpa [one, idx, xSub, ySub, body] using h
  have hBodyBool : __smtx_typeof body = SmtType.Bool :=
    choice_nth_body_bool_of_non_none hChoiceNN
  have hEqBool : __smtx_typeof (SmtTerm.eq xSub ySub) = SmtType.Bool :=
    smtx_typeof_not_arg_bool _ hBodyBool
  have hEqNN :
      __smtx_typeof_eq (__smtx_typeof xSub) (__smtx_typeof ySub) ≠
        SmtType.None := by
    intro hNone
    rw [typeof_eq_eq xSub ySub] at hEqBool
    rw [hNone] at hEqBool
    cases hEqBool
  have hEqArgs := smtx_typeof_eq_non_none hEqNN
  have hXSubNN : term_has_non_none_type xSub := by
    unfold term_has_non_none_type
    exact hEqArgs.2
  have hYSubNN : term_has_non_none_type ySub := by
    unfold term_has_non_none_type
    intro hNone
    exact hEqArgs.2 (by rw [hEqArgs.1, hNone])
  rcases str_substr_args_of_non_none hXSubNN with
    ⟨A, hXSeq, _hIdxX, _hOneX⟩
  rcases str_substr_args_of_non_none hYSubNN with
    ⟨B, hYSeq, _hIdxY, _hOneY⟩
  exact
    ⟨smt_typeof_non_none_of_eq_non_none hXSeq (by simp),
      smt_typeof_non_none_of_eq_non_none hYSeq (by simp)⟩

private theorem native_eo_to_smt_uop_indices_safe_of_skolemize_forall_non_none
    {xs F idx : Term}
    (ihForall :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) ≠
        SmtType.None ->
      native_eo_to_smt_uop_indices_safe
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) = true)
    (h :
      __smtx_typeof
          (__eo_to_smt
            (Term.UOp2 UserOp2._at_quantifiers_skolemize
              (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)
              idx)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) idx) =
      true := by
  change
    __smtx_typeof
        (native_eo_to_smt_guard_closed
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_quantifiers_skolemize
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))
              (__eo_to_smt_nat idx))
            SmtTerm.None)) ≠
      SmtType.None at h
  have hForallClosed :
      native_eo_to_smt_closed
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) =
        true :=
    native_eo_to_smt_closed_of_guard_type_non_none h
  have hGuardBody :
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_quantifiers_skolemize
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))
              (__eo_to_smt_nat idx))
            SmtTerm.None) ≠
        SmtType.None :=
    guard_body_type_non_none_of_guard_type_non_none h
  have hIdxValid : __eo_to_smt_nat_is_valid idx = true := by
    cases hIdx : __eo_to_smt_nat_is_valid idx
    · exfalso
      apply hGuardBody
      simp [native_ite, hIdx, TranslationProofs.smtx_typeof_none]
    · rfl
  have hSkolNN :
      __smtx_typeof
          (__eo_to_smt_quantifiers_skolemize
            (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))
            (__eo_to_smt_nat idx)) ≠
        SmtType.None := by
    simpa [native_ite, hIdxValid] using hGuardBody
  have hBodyNoExists :
      ∀ s T body, SmtTerm.not (__eo_to_smt F) ≠ SmtTerm.exists s T body := by
    intro s T body hEq
    cases hEq
  have hExistsBool :
      __smtx_typeof
          (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool :=
    smtx_typeof_eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
      xs (SmtTerm.not (__eo_to_smt F)) (__eo_to_smt_nat idx)
      hBodyNoExists hSkolNN
  have hForallNN :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) ≠
        SmtType.None := by
    cases xs
    case __eo_List_nil =>
      exfalso
      apply hSkolNN
      simp [__eo_to_smt_exists, __eo_to_smt_quantifiers_skolemize,
        TranslationProofs.smtx_typeof_none]
    all_goals
      change
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt F)))) ≠
          SmtType.None
      rw [typeof_not_eq, hExistsBool]
      simp [native_Teq, native_ite]
  exact native_eo_to_smt_uop_indices_safe_uop2_intro
    hForallClosed
    (native_eo_to_smt_closed_of_nat_valid hIdxValid)
    (ihForall hForallNN)
    (native_eo_to_smt_uop_indices_safe_of_nat_valid hIdxValid)

private theorem native_eo_to_smt_uop_indices_safe_of_uop2_non_none
    {op : UserOp2} {x y : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (ihy :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe y = true)
    (h : __smtx_typeof (__eo_to_smt (Term.UOp2 op x y)) ≠ SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.UOp2 op x y) = true := by
  cases op
  case _at_array_deq_diff =>
    change
      __smtx_typeof
          (native_eo_to_smt_guard_closed x
            (native_eo_to_smt_guard_closed y
              (__eo_to_smt_array_deq_diff (__eo_to_smt x)
                (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                (__smtx_typeof (__eo_to_smt y))))) ≠
        SmtType.None at h
    exact native_eo_to_smt_uop_indices_safe_of_guarded_uop2_non_none
      (op := UserOp2._at_array_deq_diff) ihx ihy
      native_eo_to_smt_array_deq_diff_args_non_none h
  case _at_bv =>
    rcases eo_to_smt_at_bv_of_non_none
        (a := __eo_to_smt x) (b := __eo_to_smt y) (by simpa using h) with
      ⟨n, w, hxNum, hyNum, _hw, _hTy⟩
    exact native_eo_to_smt_uop_indices_safe_uop2_intro
      (native_eo_to_smt_closed_of_smt_numeral hxNum)
      (native_eo_to_smt_closed_of_smt_numeral hyNum)
      (native_eo_to_smt_uop_indices_safe_of_smt_numeral hxNum)
      (native_eo_to_smt_uop_indices_safe_of_smt_numeral hyNum)
  case _at_strings_deq_diff =>
    change
      __smtx_typeof
          (native_eo_to_smt_guard_closed x
            (native_eo_to_smt_guard_closed y
              (SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int
                (SmtTerm.not
                  (SmtTerm.eq
                    (SmtTerm.str_substr (__eo_to_smt x)
                      (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                      (SmtTerm.Numeral 1))
                    (SmtTerm.str_substr (__eo_to_smt y)
                      (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                      (SmtTerm.Numeral 1))))
                native_nat_zero))) ≠
        SmtType.None at h
    exact native_eo_to_smt_uop_indices_safe_of_guarded_uop2_non_none
      (op := UserOp2._at_strings_deq_diff) ihx ihy
      native_eo_to_smt_strings_deq_diff_args_non_none h
  case _at_sets_deq_diff =>
    change
      __smtx_typeof
          (native_eo_to_smt_guard_closed x
            (native_eo_to_smt_guard_closed y
              (__eo_to_smt_sets_deq_diff (__eo_to_smt x)
                (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                (__smtx_typeof (__eo_to_smt y))))) ≠
        SmtType.None at h
    exact native_eo_to_smt_uop_indices_safe_of_guarded_uop2_non_none
      (op := UserOp2._at_sets_deq_diff) ihx ihy
      native_eo_to_smt_sets_deq_diff_args_non_none h
  case _at_quantifiers_skolemize =>
    cases x
    case Apply f F =>
      cases f
      case Apply q xs =>
        cases q
        case UOp op =>
          cases op
          case «forall» =>
            exact
              native_eo_to_smt_uop_indices_safe_of_skolemize_forall_non_none
                (xs := xs) (F := F) (idx := y) ihx h
          all_goals
            exfalso
            apply h
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact TranslationProofs.smtx_typeof_none
        all_goals
          exfalso
          apply h
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      all_goals
        exfalso
        apply h
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    all_goals
      exfalso
      apply h
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case extract =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case re_loop =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case _at_strings_num_occur_re =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case _at_strings_occur_index_re =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case _at_const =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

private theorem native_eo_to_smt_uop_indices_safe_of_apply_extract_non_none
    {hi lo x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) = true := by
  change __smtx_typeof
      (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases extract_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨i, j, w, hHi, hLo, hxTy, _hj0, _hji, _hiw⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop2_of_smt_numerals
      (op := UserOp2.extract) hHi hLo)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem smt_re_loop_args_of_non_none
    {a b x : SmtTerm}
    (h : __smtx_typeof (SmtTerm.re_loop a b x) ≠ SmtType.None) :
    ∃ i j : native_Int,
      a = SmtTerm.Numeral i ∧ b = SmtTerm.Numeral j ∧
        __smtx_typeof x = SmtType.RegLan := by
  cases a
  case Numeral aN =>
    cases b
    case Numeral bN =>
      have hTerm :
          term_has_non_none_type
            (SmtTerm.re_loop (SmtTerm.Numeral aN) (SmtTerm.Numeral bN) x) := by
        unfold term_has_non_none_type
        exact h
      exact ⟨aN, bN, rfl, rfl, (re_loop_arg_of_non_none hTerm).2.2⟩
    all_goals
      exfalso
      apply h
      rw [typeof_re_loop_eq]
      simp [__smtx_typeof_re_loop]
  all_goals
    exfalso
    apply h
    rw [typeof_re_loop_eq]
    simp [__smtx_typeof_re_loop]

private theorem native_eo_to_smt_uop_indices_safe_of_apply_re_loop_non_none
    {lo hi x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) = true := by
  change __smtx_typeof
      (SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases smt_re_loop_args_of_non_none h with
    ⟨i, j, hLo, hHi, hxTy⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop2_of_smt_numerals
      (op := UserOp2.re_loop) hLo hHi)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_uop3_non_none
    {op : UserOp3} {x y z : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (ihy :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe y = true)
    (ihz :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe z = true)
    (h : __smtx_typeof (__eo_to_smt (Term.UOp3 op x y z)) ≠ SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.UOp3 op x y z) = true := by
  cases op
  case _at_re_unfold_pos_component =>
    change
      __smtx_typeof
          (native_eo_to_smt_guard_closed x
            (native_eo_to_smt_guard_closed y
              (native_ite (__eo_to_smt_nat_is_valid z)
                (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x)
                  (__eo_to_smt y) (__eo_to_smt_nat z))
                SmtTerm.None))) ≠
        SmtType.None at h
    have hxClosed :
        native_eo_to_smt_closed x = true :=
      native_eo_to_smt_closed_of_guard_type_non_none h
    have hInner :
        __smtx_typeof
            (native_eo_to_smt_guard_closed y
              (native_ite (__eo_to_smt_nat_is_valid z)
                (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x)
                  (__eo_to_smt y) (__eo_to_smt_nat z))
                SmtTerm.None)) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none h
    have hyClosed :
        native_eo_to_smt_closed y = true :=
      native_eo_to_smt_closed_of_guard_type_non_none hInner
    have hBody :
        __smtx_typeof
            (native_ite (__eo_to_smt_nat_is_valid z)
              (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x)
                (__eo_to_smt y) (__eo_to_smt_nat z))
              SmtTerm.None) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none hInner
    have hzValid : __eo_to_smt_nat_is_valid z = true := by
      cases hz : __eo_to_smt_nat_is_valid z
      · exfalso
        apply hBody
        simp [native_ite, hz, TranslationProofs.smtx_typeof_none]
      · rfl
    have hReNN :
        term_has_non_none_type
          (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x)
            (__eo_to_smt y) (__eo_to_smt_nat z)) := by
      unfold term_has_non_none_type
      simpa [native_ite, hzValid] using hBody
    have hArgs :=
      smtx_typeof_re_unfold_pos_component_args_of_non_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt_nat z) hReNN
    exact native_eo_to_smt_uop_indices_safe_uop3_intro
      hxClosed hyClosed (native_eo_to_smt_closed_of_nat_valid hzValid)
      (ihx (smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp)))
      (ihy (smt_typeof_non_none_of_eq_non_none hArgs.2 (by simp)))
      (native_eo_to_smt_uop_indices_safe_of_nat_valid hzValid)
  case _at_witness_string_length =>
    let ST := __eo_to_smt_type x
    let body :=
      SmtTerm.eq
        (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") ST))
        (__eo_to_smt y)
    change
      __smtx_typeof
          (native_eo_to_smt_guard_closed y
            (native_eo_to_smt_guard_closed z
              (native_ite (native_Teq (__smtx_typeof (__eo_to_smt z)) SmtType.Int)
                (SmtTerm.choice_nth (native_string_lit "@x") ST body native_nat_zero)
                SmtTerm.None))) ≠
        SmtType.None at h
    have hyClosed :
        native_eo_to_smt_closed y = true :=
      native_eo_to_smt_closed_of_guard_type_non_none h
    have hInner :
        __smtx_typeof
            (native_eo_to_smt_guard_closed z
              (native_ite (native_Teq (__smtx_typeof (__eo_to_smt z)) SmtType.Int)
                (SmtTerm.choice_nth (native_string_lit "@x") ST body native_nat_zero)
                SmtTerm.None)) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none h
    have hzClosed :
        native_eo_to_smt_closed z = true :=
      native_eo_to_smt_closed_of_guard_type_non_none hInner
    have hBody :
        __smtx_typeof
            (native_ite (native_Teq (__smtx_typeof (__eo_to_smt z)) SmtType.Int)
              (SmtTerm.choice_nth (native_string_lit "@x") ST body native_nat_zero)
              SmtTerm.None) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none hInner
    have hzInt : __smtx_typeof (__eo_to_smt z) = SmtType.Int := by
      cases hTest : native_Teq (__smtx_typeof (__eo_to_smt z)) SmtType.Int
      · exfalso
        apply hBody
        simp [native_ite, hTest, TranslationProofs.smtx_typeof_none]
      · simpa [native_Teq] using hTest
    have hChoiceNN :
        term_has_non_none_type
          (SmtTerm.choice_nth (native_string_lit "@x") ST body 0) := by
      unfold term_has_non_none_type
      simpa [native_ite, hzInt, native_Teq] using hBody
    have hBodyBool : __smtx_typeof body = SmtType.Bool :=
      choice_nth_body_bool_of_non_none hChoiceNN
    have hEqNN :
        __smtx_typeof_eq
            (__smtx_typeof
              (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") ST)))
            (__smtx_typeof (__eo_to_smt y)) ≠
          SmtType.None := by
      have hBodyNN : __smtx_typeof body ≠ SmtType.None := by
        rw [hBodyBool]
        simp
      simpa [body, typeof_eq_eq] using hBodyNN
    have hEqArgs := smtx_typeof_eq_non_none hEqNN
    have hyNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
      intro hyNone
      exact hEqArgs.2 (by rw [hEqArgs.1, hyNone])
    have hChoiceGuard :
        __smtx_typeof (SmtTerm.choice_nth (native_string_lit "@x") ST body 0) =
          __smtx_typeof_guard_wf ST ST :=
      choice_term_guard_type_of_non_none hChoiceNN
    have hGuardNN : __smtx_typeof_guard_wf ST ST ≠ SmtType.None := by
      intro hNone
      unfold term_has_non_none_type at hChoiceNN
      exact hChoiceNN (by rw [hChoiceGuard, hNone])
    have hTWF : __smtx_type_wf (__eo_to_smt_type x) = true := by
      simpa [ST] using smtx_typeof_guard_wf_wf_of_non_none ST ST hGuardNN
    rcases native_eo_to_smt_uop_indices_safe_of_smt_type_wf
        (T := x) hTWF with
      ⟨hxClosed, hxSafe⟩
    exact native_eo_to_smt_uop_indices_safe_uop3_intro
      hxClosed hyClosed hzClosed hxSafe (ihy hyNN)
      (ihz (smt_typeof_non_none_of_eq_non_none hzInt (by simp)))

/--
If a term translates to a well-typed SMT term, then every indexed EO operator
occurrence in it has standalone-closed immediate indices.

The guarded branches in `__eo_to_smt` should discharge the opaque term-index
cases; the numeric-index branches are intended to be discharged from the SMT
typing rules that require their indices to translate to `SmtTerm.Numeral`.
-/
theorem eo_to_smt_well_typed_implies_uop_indices_safe
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    NativeEoToSmtUOpIndicesSafe t := by
  let rec go : (u : Term) ->
      __smtx_typeof (__eo_to_smt u) ≠ SmtType.None ->
      NativeEoToSmtUOpIndicesSafe u
    | u, h => by
        cases u <;>
          simp [NativeEoToSmtUOpIndicesSafe,
            native_eo_to_smt_uop_indices_safe] at h ⊢
        case UOp1 op x =>
          simpa [NativeEoToSmtUOpIndicesSafe,
            native_eo_to_smt_uop_indices_safe] using
            native_eo_to_smt_uop_indices_safe_of_uop1_non_none
              (x := x) (op := op) (fun hx => go x hx) h
        case UOp2 op x y =>
          simpa [NativeEoToSmtUOpIndicesSafe,
            native_eo_to_smt_uop_indices_safe] using
            native_eo_to_smt_uop_indices_safe_of_uop2_non_none
              (x := x) (y := y) (op := op)
              (fun hx => go x hx) (fun hy => go y hy) h
        case UOp3 op x y z =>
          simpa [NativeEoToSmtUOpIndicesSafe,
            native_eo_to_smt_uop_indices_safe] using
            native_eo_to_smt_uop_indices_safe_of_uop3_non_none
              (x := x) (y := y) (z := z) (op := op)
              (fun hx => go x hx) (fun hy => go y hy)
              (fun hz => go z hz) h
        case Apply f x =>
          by_cases hfDistinct : f = Term.UOp UserOp.distinct
          · subst f
            simpa [NativeEoToSmtUOpIndicesSafe,
              native_eo_to_smt_uop_indices_safe] using
              native_eo_to_smt_uop_indices_safe_of_apply_distinct_non_none
                (xs := x) (Term.Apply (Term.UOp UserOp.distinct) x)
                (fun y _hyLt hy => go y hy) (by simp) h
          by_cases hfExists :
              ∃ xs, f = Term.Apply (Term.UOp UserOp.exists) xs
          · rcases hfExists with ⟨xs, rfl⟩
            simpa [NativeEoToSmtUOpIndicesSafe,
              native_eo_to_smt_uop_indices_safe] using
              native_eo_to_smt_uop_indices_safe_of_apply_exists_non_none
                (xs := xs) (F := x)
                (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) x)
                (fun y _hyLt hy => go y hy) (by simp; omega)
                (by simp; omega) h
          by_cases hfForall :
              ∃ xs, f = Term.Apply (Term.UOp UserOp.forall) xs
          · rcases hfForall with ⟨xs, rfl⟩
            simpa [NativeEoToSmtUOpIndicesSafe,
              native_eo_to_smt_uop_indices_safe] using
              native_eo_to_smt_uop_indices_safe_of_apply_forall_non_none
                (xs := xs) (F := x)
                (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) x)
                (fun y _hyLt hy => go y hy) (by simp; omega)
                (by simp; omega) h
          cases f with
          | UOp1 op idx =>
            cases op with
            | «repeat» =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_repeat_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | zero_extend =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_zero_extend_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | sign_extend =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_sign_extend_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | rotate_left =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_rotate_left_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | rotate_right =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_rotate_right_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | _at_bit =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_at_bit_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | re_exp =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_re_exp_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | _at_strings_stoi_result =>
              change
                __smtx_typeof
                    (native_eo_to_smt_guard_closed idx
                      (SmtTerm.str_to_int
                        (SmtTerm.str_substr (__eo_to_smt idx)
                          (SmtTerm.Numeral 0) (__eo_to_smt x)))) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_guarded_uop1_apply_non_none
                  (op := UserOp1._at_strings_stoi_result)
                  (idx := idx) (x := x)
                  (body :=
                    SmtTerm.str_to_int
                      (SmtTerm.str_substr (__eo_to_smt idx)
                        (SmtTerm.Numeral 0) (__eo_to_smt x)))
                  (fun hidx => go idx hidx) (fun hx => go x hx)
                  native_eo_to_smt_strings_stoi_result_args_non_none h
            | _at_strings_itos_result =>
              change
                __smtx_typeof
                    (native_eo_to_smt_guard_closed idx
                      (SmtTerm.mod (__eo_to_smt idx)
                        (SmtTerm.multmult (SmtTerm.Numeral 10)
                          (__eo_to_smt x)))) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_guarded_uop1_apply_non_none
                  (op := UserOp1._at_strings_itos_result)
                  (idx := idx) (x := x)
                  (body :=
                    SmtTerm.mod (__eo_to_smt idx)
                      (SmtTerm.multmult (SmtTerm.Numeral 10)
                        (__eo_to_smt x)))
                  (fun hidx => go idx hidx) (fun hx => go x hx)
                  native_eo_to_smt_strings_itos_result_args_non_none h
            | int_to_bv =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_int_to_bv_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | _at_purify =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt (Term.UOp1 UserOp1._at_purify idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1._at_purify idx) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1._at_purify idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | seq_empty =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt (Term.UOp1 UserOp1.seq_empty idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1.seq_empty idx) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1.seq_empty idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | _at_strings_stoi_non_digit =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt
                        (Term.UOp1 UserOp1._at_strings_stoi_non_digit idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1._at_strings_stoi_non_digit idx)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1._at_strings_stoi_non_digit idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | _at_strings_replace_all_result =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt
                        (Term.UOp1 UserOp1._at_strings_replace_all_result idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1._at_strings_replace_all_result idx)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1._at_strings_replace_all_result idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | is =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_is_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | update =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt (Term.UOp1 UserOp1.update idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1.update idx) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1.update idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | tuple_select =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_tuple_select_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | tuple_update =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt (Term.UOp1 UserOp1.tuple_update idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1.tuple_update idx) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1.tuple_update idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | set_empty =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt (Term.UOp1 UserOp1.set_empty idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1.set_empty idx) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1.set_empty idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
          | UOp2 op idx1 idx2 =>
            cases op with
            | extract =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_extract_non_none
                  (hi := idx1) (lo := idx2) (x := x)
                  (fun hx => go x hx) h
            | re_loop =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_re_loop_non_none
                  (lo := idx1) (hi := idx2) (x := x)
                  (fun hx => go x hx) h
            | _at_array_deq_diff =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_array_deq_diff idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_array_deq_diff idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_bv =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_bv idx1 idx2) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_bv idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_strings_deq_diff =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_strings_deq_diff idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_strings_deq_diff idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_strings_num_occur_re =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_strings_num_occur_re idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_strings_num_occur_re idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_strings_occur_index_re =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_strings_occur_index_re idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_strings_occur_index_re idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_sets_deq_diff =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_sets_deq_diff idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_sets_deq_diff idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_quantifiers_skolemize =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_quantifiers_skolemize idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_quantifiers_skolemize idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_const =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_const idx1 idx2) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_const idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
          | UOp3 op idx1 idx2 idx3 =>
            simpa [NativeEoToSmtUOpIndicesSafe] using
              native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                (f := Term.UOp3 op idx1 idx2 idx3) (x := x)
                (fun hf => by
                  simpa [NativeEoToSmtUOpIndicesSafe] using
                    go (Term.UOp3 op idx1 idx2 idx3) hf)
                (fun hx => by
                  simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                (by rfl) h
          | UOp op => sorry
          | Apply g y => sorry
          | _ => sorry
        all_goals
          trivial
  exact go t
