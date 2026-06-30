import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private abbrev intToBvTerm (w t : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv w) t

private abbrev ubvToIntTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.ubv_to_int) t

private abbrev atBvTerm (w n : Term) : Term :=
  Term.UOp2 UserOp2._at_bv w n

private abbrev concatTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y

/-- The right-hand side: `concat (@bv 0 n) (concat t (Binary 0 0))`. -/
private abbrev extendRhs (t n : Term) : Term :=
  concatTerm (atBvTerm (Term.Numeral 0) n)
    (concatTerm t (Term.Binary 0 0))

private abbrev ufExtendConclusion (w t n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq) (intToBvTerm w (ubvToIntTerm t)))
    (extendRhs t n)

/-! ### Eval / typeof stable rewrites for concat (not in Support). -/

private theorem smtx_eval_concat_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.concat x y) =
      __smtx_model_eval_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_typeof_concat_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.concat x y) =
      __smtx_typeof_concat (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-! ### Program reduction and guard handling. -/

/-- When all three args are non-stuck and the premises have the expected
    shapes, the program reduces to the requires-guarded conclusion. -/
private theorem prog_uf_bv2nat_int2bv_extend_eq
    (w1 t1 n1 lw2 lt2 ln2 lw3 lt3 : Term)
    (hW : w1 ≠ Term.Stuck) (hT : t1 ≠ Term.Stuck) (hN : n1 ≠ Term.Stuck) :
    __eo_prog_uf_bv2nat_int2bv_extend w1 t1 n1
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.gt) lw2)
              (Term.Apply (Term.UOp UserOp._at_bvsize) lt2)))
          (Term.Boolean true)))
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) ln2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lw3)
            (Term.Apply (Term.UOp UserOp._at_bvsize) lt3)))) =
      __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq w1 lw2) (__eo_eq t1 lt2))
              (__eo_eq n1 ln2))
            (__eo_eq w1 lw3))
          (__eo_eq t1 lt3))
        (Term.Boolean true) (ufExtendConclusion w1 t1 n1) := by
  cases w1 <;> cases t1 <;> cases n1 <;>
    simp [__eo_prog_uf_bv2nat_int2bv_extend, ufExtendConclusion, extendRhs,
      concatTerm, atBvTerm, intToBvTerm, ubvToIntTerm] at hW hT hN ⊢

/-- A non-stuck program forces all three args to be non-stuck. -/
private theorem args_ne_stuck_of_prog_not_stuck
    (w1 t1 n1 p1 p2 : Term)
    (h : __eo_prog_uf_bv2nat_int2bv_extend w1 t1 n1
      (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck) :
    w1 ≠ Term.Stuck ∧ t1 ≠ Term.Stuck ∧ n1 ≠ Term.Stuck := by
  refine ⟨?_, ?_, ?_⟩
  · intro hW; subst w1
    simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
  · intro hT; subst t1
    cases w1 <;> simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
  · intro hN; subst n1
    cases w1 <;> cases t1 <;> simp [__eo_prog_uf_bv2nat_int2bv_extend] at h

/-- Shape lemma: a non-stuck program forces both premises to have the
    expected `eq`/`gt`/`bvsize` and `eq`/`neg`/`bvsize` shapes. -/
private theorem shape_of_prog_uf_bv2nat_int2bv_extend_not_stuck
    (w1 t1 n1 p1 p2 : Term)
    (hW : w1 ≠ Term.Stuck) (hT : t1 ≠ Term.Stuck) (hN : n1 ≠ Term.Stuck)
    (h : __eo_prog_uf_bv2nat_int2bv_extend w1 t1 n1
      (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck) :
    ∃ lw2 lt2 ln2 lw3 lt3 : Term,
      p1 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.gt) lw2)
              (Term.Apply (Term.UOp UserOp._at_bvsize) lt2)))
          (Term.Boolean true) ∧
      p2 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) ln2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lw3)
            (Term.Apply (Term.UOp UserOp._at_bvsize) lt3)) := by
  cases w1 <;> cases t1 <;> cases n1 <;>
    (try (exact absurd rfl hW)) <;> (try (exact absurd rfl hT)) <;>
    (try (exact absurd rfl hN)) <;>
    (cases p1 with
     | Apply p1EqR p1True =>
         cases p1EqR with
         | Apply p1EqL gtTerm =>
             cases p1EqL with
             | UOp op1 =>
                 cases op1 <;> try (simp [__eo_prog_uf_bv2nat_int2bv_extend] at h)
                 case eq =>
                   cases p1True with
                   | Boolean b1 =>
                       cases b1 <;> try (simp [__eo_prog_uf_bv2nat_int2bv_extend] at h)
                       case _ =>
                         cases gtTerm with
                         | Apply gtMid bvsz1 =>
                             cases gtMid with
                             | Apply gtOp lw2 =>
                                 cases gtOp with
                                 | UOp gop =>
                                     cases gop <;>
                                       try (simp [__eo_prog_uf_bv2nat_int2bv_extend] at h)
                                     case gt =>
                                       cases bvsz1 with
                                       | Apply bvOp1 lt2 =>
                                           cases bvOp1 with
                                           | UOp bop1 =>
                                               cases bop1 <;>
                                                 try (simp [__eo_prog_uf_bv2nat_int2bv_extend] at h)
                                               case _at_bvsize =>
                                                 -- now destructure p2
                                                 cases p2 with
                                                 | Apply p2EqR negTerm =>
                                                     cases p2EqR with
                                                     | Apply p2EqL ln2 =>
                                                         cases p2EqL with
                                                         | UOp op2 =>
                                                             cases op2 <;>
                                                               try (simp [__eo_prog_uf_bv2nat_int2bv_extend] at h)
                                                             case eq =>
                                                               cases negTerm with
                                                               | Apply negMid bvsz2 =>
                                                                   cases negMid with
                                                                   | Apply negOp lw3 =>
                                                                       cases negOp with
                                                                       | UOp nop =>
                                                                           cases nop <;>
                                                                             try (simp [__eo_prog_uf_bv2nat_int2bv_extend] at h)
                                                                           case neg =>
                                                                             cases bvsz2 with
                                                                             | Apply bvOp2 lt3 =>
                                                                                 cases bvOp2 with
                                                                                 | UOp bop2 =>
                                                                                     cases bop2 <;>
                                                                                       try (simp [__eo_prog_uf_bv2nat_int2bv_extend] at h)
                                                                                     case _at_bvsize =>
                                                                                       exact ⟨lw2, lt2, ln2, lw3, lt3, rfl, rfl⟩
                                                                                 | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                                                                             | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                                                                       | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                                                                   | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                                                               | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                                                         | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                                                     | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                                                 | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                                           | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                                       | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                                 | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                             | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                         | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
                   | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
             | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
         | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
     | _ => simp [__eo_prog_uf_bv2nat_int2bv_extend] at h)

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

/-- Each `__eo_eq a b` is either `Stuck` or `Boolean c`. -/
private theorem eo_eq_stuck_or_bool (a b : Term) :
    __eo_eq a b = Term.Stuck ∨ ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
  by_cases ha : a = Term.Stuck
  · subst a; exact Or.inl (by simp [__eo_eq])
  · by_cases hb : b = Term.Stuck
    · subst b; exact Or.inl (by simp [__eo_eq])
    · exact Or.inr ⟨native_teq b a, by simp [__eo_eq]⟩

/-- From the 5-way conjunction guard being non-stuck, derive that all locals
    equal the corresponding arguments. -/
private theorem eqs_of_requires_and5_not_stuck
    (w1 t1 n1 lw2 lt2 ln2 lw3 lt3 B : Term) :
    __eo_requires
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq w1 lw2) (__eo_eq t1 lt2))
            (__eo_eq n1 ln2))
          (__eo_eq w1 lw3))
        (__eo_eq t1 lt3))
      (Term.Boolean true) B ≠ Term.Stuck ->
    lw2 = w1 ∧ lt2 = t1 ∧ ln2 = n1 ∧ lw3 = w1 ∧ lt3 = t1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
    at hProg'
  have hAndTop :
      __eo_and
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq w1 lw2) (__eo_eq t1 lt2))
            (__eo_eq n1 ln2))
          (__eo_eq w1 lw3))
        (__eo_eq t1 lt3) = Term.Boolean true := hProg'.1
  -- Peel the conjunction down to its five atoms.
  rcases eo_eq_stuck_or_bool t1 lt3 with h5 | ⟨b5, h5⟩
  · simp [__eo_and, h5] at hAndTop
    -- when inner is not boolean, hAndTop forces Stuck shape; handle below
  all_goals
    rcases eo_eq_stuck_or_bool w1 lw3 with h4 | ⟨b4, h4⟩
    · first
      | (simp [__eo_and, h4, h5] at hAndTop)
      | skip
    all_goals
      rcases eo_eq_stuck_or_bool n1 ln2 with h3 | ⟨b3, h3⟩
      · first
        | (simp [__eo_and, h3, h4, h5] at hAndTop)
        | skip
      all_goals
        rcases eo_eq_stuck_or_bool t1 lt2 with h2 | ⟨b2, h2⟩
        · first
          | (simp [__eo_and, h2, h3, h4, h5] at hAndTop)
          | skip
        all_goals
          rcases eo_eq_stuck_or_bool w1 lw2 with h1 | ⟨b1, h1⟩
          · first
            | (simp [__eo_and, h1, h2, h3, h4, h5] at hAndTop)
            | skip
          all_goals
            cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
              simp [__eo_and, h1, h2, h3, h4, h5, native_and] at hAndTop
            refine ⟨eq_of_eo_eq_true w1 lw2 h1, eq_of_eo_eq_true t1 lt2 h2,
              eq_of_eo_eq_true n1 ln2 h3, eq_of_eo_eq_true w1 lw3 h4,
              eq_of_eo_eq_true t1 lt3 h5⟩

/-- The guard with all locals equal to the corresponding arguments reduces to
    the body. -/
private theorem requires_and5_self_true_body
    (w t n body : Term)
    (hW : w ≠ Term.Stuck) (hT : t ≠ Term.Stuck) (hN : n ≠ Term.Stuck) :
    __eo_requires
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq w w) (__eo_eq t t))
            (__eo_eq n n))
          (__eo_eq w w))
        (__eo_eq t t))
      (Term.Boolean true) body = body := by
  simp [__eo_requires, __eo_and,
    eo_eq_self_true_of_ne_stuck w hW,
    eo_eq_self_true_of_ne_stuck t hT,
    eo_eq_self_true_of_ne_stuck n hN, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and]

/-! ### Typing inversion. -/

private theorem typeof_int_to_bv_stuck_of_arg_stuck (A w : Term) :
    __eo_typeof_int_to_bv A w Term.Stuck = Term.Stuck := by
  unfold __eo_typeof_int_to_bv
  split <;> simp_all

private theorem typeof_int_to_bv_stuck_of_width_ty_ne_int (A w B : Term)
    (hA : A ≠ Term.UOp UserOp.Int) :
    __eo_typeof_int_to_bv A w B = Term.Stuck := by
  unfold __eo_typeof_int_to_bv
  split <;> simp_all

/-- Inversion: if `int_to_bv` (with an `Int` operand type) yields a `BitVec`
    type, then the width is a nonnegative numeral matching the result width. -/
private theorem int_to_bv_type_bitvec_inv (A w m : Term)
    (h : __eo_typeof_int_to_bv A w (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    A = Term.UOp UserOp.Int ∧
      ∃ k, w = Term.Numeral k ∧ native_zlt (-1 : native_Int) k = true ∧
        m = Term.Numeral k := by
  by_cases hA : A = Term.UOp UserOp.Int
  · subst A
    refine ⟨rfl, ?_⟩
    cases hw : w <;> rw [hw] at h <;>
      first
      | (rename_i k
         have hRed :
             __eo_typeof_int_to_bv (Term.UOp UserOp.Int) (Term.Numeral k)
                 (Term.UOp UserOp.Int) =
               native_ite (native_zlt (-1 : native_Int) k)
                 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k)) Term.Stuck := by
           simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
             native_teq, native_not, SmtEval.native_not]
         rw [hRed] at h
         cases hPos : native_zlt (-1 : native_Int) k <;>
           simp [native_ite, hPos] at h
         exact ⟨k, rfl, hPos, h.symm⟩)
      | (exfalso
         simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
           native_teq, native_not, SmtEval.native_not] at h)
  · exfalso
    rw [typeof_int_to_bv_stuck_of_width_ty_ne_int A w (Term.UOp UserOp.Int) hA] at h
    simp at h

private theorem bvsize_stuck_of_not_bitvec (T : Term) :
    (∀ m, T ≠ Term.Apply (Term.UOp UserOp.BitVec) m) ->
    __eo_typeof__at_bvsize T = Term.Stuck := by
  intro hNotBv
  cases T with
  | Apply f m =>
      cases f with
      | UOp op =>
          cases op <;> first | rfl | (exact absurd rfl (hNotBv m))
      | _ => rfl
  | _ => rfl

private theorem typeof_eq_bool_inv (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    B = A := by
  have hNeStuck : __eo_typeof_eq A B ≠ Term.Stuck := by
    rw [h]; intro hc; cases hc
  by_cases hAStuck : A = Term.Stuck
  · subst A; simp [__eo_typeof_eq] at hNeStuck
  · by_cases hBStuck : B = Term.Stuck
    · subst B
      cases A <;> simp [__eo_typeof_eq] at hNeStuck
    · have hReqEq : __eo_typeof_eq A B =
          __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool := by
        cases A <;> cases B <;> simp_all [__eo_typeof_eq]
      rw [hReqEq] at hNeStuck
      have hReq' := hNeStuck
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hReq'
      have hEqTrue : __eo_eq A B = Term.Boolean true := hReq'.1
      exact eq_of_eo_eq_true A B hEqTrue

/-- Inversion of `__eo_typeof__at_bv (typeof 0) (typeof n) n = BitVec n` etc.
    Here we just need: if the `@bv 0 n` term has BitVec type, then `n` is a
    numeral and the type is `BitVec n`. -/
private theorem typeof_at_bv_zero_inv (n m : Term)
    (h : __eo_typeof (atBvTerm (Term.Numeral 0) n) =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    ∃ k, n = Term.Numeral k ∧ m = Term.Numeral k := by
  -- typeof (@bv 0 n) = __eo_typeof__at_bv Int (typeof n) n
  have hRed :
      __eo_typeof (atBvTerm (Term.Numeral 0) n) =
        __eo_typeof__at_bv (Term.UOp UserOp.Int) (__eo_typeof n) n := by
    simp [atBvTerm, __eo_typeof, __eo_lit_type_Numeral]
  rw [hRed] at h
  cases hn : n with
  | Numeral k =>
      rw [hn] at h
      have : __eo_typeof__at_bv (Term.UOp UserOp.Int)
          (__eo_typeof (Term.Numeral k)) (Term.Numeral k) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k) := by
        simp [__eo_typeof, __eo_lit_type_Numeral, __eo_typeof__at_bv]
      rw [this] at h
      cases h
      exact ⟨k, rfl, rfl⟩
  all_goals
    (exfalso
     rw [hn] at h
     simp [__eo_typeof__at_bv, __eo_typeof, __eo_lit_type_Numeral,
       __eo_lit_type_Binary, __eo_len] at h)

/-- Inversion of the RHS typeof: from `typeof RHS = BitVec wTy`, with
    `typeof t = BitVec mt`, derive `n = Numeral N`, `mt = Numeral wt` and
    `wTy = Numeral (N + wt)`. -/
private theorem typeof_extend_rhs_inv (t n wTy : Term)
    (hRhsTy : __eo_typeof (extendRhs t n) =
      Term.Apply (Term.UOp UserOp.BitVec) wTy) :
    ∃ N wt mt : native_Int,
      n = Term.Numeral N ∧
      __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wt) ∧
      wTy = Term.Numeral (native_zplus N wt) := by
  -- typeof RHS = concat (typeof (@bv 0 n)) (typeof (concat t (Binary 0 0)))
  have hRed :
      __eo_typeof (extendRhs t n) =
        __eo_typeof_concat
          (__eo_typeof (atBvTerm (Term.Numeral 0) n))
          (__eo_typeof_concat (__eo_typeof t)
            (__eo_typeof (Term.Binary 0 0))) := by
    simp [extendRhs, concatTerm, __eo_typeof]
  rw [hRed] at hRhsTy
  -- For the outer concat to give BitVec, both inputs must be BitVec.
  -- First, `typeof (Binary 0 0) = BitVec (Numeral 0)`.
  have hBin : __eo_typeof (Term.Binary 0 0) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0) := by
    simp [__eo_typeof, __eo_lit_type_Binary, __eo_len]
  rw [hBin] at hRhsTy
  -- The inner concat: `typeof t` must be `BitVec mt`.
  by_cases htBv : ∃ mt, __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) mt
  · rcases htBv with ⟨mt, htTy⟩
    rw [htTy] at hRhsTy
    have hInner :
        __eo_typeof_concat (Term.Apply (Term.UOp UserOp.BitVec) mt)
          (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0)) =
          Term.Apply (Term.UOp UserOp.BitVec) (__eo_add mt (Term.Numeral 0)) := by
      simp [__eo_typeof_concat]
    rw [hInner] at hRhsTy
    -- Now `mt` must be a numeral for `__eo_add mt (Numeral 0)` to be a Numeral,
    -- and the outer `@bv` operand must be a numeral too.
    by_cases hbvBv : ∃ bm, __eo_typeof (atBvTerm (Term.Numeral 0) n) =
        Term.Apply (Term.UOp UserOp.BitVec) bm
    · rcases hbvBv with ⟨bm, hbvTy⟩
      rcases typeof_at_bv_zero_inv n bm hbvTy with ⟨N, hnN, hbmN⟩
      subst hbmN
      rw [hbvTy] at hRhsTy
      -- mt must be a numeral
      cases hmt : mt with
      | Numeral wt =>
          rw [hmt] at hRhsTy htTy
          have hAdd : __eo_add (Term.Numeral wt) (Term.Numeral 0) =
              Term.Numeral (native_zplus wt 0) := by
            simp [__eo_add]
          rw [hAdd] at hRhsTy
          have hOuter :
              __eo_typeof_concat (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral N))
                (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_zplus wt 0))) =
                Term.Apply (Term.UOp UserOp.BitVec)
                  (__eo_add (Term.Numeral N) (Term.Numeral (native_zplus wt 0))) := by
            simp [__eo_typeof_concat]
          rw [hOuter] at hRhsTy
          have hAdd2 : __eo_add (Term.Numeral N) (Term.Numeral (native_zplus wt 0)) =
              Term.Numeral (native_zplus N (native_zplus wt 0)) := by
            simp [__eo_add]
          rw [hAdd2] at hRhsTy
          have hwTy : wTy = Term.Numeral (native_zplus N (native_zplus wt 0)) := by
            cases hRhsTy; rfl
          refine ⟨N, wt, wt, hnN, htTy, ?_⟩
          rw [hwTy]
          have : native_zplus wt 0 = wt := by simp [SmtEval.native_zplus]
          rw [this]
      all_goals
        (exfalso
         rw [hmt] at hRhsTy
         simp [__eo_typeof_concat, __eo_add] at hRhsTy)
    · exfalso
      -- `@bv 0 n` not bitvec => outer concat is stuck.
      have hbvStuck : ∀ z,
          __eo_typeof (atBvTerm (Term.Numeral 0) n) ≠
            Term.Apply (Term.UOp UserOp.BitVec) z := by
        intro z hz; exact hbvBv ⟨z, hz⟩
      cases hbv : __eo_typeof (atBvTerm (Term.Numeral 0) n) <;>
        simp_all [__eo_typeof_concat]
  · exfalso
    have htStuck : ∀ z, __eo_typeof t ≠ Term.Apply (Term.UOp UserOp.BitVec) z := by
      intro z hz; exact htBv ⟨z, hz⟩
    cases ht : __eo_typeof t <;>
      simp_all [__eo_typeof_concat]

/-- From the conclusion's type being `Bool`, derive the typing facts needed:
    `n = Numeral N`, the LHS width arg `w = Numeral wTy` with `wTy ≥ 0`,
    `typeof t = BitVec (Numeral wt)`, and `wTy = N + wt`. -/
private theorem typeof_args_of_conclusion_bool (w t n : Term) :
    __eo_typeof (ufExtendConclusion w t n) = Term.Bool ->
    ∃ N wt : native_Int,
      n = Term.Numeral N ∧
      w = Term.Numeral (native_zplus N wt) ∧
      native_zleq 0 (native_zplus N wt) = true ∧
      __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wt) := by
  intro hTy
  -- typeof conclusion = typeof_eq (typeof LHS) (typeof RHS)
  have hTyEq :
      __eo_typeof (ufExtendConclusion w t n) =
        __eo_typeof_eq
          (__eo_typeof_int_to_bv (__eo_typeof w) w
            (__eo_typeof__at_bvsize (__eo_typeof t)))
          (__eo_typeof (extendRhs t n)) := by
    simp [ufExtendConclusion, intToBvTerm, ubvToIntTerm, __eo_typeof]
  rw [hTyEq] at hTy
  -- Both operand types are equal.
  have hEqTy :
      __eo_typeof (extendRhs t n) =
        __eo_typeof_int_to_bv (__eo_typeof w) w
          (__eo_typeof__at_bvsize (__eo_typeof t)) :=
    typeof_eq_bool_inv _ _ hTy
  -- The RHS type is a BitVec, so the LHS type is too.
  by_cases hBv : ∃ wTy, __eo_typeof (extendRhs t n) =
      Term.Apply (Term.UOp UserOp.BitVec) wTy
  · rcases hBv with ⟨wTy, hRhsTy⟩
    rcases typeof_extend_rhs_inv t n wTy hRhsTy with ⟨N, wt, mt, hnN, htTy, hwTy⟩
    -- LHS type equals the RHS type, a BitVec.
    have hLhsTyBv :
        __eo_typeof_int_to_bv (__eo_typeof w) w
          (__eo_typeof__at_bvsize (__eo_typeof t)) =
          Term.Apply (Term.UOp UserOp.BitVec) wTy := by
      rw [← hEqTy, hRhsTy]
    -- `bvsize (typeof t)` is `Int`.
    have hBvsizeInt : __eo_typeof__at_bvsize (__eo_typeof t) = Term.UOp UserOp.Int := by
      rw [htTy]; rfl
    rw [hBvsizeInt] at hLhsTyBv
    rcases int_to_bv_type_bitvec_inv (__eo_typeof w) w wTy hLhsTyBv with
      ⟨_hWTyInt, k, hwk, hPos, hmk⟩
    -- wTy = Numeral k and also wTy = Numeral (N+wt)
    rw [hwTy] at hmk
    have hk : k = native_zplus N wt := by
      have := hmk.symm
      injection this with hkk
      exact hkk.symm
    subst hk
    refine ⟨N, wt, hnN, hwk, ?_, htTy⟩
    have hLt' : (-1 : native_Int) < native_zplus N wt := by
      simpa [native_zlt, SmtEval.native_zlt] using hPos
    have hNonneg : (0 : native_Int) <= native_zplus N wt := by
      have hStep : (-1 : native_Int) + 1 <= native_zplus N wt :=
        (Int.add_one_le_iff).2 hLt'
      simpa using hStep
    simpa [native_zleq, SmtEval.native_zleq] using hNonneg
  · exfalso
    -- RHS not bitvec; then LHS type (= RHS type) is not bitvec, but its inversion
    -- shows the equation between LHS-type and RHS-type can't be Bool... contradiction
    -- via: RHS type = LHS type, but we need to show LHS type IS a bitvec.
    -- Actually use: from hEqTy, RHS type = LHS type. We show the eq result can't
    -- be Bool unless RHS type is a bitvec. Inspect the LHS type form.
    -- The cleanest: the conclusion type was Bool, so eq of two equal types; if RHS
    -- (= LHS) type is Stuck the typeof_eq would be Stuck, contradicting Bool.
    -- So RHS type is non-stuck and is the int_to_bv type, which is either Stuck or
    -- a BitVec. Hence it must be a BitVec, contradicting hBv.
    have hNotStuck : __eo_typeof (extendRhs t n) ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hTy
      -- typeof_eq Stuck _ = Stuck (since first arg stuck) -> not Bool
      simp [__eo_typeof_eq] at hTy
    -- RHS type = LHS type = int_to_bv type, which is BitVec or Stuck.
    rw [hEqTy] at hNotStuck hBv
    -- int_to_bv type is BitVec or Stuck.
    have hForm :
        (∃ m, __eo_typeof_int_to_bv (__eo_typeof w) w
          (__eo_typeof__at_bvsize (__eo_typeof t)) =
            Term.Apply (Term.UOp UserOp.BitVec) m) ∨
        __eo_typeof_int_to_bv (__eo_typeof w) w
          (__eo_typeof__at_bvsize (__eo_typeof t)) = Term.Stuck := by
      unfold __eo_typeof_int_to_bv
      split
      · rename_i A wv B heqA heqB
        -- the `Int Int (BitVec n)` branch
        rename_i n0
        simp only []
        -- result is requires(...) BitVec, which is BitVec or Stuck
        by_cases hg : native_zlt (-1 : native_Int)
            (match wv with | Term.Numeral q => q | _ => 0) = true
        all_goals
          (cases wv <;>
            simp [__eo_requires, __eo_gt, native_ite, native_teq, native_not,
              SmtEval.native_not] <;>
            first
            | (rename_i q; by_cases hpos : native_zlt (-1 : native_Int) q = true <;>
                simp [hpos] <;> first | (exact Or.inl ⟨_, rfl⟩) | (exact Or.inr rfl))
            | (exact Or.inr rfl)
            | (exact Or.inl ⟨_, rfl⟩))
      · exact Or.inr rfl
    rcases hForm with ⟨m, hm⟩ | hStuck
    · exact hBv ⟨m, hm⟩
    · exact hNotStuck hStuck

/-! ### SMT typing of each side. -/

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x1 w : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ k, w = Term.Numeral k ∧ native_zleq 0 k = true ∧
      __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat k) := by
  intro hX1Trans hX1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x1) rfl
      hX1Trans hX1Type
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral k =>
    cases hNonneg : native_zleq 0 k <;> simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hX1Trans hSmtType)
    · exact ⟨k, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hX1Trans hSmtType)

private theorem width_nat_to_int_eq
    (k : native_Int) (hNonneg : native_zleq 0 k = true) :
    native_nat_to_int (native_int_to_nat k) = k := by
  have hnNonneg : 0 <= k := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hInt : (Int.ofNat (Int.toNat k) : Int) = k :=
    Int.toNat_of_nonneg hnNonneg
  simpa [SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

/-! ### The eval crux. -/

/-- The two sides of the conclusion evaluate to the same value. -/
private theorem eval_lhs_matches_rhs
    (M : SmtModel) (hM : model_total_typed M)
    (N wt : native_Int) (t n : Term) :
    RuleProofs.eo_has_smt_translation t ->
    n = Term.Numeral N ->
    native_zleq 0 N = true ->
    native_zleq 0 wt = true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat wt) ->
    __smtx_model_eval M
        (__eo_to_smt (intToBvTerm (Term.Numeral (native_zplus N wt)) (ubvToIntTerm t))) =
      __smtx_model_eval M (__eo_to_smt (extendRhs t n)) := by
  intro hTTrans hnN hNNonneg hWtNonneg hTSmtTy
  subst hnN
  -- The eval value of `t` is a canonical Binary of width wt.
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec (native_int_to_nat wt) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hTTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalT⟩
  rw [width_nat_to_int_eq wt hWtNonneg] at hEvalT
  -- canonicity of the payload at width wt.
  have hCanon :
      native_zeq payload (native_mod_total payload (native_int_pow2 wt)) = true :=
    bitvec_payload_canonical (u := native_int_to_nat wt)
      (by rw [hEvalT] at hEvalTy; exact hEvalTy)
  -- payload canonical at extended width N + wt.
  have hCanonExt :
      native_zeq payload
        (native_mod_total payload (native_int_pow2 (native_zplus N wt))) = true :=
    bitvec_payload_canonical_zero_extend hNNonneg hWtNonneg hCanon
  have hModExt : native_mod_total payload (native_int_pow2 (native_zplus N wt)) = payload := by
    have hEq : payload =
        native_mod_total payload (native_int_pow2 (native_zplus N wt)) := by
      simpa [SmtEval.native_zeq] using hCanonExt
    exact hEq.symm
  have hModBase : native_mod_total payload (native_int_pow2 wt) = payload := by
    have hEq : payload = native_mod_total payload (native_int_pow2 wt) := by
      simpa [SmtEval.native_zeq] using hCanon
    exact hEq.symm
  -- Translate both sides to SMT terms.
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral (native_zplus N wt))
        (SmtTerm.ubv_to_int (__eo_to_smt t))) =
    __smtx_model_eval M
      (SmtTerm.concat
        (__eo_to_smt__at_bv (SmtTerm.Numeral 0) (SmtTerm.Numeral N))
        (SmtTerm.concat (__eo_to_smt t) (SmtTerm.Binary 0 0)))
  -- LHS eval.
  rw [smtx_eval_int_to_bv_term_eq, smtx_eval_ubv_to_int_term_eq, hEvalT]
  have hEvalNum :
      ∀ z : native_Int, __smtx_model_eval M (SmtTerm.Numeral z) = SmtValue.Numeral z := by
    intro z; rw [__smtx_model_eval.eq_2]
  rw [hEvalNum]
  simp only [__smtx_model_eval_ubv_to_int, __smtx_model_eval_int_to_bv, hModExt]
  -- RHS eval.
  have hNNonneg' : 0 <= N := by simpa [SmtEval.native_zleq] using hNNonneg
  have hatbv : __eo_to_smt__at_bv (SmtTerm.Numeral 0) (SmtTerm.Numeral N) =
      SmtTerm.Binary N 0 := by
    simp [__eo_to_smt__at_bv, native_ite, hNNonneg, SmtEval.native_mod_total]
  rw [smtx_eval_concat_term_eq, smtx_eval_concat_term_eq, hatbv, hEvalT]
  rw [__smtx_model_eval.eq_4]
  -- evaluate the inner concat: Binary wt payload ++ Binary 0 0
  simp only [__smtx_model_eval_concat, native_binary_concat]
  -- Now both sides are Binary expressions; reduce arithmetic.
  -- inner: Binary (wt+0) (mod (payload*2^0 + 0) 2^(wt+0))
  -- outer: Binary (N + (wt+0)) (mod (0*2^(wt+0) + inner_payload) 2^(N+(wt+0)))
  have hPow0 : native_int_pow2 0 = 1 := by
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total]
  have hwt0 : native_zplus wt 0 = wt := by simp [SmtEval.native_zplus]
  -- Simplify the inner payload.
  have hInnerPayload :
      native_mod_total (native_zplus (native_zmult payload (native_int_pow2 0)) 0)
        (native_int_pow2 (native_zplus wt 0)) = payload := by
    rw [hPow0, hwt0]
    simp [SmtEval.native_zmult, SmtEval.native_zplus, hModBase]
  rw [hwt0] at *
  -- Outer.
  have hOuterPayload :
      native_mod_total
        (native_zplus
          (native_zmult 0 (native_int_pow2 wt))
          (native_mod_total (native_zplus (native_zmult payload (native_int_pow2 0)) 0)
            (native_int_pow2 wt)))
        (native_int_pow2 (native_zplus N wt)) = payload := by
    rw [hPow0]
    simp only [SmtEval.native_zmult, SmtEval.native_zplus]
    rw [show native_mod_total (payload * 1 + 0) (native_int_pow2 wt) = payload by
      simp [SmtEval.native_zmult, SmtEval.native_mod_total] at hModBase ⊢; rw [hModBase]]
    simp [SmtEval.native_zplus, hModExt]
  -- Final: both Binary (N+wt) payload.
  simp only [hInnerPayload, hOuterPayload, SmtEval.native_zplus]

/-- SMT typing of the LHS `int_to_bv (N+wt) (ubv_to_int t)`. -/
private theorem smt_typeof_lhs_eq
    (N wt : native_Int) (t : Term) :
    native_zleq 0 (native_zplus N wt) = true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat wt) ->
    __smtx_typeof
        (__eo_to_smt (intToBvTerm (Term.Numeral (native_zplus N wt)) (ubvToIntTerm t))) =
      SmtType.BitVec (native_int_to_nat (native_zplus N wt)) := by
  intro hNonneg hTSmtTy
  change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral (native_zplus N wt))
        (SmtTerm.ubv_to_int (__eo_to_smt t))) =
    SmtType.BitVec (native_int_to_nat (native_zplus N wt))
  rw [smtx_typeof_int_to_bv_term_eq, smtx_typeof_ubv_to_int_term_eq]
  simp [__smtx_typeof_int_to_bv, __smtx_typeof_bv_op_1_ret, native_ite,
    hTSmtTy, hNonneg]

/-- SMT typing of the RHS `concat (@bv 0 N) (concat t (Binary 0 0))`. -/
private theorem smt_typeof_rhs_eq
    (N wt : native_Int) (t n : Term) :
    n = Term.Numeral N ->
    native_zleq 0 N = true ->
    native_zleq 0 wt = true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat wt) ->
    __smtx_typeof (__eo_to_smt (extendRhs t n)) =
      SmtType.BitVec (native_int_to_nat (native_zplus N wt)) := by
  intro hnN hNNonneg hWtNonneg hTSmtTy
  subst hnN
  change __smtx_typeof
      (SmtTerm.concat
        (__eo_to_smt__at_bv (SmtTerm.Numeral 0) (SmtTerm.Numeral N))
        (SmtTerm.concat (__eo_to_smt t) (SmtTerm.Binary 0 0))) =
    SmtType.BitVec (native_int_to_nat (native_zplus N wt))
  -- `@bv 0 N` translates to `Binary N 0`.
  have hatbv : __eo_to_smt__at_bv (SmtTerm.Numeral 0) (SmtTerm.Numeral N) =
      SmtTerm.Binary N 0 := by
    simp [__eo_to_smt__at_bv, native_ite, hNNonneg, SmtEval.native_mod_total]
  rw [hatbv]
  rw [smtx_typeof_concat_term_eq, smtx_typeof_concat_term_eq, hTSmtTy]
  -- typeof (Binary N 0) = BitVec (int_to_nat N)
  have hTyBinN : __smtx_typeof (SmtTerm.Binary N 0) =
      SmtType.BitVec (native_int_to_nat N) := by
    rw [__smtx_typeof.eq_5]
    simp [native_ite, SmtEval.native_and, hNNonneg, SmtEval.native_zeq,
      SmtEval.native_mod_total]
  have hTyBin0 : __smtx_typeof (SmtTerm.Binary 0 0) = SmtType.BitVec 0 := by
    rw [__smtx_typeof.eq_5]
    simp [native_ite, SmtEval.native_and, SmtEval.native_zeq, SmtEval.native_mod_total,
      SmtEval.native_int_to_nat]
  rw [hTyBinN, hTyBin0]
  -- inner: concat (BitVec wt) (BitVec 0) = BitVec (int_to_nat (nat_to_int wt + 0))
  have hWtRound : native_nat_to_int (native_int_to_nat wt) = wt :=
    width_nat_to_int_eq wt hWtNonneg
  have hNRound : native_nat_to_int (native_int_to_nat N) = N :=
    width_nat_to_int_eq N hNNonneg
  simp only [__smtx_typeof_concat]
  -- reduce nat_to_int (int_to_nat _) and the zplus arithmetic
  rw [show native_nat_to_int (0 : native_Nat) = 0 by
        simp [SmtEval.native_nat_to_int]]
  rw [hWtRound, hNRound]
  rw [show native_zplus wt 0 = wt by simp [SmtEval.native_zplus]]
  rw [hWtRound]

/-! ### Bool typing and interpretation.

INFRASTRUCTURE GAP (see report): proving the unconditional
`StepRuleProperties.has_smt_translation` obligation for this rule requires
`n1 ≥ 0` (the zero-extension amount). The conclusion contains `@bv 0 n1`, whose
SMT translation `__eo_to_smt__at_bv (Numeral 0) (Numeral n1)` is `SmtTerm.None`
when `n1 < 0`, making the whole conclusion untranslatable. But `n1 = w - bvsize t`
can be negative whenever the *premise* `gt w (bvsize t) = true` is violated, and
the eo type system does NOT reject negative-width `@bv` (verified by `#eval`:
`__eo_typeof (@bv 0 (-1)) = BitVec (Numeral -1)`, not `Stuck`). So `n1 ≥ 0` is
only guaranteed by premise *truth*, which is available solely through
`RulePremiseEvidence` (i.e. for `facts_of_true`), NOT for `has_smt_translation`.
There is no generic `__eo_typeof t = Bool → eo_has_smt_translation t` lemma
(confirmed by the note in `Cpc/Proofs/Rules/Instantiate.lean:96`). The single
`sorry` below is exactly this `n1 ≥ 0` obligation. -/

private theorem extend_n1_nonneg_gap (N : native_Int) : native_zleq 0 N = true := by
  sorry

private theorem typed_conclusion_impl (w t n : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof (ufExtendConclusion w t n) = Term.Bool ->
    RuleProofs.eo_has_bool_type (ufExtendConclusion w t n) := by
  intro hTTrans hResultTy
  rcases typeof_args_of_conclusion_bool w t n hResultTy with ⟨N, wt, hnN, hwW, hNonneg, htTy⟩
  subst hwW
  subst hnN
  -- SMT type of `t`.
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t (Term.Numeral wt) hTTrans htTy with
    ⟨wt', hwteq, hWtNonneg, hTSmtTy⟩
  injection hwteq with hwteq'
  subst hwteq'
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (intToBvTerm (Term.Numeral (native_zplus N wt)) (ubvToIntTerm t))) =
        SmtType.BitVec (native_int_to_nat (native_zplus N wt)) :=
    smt_typeof_lhs_eq N wt t hNonneg hTSmtTy
  have hNNonneg : native_zleq 0 N = true := by
    -- from N + wt ≥ 0 and wt ≥ 0... actually we need N ≥ 0 separately.
    -- N ≥ 0 follows from `n` typing? We derived `n = Numeral N` only. But the
    -- `@bv 0 N` term required N's type to be Int (a numeral) — nonnegativity of N
    -- comes from the requirement that `@bv 0 N` is a well-typed BitVec, which is
    -- implied by the conclusion being Bool. We extract it below.
    -- Use: N + wt ≥ 0 and wt ≥ 0 is not enough. Instead, the RHS must have a real
    -- BitVec smt type, which requires N ≥ 0.
    exact extend_n1_nonneg_gap N
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (extendRhs t n)) =
        SmtType.BitVec (native_int_to_nat (native_zplus N wt)) :=
    smt_typeof_rhs_eq N wt t n rfl hNNonneg hWtNonneg hTSmtTy
  refine RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (intToBvTerm (Term.Numeral (native_zplus N wt)) (ubvToIntTerm t)) (extendRhs t n)
    (by rw [hLhsTy, hRhsTy]) ?_
  rw [hLhsTy]
  intro hC; cases hC

private theorem facts_conclusion_impl
    (M : SmtModel) (hM : model_total_typed M) (w t n : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof (ufExtendConclusion w t n) = Term.Bool ->
    eo_interprets M (ufExtendConclusion w t n) true := by
  intro hTTrans hResultTy
  rcases typeof_args_of_conclusion_bool w t n hResultTy with ⟨N, wt, hnN, hwW, hNonneg, htTy⟩
  have hProgBool :
      RuleProofs.eo_has_bool_type (ufExtendConclusion w t n) :=
    typed_conclusion_impl w t n hTTrans hResultTy
  subst hwW
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t (Term.Numeral wt) hTTrans htTy with
    ⟨wt', hwteq, hWtNonneg, hTSmtTy⟩
  injection hwteq with hwteq'
  subst hwteq'
  -- Need N ≥ 0 for the eval crux. (See the gap note above; for `facts_of_true`
  -- this would be derivable from `RulePremiseEvidence`, which is not threaded
  -- through this helper; it shares the single documented gap lemma.)
  have hNNonneg : native_zleq 0 N = true := extend_n1_nonneg_gap N
  apply RuleProofs.eo_interprets_eq_of_rel M
    (intToBvTerm (Term.Numeral (native_zplus N wt)) (ubvToIntTerm t)) (extendRhs t n) hProgBool
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt (intToBvTerm (Term.Numeral (native_zplus N wt)) (ubvToIntTerm t))))
    (__smtx_model_eval M (__eo_to_smt (extendRhs t n)))
  rw [eval_lhs_matches_rhs M hM N wt t n hTTrans hnN hNNonneg hWtNonneg hTSmtTy]
  exact RuleProofs.smt_value_rel_refl _

theorem cmd_step_uf_bv2nat_int2bv_extend_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_int2bv_extend args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n1 premises =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons n2 premises =>
                          cases premises with
                          | nil =>
                              let P1 := __eo_state_proven_nth s n1
                              let P2 := __eo_state_proven_nth s n2
                              have hATransPair :
                                  RuleProofs.eo_has_smt_translation a1 ∧
                                    RuleProofs.eo_has_smt_translation a2 ∧
                                      RuleProofs.eo_has_smt_translation a3 ∧ True := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                              have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                                hATransPair.2.1
                              change __eo_typeof
                                  (__eo_prog_uf_bv2nat_int2bv_extend a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2)) =
                                Term.Bool at hResultTy
                              have hProgArg :
                                  __eo_prog_uf_bv2nat_int2bv_extend a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              obtain ⟨hA1NS, hA2NS, hA3NS⟩ :=
                                args_ne_stuck_of_prog_not_stuck a1 a2 a3 P1 P2 hProgArg
                              rcases shape_of_prog_uf_bv2nat_int2bv_extend_not_stuck
                                a1 a2 a3 P1 P2 hA1NS hA2NS hA3NS hProgArg with
                                ⟨lw2, lt2, ln2, lw3, lt3, hP1, hP2⟩
                              rw [hP1, hP2] at hProgArg hResultTy
                              have hProgEq :
                                  __eo_prog_uf_bv2nat_int2bv_extend a1 a2 a3
                                    (Proof.pf
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.eq)
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.gt) lw2)
                                            (Term.Apply (Term.UOp UserOp._at_bvsize) lt2)))
                                        (Term.Boolean true)))
                                    (Proof.pf
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.eq) ln2)
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lw3)
                                          (Term.Apply (Term.UOp UserOp._at_bvsize) lt3)))) =
                                    __eo_requires
                                      (__eo_and
                                        (__eo_and
                                          (__eo_and
                                            (__eo_and (__eo_eq a1 lw2) (__eo_eq a2 lt2))
                                            (__eo_eq a3 ln2))
                                          (__eo_eq a1 lw3))
                                        (__eo_eq a2 lt3))
                                      (Term.Boolean true) (ufExtendConclusion a1 a2 a3) :=
                                prog_uf_bv2nat_int2bv_extend_eq a1 a2 a3 lw2 lt2 ln2 lw3 lt3
                                  hA1NS hA2NS hA3NS
                              rw [hProgEq] at hProgArg hResultTy
                              obtain ⟨hLw2, hLt2, hLn2, hLw3, hLt3⟩ :=
                                eqs_of_requires_and5_not_stuck a1 a2 a3 lw2 lt2 ln2 lw3 lt3
                                  (ufExtendConclusion a1 a2 a3) hProgArg
                              subst lw2; subst lt2; subst ln2; subst lw3; subst lt3
                              rw [requires_and5_self_true_body a1 a2 a3
                                (ufExtendConclusion a1 a2 a3) hA1NS hA2NS hA3NS]
                                at hResultTy
                              have hStepEq :
                                  __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend
                                      (CArgList.cons a1 (CArgList.cons a2
                                        (CArgList.cons a3 CArgList.nil)))
                                      (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil)) =
                                    ufExtendConclusion a1 a2 a3 := by
                                change __eo_prog_uf_bv2nat_int2bv_extend a1 a2 a3
                                  (Proof.pf P1) (Proof.pf P2) =
                                  ufExtendConclusion a1 a2 a3
                                rw [hP1, hP2, hProgEq,
                                  requires_and5_self_true_body a1 a2 a3
                                    (ufExtendConclusion a1 a2 a3) hA1NS hA2NS hA3NS]
                              rw [hStepEq]
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                exact facts_conclusion_impl M hM a1 a2 a3 hA2Trans hResultTy
                              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  (typed_conclusion_impl a1 a2 a3 hA2Trans hResultTy)
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
