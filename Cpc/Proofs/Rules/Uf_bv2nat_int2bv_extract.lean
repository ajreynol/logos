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

private abbrev extractTerm (wm t : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract wm (Term.Numeral 0)) t

private abbrev ufConclusion (w t wm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (intToBvTerm w (ubvToIntTerm t)))
    (extractTerm wm t)

private abbrev ufType (w t wm : Term) : Term :=
  __eo_typeof_eq
    (__eo_typeof_int_to_bv (__eo_typeof w) w
      (__eo_typeof__at_bvsize (__eo_typeof t)))
    (__eo_typeof_extract (__eo_typeof wm) wm
      (__eo_typeof (Term.Numeral 0)) (Term.Numeral 0) (__eo_typeof t))

private theorem typeof_ufConclusion_eq (w t wm : Term) :
    __eo_typeof (ufConclusion w t wm) = ufType w t wm := by
  rfl

/-- Stable rewrite for typing SMT extraction terms. -/
private theorem smtx_typeof_extract_term_eq
    (hi lo x : SmtTerm) :
    __smtx_typeof (SmtTerm.extract hi lo x) =
      __smtx_typeof_extract hi lo (__smtx_typeof x) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-! ## requires/and guard handling (4-way conjunction) -/

private theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem eo_eq_stuck_or_bool (a b : Term) :
    __eo_eq a b = Term.Stuck ∨
      ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
  by_cases ha : a = Term.Stuck
  · subst a
    exact Or.inl (by simp [__eo_eq])
  · by_cases hb : b = Term.Stuck
    · subst b
      exact Or.inl (by simp [__eo_eq])
    · exact Or.inr ⟨native_teq b a, by simp [__eo_eq]⟩

private theorem eo_and_true_split (p q : Term)
    (h : __eo_and p q = Term.Boolean true) :
    p = Term.Boolean true ∧ q = Term.Boolean true := by
  cases p with
  | Boolean b1 =>
      cases q with
      | Boolean b2 =>
          cases b1 <;> cases b2 <;> simp [__eo_and, native_and] at h ⊢
      | _ => simp [__eo_and] at h
  | _ => simp [__eo_and] at h

/-- A `requires (and (and (and (eq w lw)(eq t lt))(eq wm lwm))(eq w lw3)) true B`
    that is non-stuck forces all four equalities to align. -/
private theorem eqs4_of_requires_and_eq_true_not_stuck
    (w lw t lt wm lwm w3 lw3 B : Term) :
    __eo_requires
      (__eo_and
        (__eo_and (__eo_and (__eo_eq w lw) (__eo_eq t lt)) (__eo_eq wm lwm))
        (__eo_eq w3 lw3))
      (Term.Boolean true) B ≠ Term.Stuck ->
    lw = w ∧ lt = t ∧ lwm = wm ∧ lw3 = w3 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hProg'
  have hAnd :
      __eo_and
        (__eo_and (__eo_and (__eo_eq w lw) (__eo_eq t lt)) (__eo_eq wm lwm))
        (__eo_eq w3 lw3) = Term.Boolean true := hProg'.1
  obtain ⟨hAnd3, hEq4⟩ := eo_and_true_split _ _ hAnd
  obtain ⟨hAnd2, hEq3⟩ := eo_and_true_split _ _ hAnd3
  obtain ⟨hEq1, hEq2⟩ := eo_and_true_split _ _ hAnd2
  exact ⟨eq_of_eo_eq_true w lw hEq1, eq_of_eo_eq_true t lt hEq2,
    eq_of_eo_eq_true wm lwm hEq3, eq_of_eo_eq_true w3 lw3 hEq4⟩

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem requires_and4_eq_self_true_body
    (w t wm body : Term)
    (hWNotStuck : w ≠ Term.Stuck)
    (hTNotStuck : t ≠ Term.Stuck)
    (hWmNotStuck : wm ≠ Term.Stuck) :
    __eo_requires
      (__eo_and
        (__eo_and (__eo_and (__eo_eq w w) (__eo_eq t t)) (__eo_eq wm wm))
        (__eo_eq w w))
      (Term.Boolean true) body = body := by
  simp [__eo_requires, __eo_and, eo_eq_self_true_of_ne_stuck w hWNotStuck,
    eo_eq_self_true_of_ne_stuck t hTNotStuck,
    eo_eq_self_true_of_ne_stuck wm hWmNotStuck, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and]

/-! ## program reduction -/

/-- When the args are non-stuck and the two premises have the expected shape, the
    program reduces to the requires-guarded conclusion. -/
private theorem prog_uf_bv2nat_int2bv_extract_eq
    (w1 t1 wm1 lw1 lt1 lwm1 lw1' : Term)
    (hW : w1 ≠ Term.Stuck) (hT : t1 ≠ Term.Stuck) (hWm : wm1 ≠ Term.Stuck) :
    __eo_prog_uf_bv2nat_int2bv_extract w1 t1 wm1
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.lt) lw1)
              (Term.Apply (Term.UOp UserOp._at_bvsize) lt1)))
          (Term.Boolean true)))
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) lwm1)
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lw1') (Term.Numeral 1)))) =
      __eo_requires
        (__eo_and
          (__eo_and (__eo_and (__eo_eq w1 lw1) (__eo_eq t1 lt1)) (__eo_eq wm1 lwm1))
          (__eo_eq w1 lw1'))
        (Term.Boolean true) (ufConclusion w1 t1 wm1) := by
  cases w1 <;> (try (exact absurd rfl hW)) <;>
  cases t1 <;> (try (exact absurd rfl hT)) <;>
  cases wm1 <;> (try (exact absurd rfl hWm)) <;>
    simp [__eo_prog_uf_bv2nat_int2bv_extract, ufConclusion,
      intToBvTerm, ubvToIntTerm, extractTerm]

private theorem args_ne_stuck_of_prog_not_stuck
    (w1 t1 wm1 p1 p2 : Term)
    (h : __eo_prog_uf_bv2nat_int2bv_extract w1 t1 wm1 (Proof.pf p1) (Proof.pf p2) ≠
      Term.Stuck) :
    w1 ≠ Term.Stuck ∧ t1 ≠ Term.Stuck ∧ wm1 ≠ Term.Stuck := by
  refine ⟨?_, ?_, ?_⟩
  · intro hW; subst w1
    simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
  · intro hT; subst t1
    cases w1 <;> simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
  · intro hWm; subst wm1
    cases w1 <;> cases t1 <;> simp [__eo_prog_uf_bv2nat_int2bv_extract] at h

/-- Shape of the two premises forced by a non-stuck program. -/
private theorem shape_of_prog_uf_bv2nat_int2bv_extract_not_stuck
    (w1 t1 wm1 p1 p2 : Term)
    (hW : w1 ≠ Term.Stuck) (hT : t1 ≠ Term.Stuck) (hWm : wm1 ≠ Term.Stuck)
    (h : __eo_prog_uf_bv2nat_int2bv_extract w1 t1 wm1 (Proof.pf p1) (Proof.pf p2) ≠
      Term.Stuck) :
    ∃ lw1 lt1 lwm1 lw1' : Term,
      p1 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.lt) lw1)
              (Term.Apply (Term.UOp UserOp._at_bvsize) lt1)))
          (Term.Boolean true) ∧
      p2 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) lwm1)
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lw1') (Term.Numeral 1)) := by
  cases p1 with
     | Apply p1EqR p1R =>
         cases p1EqR with
         | Apply p1EqL ltTerm =>
             cases p1EqL with
             | UOp op1 =>
                 cases op1 <;> try (simp [__eo_prog_uf_bv2nat_int2bv_extract] at h)
                 case eq =>
                   cases p1R with
                   | Boolean b1 =>
                       cases b1 <;>
                         try (simp [__eo_prog_uf_bv2nat_int2bv_extract] at h)
                       case _ =>
                         cases ltTerm with
                         | Apply ltL bvsizeArg =>
                             cases ltL with
                             | Apply ltOp lw1 =>
                                 cases ltOp with
                                 | UOp lop =>
                                     cases lop <;>
                                       try (simp [__eo_prog_uf_bv2nat_int2bv_extract] at h)
                                     case lt =>
                                       cases bvsizeArg with
                                       | Apply bvOp lt1 =>
                                           cases bvOp with
                                           | UOp bop =>
                                               cases bop <;>
                                                 try (simp [__eo_prog_uf_bv2nat_int2bv_extract] at h)
                                               case _at_bvsize =>
                                                 cases p2 with
                                                 | Apply p2EqR negTerm =>
                                                     cases p2EqR with
                                                     | Apply p2EqL lwm1 =>
                                                         cases p2EqL with
                                                         | UOp op2 =>
                                                             cases op2 <;>
                                                               try (simp [__eo_prog_uf_bv2nat_int2bv_extract] at h)
                                                             case eq =>
                                                               cases negTerm with
                                                               | Apply negR oneTerm =>
                                                                   cases negR with
                                                                   | Apply negOp lw1' =>
                                                                       cases negOp with
                                                                       | UOp nop =>
                                                                           cases nop <;>
                                                                             try (simp [__eo_prog_uf_bv2nat_int2bv_extract] at h)
                                                                           case neg =>
                                                                             cases oneTerm with
                                                                             | Numeral k =>
                                                                                 by_cases hk : k = (1 : native_Int)
                                                                                 · subst k
                                                                                   exact ⟨lw1, lt1, lwm1, lw1', rfl, rfl⟩
                                                                                 · simp [__eo_prog_uf_bv2nat_int2bv_extract, hk] at h
                                                                             | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                                                                       | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                                                                   | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                                                               | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                                                         | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                                                     | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                                                 | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                                           | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                                       | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                                 | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                             | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                         | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
                   | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
             | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
         | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
     | _ => simp [__eo_prog_uf_bv2nat_int2bv_extract] at h

/-! ## typing inversion -/

private theorem typeof_int_to_bv_stuck_of_arg_stuck (A w : Term) :
    __eo_typeof_int_to_bv A w Term.Stuck = Term.Stuck := by
  unfold __eo_typeof_int_to_bv
  split <;> simp_all

private theorem typeof_int_to_bv_stuck_of_width_ty_ne_int (A w B : Term)
    (hA : A ≠ Term.UOp UserOp.Int) :
    __eo_typeof_int_to_bv A w B = Term.Stuck := by
  unfold __eo_typeof_int_to_bv
  split <;> simp_all

private theorem int_to_bv_type_bitvec_inv (A w m : Term)
    (h : __eo_typeof_int_to_bv A w (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    A = Term.UOp UserOp.Int ∧
      ∃ n, w = Term.Numeral n ∧ native_zlt (-1 : native_Int) n = true ∧
        m = Term.Numeral n := by
  by_cases hA : A = Term.UOp UserOp.Int
  · subst A
    refine ⟨rfl, ?_⟩
    cases hw : w <;> rw [hw] at h <;>
      first
      | (rename_i n
         have hRed :
             __eo_typeof_int_to_bv (Term.UOp UserOp.Int) (Term.Numeral n)
                 (Term.UOp UserOp.Int) =
               native_ite (native_zlt (-1 : native_Int) n)
                 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n)) Term.Stuck := by
           simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
             native_teq, native_not, SmtEval.native_not]
         rw [hRed] at h
         cases hPos : native_zlt (-1 : native_Int) n <;>
           simp [native_ite, hPos] at h
         exact ⟨n, rfl, hPos, h.symm⟩)
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
    B = A ∧ A ≠ Term.Stuck := by
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
      exact ⟨eq_of_eo_eq_true A B hEqTrue, hAStuck⟩

/-- Extract typing yields `Stuck` unless the operand type is a bit-vector. -/
private theorem typeof_extract_stuck_of_arg_stuck (A wm B lo : Term) :
    __eo_typeof_extract A wm B lo Term.Stuck = Term.Stuck := by
  unfold __eo_typeof_extract
  split <;> simp_all

/-- Inversion of the extract typing on a non-stuck (bit-vector) operand:
    a `BitVec` result forces both index types to be `Int`, the indices to be
    numerals (lo here is `0`), and the resulting width term to be `wm - lo + 1`
    with the operand width strictly greater than the high index. -/
private theorem typeof_extract_bitvec_inv
    (A wm lo nn m : Term)
    (h : __eo_typeof_extract A wm (__eo_typeof (Term.Numeral 0)) (Term.Numeral 0)
        (Term.Apply (Term.UOp UserOp.BitVec) nn) =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    A = Term.UOp UserOp.Int ∧
      ∃ wmn nnn, wm = Term.Numeral wmn ∧ nn = Term.Numeral nnn ∧
        native_zlt wmn nnn = true ∧
        m = Term.Numeral (native_zplus (native_zplus wmn (native_zneg 0)) 1) := by
  -- `typeof (Numeral 0) = Int`.
  have hZeroTy : __eo_typeof (Term.Numeral 0) = Term.UOp UserOp.Int := by
    rfl
  rw [hZeroTy] at h
  -- The operand-type bit-vector forces `A = Int` and `wm`,`nn` numerals.
  cases hA : A <;> rw [hA] at h <;>
    (try (exfalso; simp [__eo_typeof_extract] at h)) <;>
    rename_i op
  -- Now `A = UOp op`; we need `op = Int`.
  cases op <;>
    (try (exfalso; simp [__eo_typeof_extract] at h)) <;>
    (-- `A = UOp Int`.
     refine ⟨rfl, ?_⟩
     cases hwm : wm <;> rw [hwm] at h <;>
       (try (exfalso; simp [__eo_typeof_extract] at h)) <;>
       rename_i wmn
     cases hnn : nn <;> rw [hnn] at h <;>
       (try (exfalso; simp [__eo_typeof_extract] at h)) <;>
       rename_i nnn
     -- Now everything is numeral; reduce the typeof.
     have hRed :
         __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral wmn)
             (Term.UOp UserOp.Int) (Term.Numeral 0)
             (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral nnn)) =
           native_ite (native_zlt nnn wmn) Term.Stuck
             (Term.Apply (Term.UOp UserOp.BitVec)
               (Term.Numeral (native_zplus (native_zplus wmn (native_zneg 0)) 1))) := by
       simp [__eo_typeof_extract, __eo_requires, __eo_gt, __eo_add, __eo_neg,
         native_ite, native_teq, native_not, SmtEval.native_not, native_zplus,
         native_zneg]
     rw [hRed] at h
     cases hLt : native_zlt nnn wmn <;> simp [native_ite, hLt] at h
     -- `native_zlt nnn wmn = false`, so `wmn <= nnn`; but extract needs `nn > h`
     -- i.e. `nnn > wmn`.  We get the strict version: the result width term gives
     -- `m`, and the guard `gt nn wm` requires `wmn < nnn`.
     refine ⟨wmn, nnn, rfl, rfl, ?_, h.symm⟩
     -- From `native_zlt nnn wmn = false` we only get `wmn <= nnn`.  But the
     -- requires-guard `__eo_gt nn h` collapsing to a non-stuck result needs the
     -- strict inequality; re-derive it directly.
     have hStrict : native_zlt wmn nnn = true := by
       by_contra hc
       have hcF : native_zlt wmn nnn = false := by
         cases hv : native_zlt wmn nnn with
         | false => rfl
         | true => exact absurd hv hc
       -- if not strict, the requires guard `gt nn wm` is stuck.
       have hRed2 :
           __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral wmn)
               (Term.UOp UserOp.Int) (Term.Numeral 0)
               (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral nnn)) =
             Term.Stuck := by
         simp [__eo_typeof_extract, __eo_requires, __eo_gt, __eo_add, __eo_neg,
           native_ite, native_teq, native_not, SmtEval.native_not, hcF]
       rw [hRed2] at h
       cases h
     exact hStrict)

/-- A non-stuck `int_to_bv` type forces it to be a `BitVec` term. -/
private theorem int_to_bv_type_ne_stuck_bitvec (A w B : Term)
    (h : __eo_typeof_int_to_bv A w B ≠ Term.Stuck) :
    ∃ m, __eo_typeof_int_to_bv A w B = Term.Apply (Term.UOp UserOp.BitVec) m := by
  unfold __eo_typeof_int_to_bv at h ⊢
  split at h
  · exact absurd rfl h
  · rename_i w' heq
    -- the `requires (gt w' (-1)) true (BitVec w')` branch
    by_cases hPos : native_zlt (-1 : native_Int) w' = true
    · refine ⟨w', ?_⟩
      simp [__eo_requires, __eo_gt, native_ite, native_teq, native_not,
        SmtEval.native_not, hPos]
    · exfalso
      have hF : native_zlt (-1 : native_Int) w' = false := by
        cases hv : native_zlt (-1 : native_Int) w' with
        | false => rfl
        | true => exact absurd hv hPos
      simp [__eo_requires, __eo_gt, native_ite, native_teq, native_not,
        SmtEval.native_not, hF] at h
  · exact absurd rfl h

/-! ## from result-type Bool, derive the argument shapes -/

private theorem typeof_args_of_conclusion_bool (w t wm : Term) :
    __eo_typeof (ufConclusion w t wm) = Term.Bool ->
    ∃ wn wmn nn,
      w = Term.Numeral wn ∧ wm = Term.Numeral wmn ∧
      native_zleq 0 wn = true ∧
      __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral nn) ∧
      native_zlt wmn nn = true ∧
      wn = native_zplus wmn 1 := by
  intro hTy
  rw [typeof_ufConclusion_eq] at hTy
  simp only [ufType] at hTy
  -- The two operand types of the top `eq` agree, and the LHS (int_to_bv) type
  -- is non-stuck.
  obtain ⟨hEqTy, hLhsNe⟩ := typeof_eq_bool_inv _ _ hTy
  -- `hEqTy : extract-type = int_to_bv-type`; `hLhsNe : int_to_bv-type ≠ Stuck`.
  -- Since int_to_bv-type is non-stuck, `typeof t` is a `BitVec`.
  obtain ⟨mLhs, hLhsBv⟩ := int_to_bv_type_ne_stuck_bitvec _ _ _ hLhsNe
  -- Invert the int_to_bv type: width type Int, `w = Numeral wn`, arg type Int.
  -- First, the arg type `__eo_typeof__at_bvsize (typeof t)` must be `Int`.
  have hBvsizeInt :
      __eo_typeof__at_bvsize (__eo_typeof t) = Term.UOp UserOp.Int := by
    by_contra hc
    -- otherwise the arg type is `Stuck` and int_to_bv is `Stuck`.
    by_cases hBv : ∃ m, __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) m
    · rcases hBv with ⟨m, hTTy⟩
      rw [hTTy] at hc
      exact hc rfl
    · have hStuck : __eo_typeof__at_bvsize (__eo_typeof t) = Term.Stuck :=
        bvsize_stuck_of_not_bitvec (__eo_typeof t)
          (by intro m hm; exact hBv ⟨m, hm⟩)
      rw [hStuck, typeof_int_to_bv_stuck_of_arg_stuck] at hLhsNe
      exact hLhsNe rfl
  -- `typeof t` is `BitVec (Numeral nn)`.
  obtain ⟨nn, hTTy⟩ : ∃ nn, __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral nn) := by
    cases hT : __eo_typeof t with
    | Apply f m =>
        cases f with
        | UOp op =>
            cases op <;> rw [hT] at hBvsizeInt <;>
              first
              | (cases m with
                 | Numeral nn => exact ⟨nn, rfl⟩
                 | _ => simp [__eo_typeof__at_bvsize] at hBvsizeInt)
              | (simp [__eo_typeof__at_bvsize] at hBvsizeInt)
        | _ => rw [hT] at hBvsizeInt; simp [__eo_typeof__at_bvsize] at hBvsizeInt
    | _ => rw [hT] at hBvsizeInt; simp [__eo_typeof__at_bvsize] at hBvsizeInt
  rw [hBvsizeInt] at hLhsBv
  -- Invert int_to_bv to learn `w = Numeral wn`, `wn > -1`, and width term.
  rcases int_to_bv_type_bitvec_inv (__eo_typeof w) w mLhs hLhsBv with
    ⟨_hWTyInt, wn, hwn, hwPos, hmLhs⟩
  subst w
  subst mLhs
  -- Now transport the equality of types to invert the extract side.
  rw [hLhsBv, hTTy] at hEqTy
  -- `hEqTy : extract-type = BitVec (Numeral wn)`.
  rcases typeof_extract_bitvec_inv (__eo_typeof wm) wm (Term.Numeral 0)
      (Term.Numeral nn) (Term.Numeral wn) hEqTy with
    ⟨_hWmTyInt, wmn, nnn, hwmEq, hnnEq, hLtStrict, hmExtract⟩
  -- `nnn = nn` from injecting `Term.Numeral nnn = Term.Numeral nn`.
  injection hnnEq with hnnn
  subst hnnn
  -- The width term coincidence gives `wn = wmn + 1`.
  injection hmExtract with hmwidth
  -- `wn = wmn + (-0) + 1 = wmn + 1`.
  have hWnEq : wn = native_zplus wmn 1 := by
    have := hmwidth.symm
    simp [native_zplus, native_zneg] at this ⊢
    omega
  refine ⟨wn, wmn, nn, rfl, hwmEq, ?_, hTTy, hLtStrict, hWnEq⟩
  -- nonnegativity of `wn` from `wn > -1`.
  have hLt' : (-1 : native_Int) < wn := by
    simpa [native_zlt, SmtEval.native_zlt] using hwPos
  have hNonneg : (0 : native_Int) <= wn := by
    have hStep : (-1 : native_Int) + 1 <= wn := (Int.add_one_le_iff).2 hLt'
    simpa using hStep
  simpa [native_zleq, SmtEval.native_zleq] using hNonneg

theorem cmd_step_uf_bv2nat_int2bv_extract_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_int2bv_extract args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extract args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extract args premises) :=
by
  sorry
