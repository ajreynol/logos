import Cpc.SmtModel

/-!
# SMT free type-references vs. well-formedness

Infrastructure for the `dtMutual` lift↔translation correctness work. A well-formed SMT type
contains no *free* type-reference: every `TypeRef s` occurring in it is bound by an enclosing
`Datatype s …` (or by the ambient `refs`). This is the key fact that lets us show the SMT
`lift`/`substitute` is a no-op on the (closed) interiors of translated tuples — see
`Cpc.Proofs.Translation.EoTypeofCore` and the session notes on `eo_to_smt_datatype_lift`.
-/

open SmtEval
namespace Smtm

/- `hasFreeTy sub refs T` holds iff `T` contains a `TypeRef sub` not bound by `refs` or by an
enclosing datatype. Its ref-scoping mirrors `__smtx_type_wf_rec` exactly (Seq/Set/Map reset the
ref context to `nil`; `Datatype s` inserts `s`). -/
mutual
def hasFreeTy (sub : native_String) : RefList → SmtType → Bool
  | refs, (SmtType.Datatype s d) => hasFreeDt sub (native_reflist_insert refs s) d
  | _,    (SmtType.Seq x) => hasFreeTy sub native_reflist_nil x
  | _,    (SmtType.Set x) => hasFreeTy sub native_reflist_nil x
  | _,    (SmtType.Map x y) => native_or (hasFreeTy sub native_reflist_nil x) (hasFreeTy sub native_reflist_nil y)
  | _, _ => false
def hasFreeDt (sub : native_String) : RefList → SmtDatatype → Bool
  | refs, (SmtDatatype.sum c d) => native_or (hasFreeDtc sub refs c) (hasFreeDt sub refs d)
  | _,    SmtDatatype.null => false
def hasFreeDtc (sub : native_String) : RefList → SmtDatatypeCons → Bool
  | refs, (SmtDatatypeCons.cons (SmtType.TypeRef s) c) =>
      native_or (native_and (native_streq s sub) (native_not (native_reflist_contains refs sub)))
        (hasFreeDtc sub refs c)
  | refs, (SmtDatatypeCons.cons T c) => native_or (hasFreeTy sub refs T) (hasFreeDtc sub refs c)
  | _,    SmtDatatypeCons.unit => false
end

/- A well-formed SMT type/datatype/cons has no free type-reference (for any candidate name). -/
mutual
theorem hasFreeTy_eq_false_of_wf (sub : native_String) :
    (T : SmtType) → (refs : RefList) → __smtx_type_wf_rec T refs = true → hasFreeTy sub refs T = false
  | SmtType.Datatype s d, refs, h => by
      simp only [__smtx_type_wf_rec] at h
      have hd : __smtx_dt_wf_rec d (native_reflist_insert refs s) = true := by
        cases hc : native_reflist_contains refs s <;> simp [native_ite, hc] at h ⊢
        exact h
      simp only [hasFreeTy]
      exact hasFreeDt_eq_false_of_wf sub d (native_reflist_insert refs s) hd
  | SmtType.Seq x, refs, h => by
      simp only [__smtx_type_wf_rec, native_and, Bool.and_eq_true] at h
      simp only [hasFreeTy]
      exact hasFreeTy_eq_false_of_wf sub x native_reflist_nil h.2
  | SmtType.Set x, refs, h => by
      simp only [__smtx_type_wf_rec, native_and, Bool.and_eq_true] at h
      simp only [hasFreeTy]
      exact hasFreeTy_eq_false_of_wf sub x native_reflist_nil h.2
  | SmtType.Map x y, refs, h => by
      simp only [__smtx_type_wf_rec, native_and, Bool.and_eq_true] at h
      simp only [hasFreeTy, native_or, Bool.or_eq_false_iff]
      exact ⟨hasFreeTy_eq_false_of_wf sub x native_reflist_nil h.2.1,
        hasFreeTy_eq_false_of_wf sub y native_reflist_nil h.2.2.2⟩
  | SmtType.TypeRef s, refs, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.FunType x y, refs, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.DtcAppType x y, refs, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.None, refs, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.RegLan, refs, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.Bool, refs, h => by simp [hasFreeTy]
  | SmtType.Int, refs, h => by simp [hasFreeTy]
  | SmtType.Real, refs, h => by simp [hasFreeTy]
  | SmtType.BitVec n, refs, h => by simp [hasFreeTy]
  | SmtType.Char, refs, h => by simp [hasFreeTy]
  | SmtType.USort n, refs, h => by simp [hasFreeTy]

theorem hasFreeDt_eq_false_of_wf (sub : native_String) :
    (d : SmtDatatype) → (refs : RefList) → __smtx_dt_wf_rec d refs = true → hasFreeDt sub refs d = false
  | SmtDatatype.null, refs, h => by simp [__smtx_dt_wf_rec] at h
  | SmtDatatype.sum c SmtDatatype.null, refs, h => by
      simp only [__smtx_dt_wf_rec] at h
      have hC := hasFreeDtc_eq_false_of_wf sub c refs h
      rw [hasFreeDt, hC, hasFreeDt]; rfl
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), refs, h => by
      simp only [__smtx_dt_wf_rec, native_ite] at h
      have hc : __smtx_dt_cons_wf_rec c refs = true := by
        cases hcc : __smtx_dt_cons_wf_rec c refs <;> simp [hcc] at h ⊢
      have hd : __smtx_dt_wf_rec (SmtDatatype.sum c2 d2) refs = true := by
        rw [hc] at h; simpa using h
      have hC := hasFreeDtc_eq_false_of_wf sub c refs hc
      have hD := hasFreeDt_eq_false_of_wf sub (SmtDatatype.sum c2 d2) refs hd
      rw [hasFreeDt, hC, hD]; rfl

theorem hasFreeDtc_eq_false_of_wf (sub : native_String) :
    (c : SmtDatatypeCons) → (refs : RefList) → __smtx_dt_cons_wf_rec c refs = true → hasFreeDtc sub refs c = false
  | SmtDatatypeCons.unit, refs, h => by simp [hasFreeDtc]
  | SmtDatatypeCons.cons T c, refs, h => by
      cases T with
      | TypeRef s =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at h
          split at h
          · next hs =>
              have hc : __smtx_dt_cons_wf_rec c refs = true := h
              have hC := hasFreeDtc_eq_false_of_wf sub c refs hc
              have hFirst : native_and (native_streq s sub)
                  (native_not (native_reflist_contains refs sub)) = false := by
                by_cases hse : s = sub
                · subst hse; simp [native_and, native_not, native_streq, hs]
                · simp [native_and, native_streq, hse]
              rw [hasFreeDtc, hFirst, hC]; rfl
          · next => exact absurd h (by simp)
      | _ =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at h
          split at h
          · next hwfT =>
              have hc : __smtx_dt_cons_wf_rec c refs = true := h
              have hT := hasFreeTy_eq_false_of_wf sub _ refs hwfT
              have hC := hasFreeDtc_eq_false_of_wf sub c refs hc
              simp [hasFreeDtc, hT, hC, native_or]
          · next => exact absurd h (by simp)
end

private theorem contains_cons_irrel {sub s : native_String} {r1 r2 : RefList}
    (h : native_reflist_contains r1 sub = native_reflist_contains r2 sub) :
    native_reflist_contains (native_reflist_insert r1 s) sub
      = native_reflist_contains (native_reflist_insert r2 s) sub := by
  simp only [native_reflist_contains, native_reflist_insert, List.mem_cons] at h ⊢
  have hiff : (sub ∈ r1) ↔ (sub ∈ r2) := decide_eq_decide.mp h
  rw [decide_eq_decide]
  exact or_congr_right hiff

/- `hasFree…` depends on `refs` only through whether `sub` is a member of it. -/
mutual
theorem hasFreeTy_refs_irrel (sub : native_String) :
    (T : SmtType) → (r1 r2 : RefList) →
      native_reflist_contains r1 sub = native_reflist_contains r2 sub →
      hasFreeTy sub r1 T = hasFreeTy sub r2 T
  | SmtType.Datatype s d, r1, r2, h => by
      simp only [hasFreeTy]
      exact hasFreeDt_refs_irrel sub d _ _ (contains_cons_irrel h)
  | SmtType.Seq x, r1, r2, h => by simp only [hasFreeTy]
  | SmtType.Set x, r1, r2, h => by simp only [hasFreeTy]
  | SmtType.Map x y, r1, r2, h => by simp only [hasFreeTy]
  | SmtType.TypeRef s, _, _, _ => by simp only [hasFreeTy]
  | SmtType.FunType x y, _, _, _ => by simp only [hasFreeTy]
  | SmtType.DtcAppType x y, _, _, _ => by simp only [hasFreeTy]
  | SmtType.None, _, _, _ => by simp only [hasFreeTy]
  | SmtType.RegLan, _, _, _ => by simp only [hasFreeTy]
  | SmtType.Bool, _, _, _ => by simp only [hasFreeTy]
  | SmtType.Int, _, _, _ => by simp only [hasFreeTy]
  | SmtType.Real, _, _, _ => by simp only [hasFreeTy]
  | SmtType.BitVec n, _, _, _ => by simp only [hasFreeTy]
  | SmtType.Char, _, _, _ => by simp only [hasFreeTy]
  | SmtType.USort n, _, _, _ => by simp only [hasFreeTy]

theorem hasFreeDt_refs_irrel (sub : native_String) :
    (d : SmtDatatype) → (r1 r2 : RefList) →
      native_reflist_contains r1 sub = native_reflist_contains r2 sub →
      hasFreeDt sub r1 d = hasFreeDt sub r2 d
  | SmtDatatype.null, r1, r2, h => by simp only [hasFreeDt]
  | SmtDatatype.sum c d, r1, r2, h => by
      simp only [hasFreeDt]
      rw [hasFreeDtc_refs_irrel sub c r1 r2 h, hasFreeDt_refs_irrel sub d r1 r2 h]

theorem hasFreeDtc_refs_irrel (sub : native_String) :
    (c : SmtDatatypeCons) → (r1 r2 : RefList) →
      native_reflist_contains r1 sub = native_reflist_contains r2 sub →
      hasFreeDtc sub r1 c = hasFreeDtc sub r2 c
  | SmtDatatypeCons.unit, r1, r2, h => by simp only [hasFreeDtc]
  | SmtDatatypeCons.cons T c, r1, r2, h => by
      cases T with
      | TypeRef s =>
          simp only [hasFreeDtc]
          rw [h, hasFreeDtc_refs_irrel sub c r1 r2 h]
      | _ =>
          simp only [hasFreeDtc]
          rw [hasFreeTy_refs_irrel sub _ r1 r2 h, hasFreeDtc_refs_irrel sub c r1 r2 h]
end

/- The SMT lift `__smtx_*_lift s D` is a no-op on a structure `W` that is well-formed both at
`r0` (with `sub ∉ r0`) and at `rR` (with `sub ∈ rR`), when the target body `D` has a free
reference `sub` at scope `[s]`. A fold would place the target inside `W`; its free `sub` must be
bound somewhere, which `wf @ r0` (free-refs) turns into "`W` binds `sub`", which `wf @ rR`
(no-aliasing, `sub ∈ rR`) forbids. This is the tuple no-op: translated tuple bodies are wf at
`[]` (`wf_component`) and at the ambient `refs ∋ sub`. -/
mutual
theorem lift_noop_ty (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (T : SmtType) → (r0 rR : RefList) →
      native_reflist_contains r0 sub = false →
      native_reflist_contains rR sub = true →
      __smtx_type_wf_rec T r0 = true →
      __smtx_type_wf_rec T rR = true →
      __smtx_type_lift s D T = T
  | SmtType.Datatype s' X, r0, rR, h0, hR, hwf0, hwfR => by
      have hns0 : native_reflist_contains r0 s' = false := by
        cases hc : native_reflist_contains r0 s' <;> simp [__smtx_type_wf_rec, native_ite, hc] at hwf0 ⊢
      have hX0 : __smtx_dt_wf_rec X (native_reflist_insert r0 s') = true := by
        simp [__smtx_type_wf_rec, native_ite, hns0] at hwf0; exact hwf0
      have hnsR : native_reflist_contains rR s' = false := by
        cases hc : native_reflist_contains rR s' <;> simp [__smtx_type_wf_rec, native_ite, hc] at hwfR ⊢
      have hXR : __smtx_dt_wf_rec X (native_reflist_insert rR s') = true := by
        simp [__smtx_type_wf_rec, native_ite, hnsR] at hwfR; exact hwfR
      have hs'sub : s' ≠ sub := by
        intro he; subst he; rw [hR] at hnsR; exact absurd hnsR (by simp)
      have hsub0 : sub ∉ r0 := by simpa [native_reflist_contains] using h0
      have hsubR : sub ∈ rR := by simpa [native_reflist_contains] using hR
      have hsubs' : sub ≠ s' := Ne.symm hs'sub
      have h0' : native_reflist_contains (native_reflist_insert r0 s') sub = false := by
        simp [native_reflist_contains, native_reflist_insert, List.mem_cons, hsubs', hsub0]
      have hR' : native_reflist_contains (native_reflist_insert rR s') sub = true := by
        simp [native_reflist_contains, native_reflist_insert, List.mem_cons, hsubR]
      simp only [__smtx_type_lift]
      have hnofold : ¬ (native_Teq (SmtType.Datatype s D) (SmtType.Datatype s' X) = true) := by
        intro hTeq
        have heq : SmtType.Datatype s D = SmtType.Datatype s' X :=
          of_decide_eq_true (by simpa [native_Teq] using hTeq)
        injection heq with hs hXeq
        subst hs; subst hXeq
        have hDfree_false : hasFreeDt sub (native_reflist_insert r0 s) D = false :=
          hasFreeDt_eq_false_of_wf sub D (native_reflist_insert r0 s) hX0
        have hconteq : native_reflist_contains (native_reflist_insert r0 s) sub
            = native_reflist_contains (native_reflist_insert native_reflist_nil s) sub := by
          have hsubs : sub ≠ s := hsne
          simp [native_reflist_contains, native_reflist_insert, List.mem_cons,
            hsubs, hsub0, native_reflist_nil]
        have hDfree_true : hasFreeDt sub (native_reflist_insert r0 s) D = true := by
          rw [hasFreeDt_refs_irrel sub D (native_reflist_insert r0 s)
            (native_reflist_insert native_reflist_nil s) hconteq]
          exact hFree
        rw [hDfree_false] at hDfree_true; exact absurd hDfree_true (by simp)
      rw [native_ite, if_neg hnofold]
      congr 1
      exact lift_noop_dt s sub D hsne hFree X (native_reflist_insert r0 s')
        (native_reflist_insert rR s') h0' hR' hX0 hXR
  | SmtType.Seq x, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.Set x, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.Map x y, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.TypeRef s', _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.FunType x y, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.DtcAppType x y, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.None, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.RegLan, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.Bool, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.Int, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.Real, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.BitVec n, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.Char, _, _, _, _, _, _ => by simp only [__smtx_type_lift]
  | SmtType.USort n, _, _, _, _, _, _ => by simp only [__smtx_type_lift]

theorem lift_noop_dt (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (W : SmtDatatype) → (r0 rR : RefList) →
      native_reflist_contains r0 sub = false →
      native_reflist_contains rR sub = true →
      __smtx_dt_wf_rec W r0 = true →
      __smtx_dt_wf_rec W rR = true →
      __smtx_dt_lift s D W = W
  | SmtDatatype.null, _, _, _, _, hwf0, _ => by simp [__smtx_dt_wf_rec] at hwf0
  | SmtDatatype.sum c SmtDatatype.null, r0, rR, h0, hR, hwf0, hwfR => by
      simp only [__smtx_dt_wf_rec] at hwf0 hwfR
      show SmtDatatype.sum (__smtx_dtc_lift s D c) SmtDatatype.null = SmtDatatype.sum c SmtDatatype.null
      rw [lift_noop_dtc s sub D hsne hFree c r0 rR h0 hR hwf0 hwfR]
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), r0, rR, h0, hR, hwf0, hwfR => by
      simp only [__smtx_dt_wf_rec, native_ite] at hwf0 hwfR
      have hc0 : __smtx_dt_cons_wf_rec c r0 = true := by
        cases hcc : __smtx_dt_cons_wf_rec c r0 <;> simp [hcc] at hwf0 ⊢
      have hd0 : __smtx_dt_wf_rec (SmtDatatype.sum c2 d2) r0 = true := by rw [hc0] at hwf0; simpa using hwf0
      have hcR : __smtx_dt_cons_wf_rec c rR = true := by
        cases hcc : __smtx_dt_cons_wf_rec c rR <;> simp [hcc] at hwfR ⊢
      have hdR : __smtx_dt_wf_rec (SmtDatatype.sum c2 d2) rR = true := by rw [hcR] at hwfR; simpa using hwfR
      show SmtDatatype.sum (__smtx_dtc_lift s D c) (__smtx_dt_lift s D (SmtDatatype.sum c2 d2))
         = SmtDatatype.sum c (SmtDatatype.sum c2 d2)
      rw [lift_noop_dtc s sub D hsne hFree c r0 rR h0 hR hc0 hcR,
        lift_noop_dt s sub D hsne hFree (SmtDatatype.sum c2 d2) r0 rR h0 hR hd0 hdR]

theorem lift_noop_dtc (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (c : SmtDatatypeCons) → (r0 rR : RefList) →
      native_reflist_contains r0 sub = false →
      native_reflist_contains rR sub = true →
      __smtx_dt_cons_wf_rec c r0 = true →
      __smtx_dt_cons_wf_rec c rR = true →
      __smtx_dtc_lift s D c = c
  | SmtDatatypeCons.unit, _, _, _, _, _, _ => by simp [__smtx_dtc_lift]
  | SmtDatatypeCons.cons T c, r0, rR, h0, hR, hwf0, hwfR => by
      cases T with
      | TypeRef s' =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf0 hwfR
          have hc0 : __smtx_dt_cons_wf_rec c r0 = true := by
            split at hwf0
            · exact hwf0
            · exact absurd hwf0 (by simp)
          have hcR : __smtx_dt_cons_wf_rec c rR = true := by
            split at hwfR
            · exact hwfR
            · exact absurd hwfR (by simp)
          simp only [__smtx_dtc_lift, __smtx_type_lift]
          rw [lift_noop_dtc s sub D hsne hFree c r0 rR h0 hR hc0 hcR]
      | _ =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf0 hwfR
          split at hwf0
          · next hT0 =>
              split at hwfR
              · next hTR =>
                  simp only [__smtx_dtc_lift]
                  rw [lift_noop_ty s sub D hsne hFree _ r0 rR h0 hR hT0 hTR,
                    lift_noop_dtc s sub D hsne hFree c r0 rR h0 hR hwf0 hwfR]
              · next => exact absurd hwfR (by simp)
          · next => exact absurd hwf0 (by simp)
end

end Smtm
