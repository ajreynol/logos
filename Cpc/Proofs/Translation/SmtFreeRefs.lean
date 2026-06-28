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

/- The SMT substitute `__smtx_*_substitute sub X` is a no-op on a structure `W` well-formed both at
`r0` (sub ∉ r0) and `rR` (sub ∈ rR): such a `W` has no `TypeRef sub` occurrence (a free one would be
caught by `wf @ r0`; a bound one needs a `Datatype sub` binder, forbidden by `wf @ rR`'s no-aliasing). -/
mutual
theorem subst_noop_ty (sub : native_String) :
    (T : SmtType) → (X : SmtDatatype) → (r0 rR : RefList) →
      native_reflist_contains r0 sub = false →
      native_reflist_contains rR sub = true →
      __smtx_type_wf_rec T r0 = true →
      __smtx_type_wf_rec T rR = true →
      __smtx_type_substitute sub X T = T
  | SmtType.Datatype s' Y, X, r0, rR, h0, hR, hwf0, hwfR => by
      have hns0 : native_reflist_contains r0 s' = false := by
        cases hc : native_reflist_contains r0 s' <;> simp [__smtx_type_wf_rec, native_ite, hc] at hwf0 ⊢
      have hY0 : __smtx_dt_wf_rec Y (native_reflist_insert r0 s') = true := by
        simp [__smtx_type_wf_rec, native_ite, hns0] at hwf0; exact hwf0
      have hnsR : native_reflist_contains rR s' = false := by
        cases hc : native_reflist_contains rR s' <;> simp [__smtx_type_wf_rec, native_ite, hc] at hwfR ⊢
      have hYR : __smtx_dt_wf_rec Y (native_reflist_insert rR s') = true := by
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
      have hstreq : native_streq sub s' = false := by simp [native_streq, fun h => hsubs' h]
      simp only [__smtx_type_substitute, native_ite, hstreq, if_false]
      congr 1
      exact subst_noop_dt sub Y (__smtx_dt_lift s' Y X) (native_reflist_insert r0 s')
        (native_reflist_insert rR s') h0' hR' hY0 hYR
  | SmtType.TypeRef s', X, r0, rR, h0, hR, hwf0, hwfR => by
      simp [__smtx_type_wf_rec] at hwf0
  | SmtType.Seq x, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.Set x, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.Map x y, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.FunType x y, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.DtcAppType x y, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.None, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.RegLan, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.Bool, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.Int, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.Real, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.BitVec n, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.Char, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]
  | SmtType.USort n, _, _, _, _, _, _, _ => by simp only [__smtx_type_substitute]

theorem subst_noop_dt (sub : native_String) :
    (W : SmtDatatype) → (X : SmtDatatype) → (r0 rR : RefList) →
      native_reflist_contains r0 sub = false →
      native_reflist_contains rR sub = true →
      __smtx_dt_wf_rec W r0 = true →
      __smtx_dt_wf_rec W rR = true →
      __smtx_dt_substitute sub X W = W
  | SmtDatatype.null, _, _, _, _, _, hwf0, _ => by simp [__smtx_dt_wf_rec] at hwf0
  | SmtDatatype.sum c SmtDatatype.null, X, r0, rR, h0, hR, hwf0, hwfR => by
      simp only [__smtx_dt_wf_rec] at hwf0 hwfR
      show SmtDatatype.sum (__smtx_dtc_substitute sub X c) SmtDatatype.null = SmtDatatype.sum c SmtDatatype.null
      rw [subst_noop_dtc sub c X r0 rR h0 hR hwf0 hwfR]
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), X, r0, rR, h0, hR, hwf0, hwfR => by
      simp only [__smtx_dt_wf_rec, native_ite] at hwf0 hwfR
      have hc0 : __smtx_dt_cons_wf_rec c r0 = true := by
        cases hcc : __smtx_dt_cons_wf_rec c r0 <;> simp [hcc] at hwf0 ⊢
      have hd0 : __smtx_dt_wf_rec (SmtDatatype.sum c2 d2) r0 = true := by rw [hc0] at hwf0; simpa using hwf0
      have hcR : __smtx_dt_cons_wf_rec c rR = true := by
        cases hcc : __smtx_dt_cons_wf_rec c rR <;> simp [hcc] at hwfR ⊢
      have hdR : __smtx_dt_wf_rec (SmtDatatype.sum c2 d2) rR = true := by rw [hcR] at hwfR; simpa using hwfR
      show SmtDatatype.sum (__smtx_dtc_substitute sub X c) (__smtx_dt_substitute sub X (SmtDatatype.sum c2 d2))
         = SmtDatatype.sum c (SmtDatatype.sum c2 d2)
      rw [subst_noop_dtc sub c X r0 rR h0 hR hc0 hcR,
        subst_noop_dt sub (SmtDatatype.sum c2 d2) X r0 rR h0 hR hd0 hdR]

theorem subst_noop_dtc (sub : native_String) :
    (c : SmtDatatypeCons) → (X : SmtDatatype) → (r0 rR : RefList) →
      native_reflist_contains r0 sub = false →
      native_reflist_contains rR sub = true →
      __smtx_dt_cons_wf_rec c r0 = true →
      __smtx_dt_cons_wf_rec c rR = true →
      __smtx_dtc_substitute sub X c = c
  | SmtDatatypeCons.unit, _, _, _, _, _, _, _ => by simp [__smtx_dtc_substitute]
  | SmtDatatypeCons.cons T c, X, r0, rR, h0, hR, hwf0, hwfR => by
      cases T with
      | TypeRef s' =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf0 hwfR
          have hs0 : native_reflist_contains r0 s' = true := by
            by_cases hc : native_reflist_contains r0 s' = true
            · exact hc
            · rw [if_neg hc] at hwf0; exact absurd hwf0 (by simp)
          have hc0 : __smtx_dt_cons_wf_rec c r0 = true := by rw [if_pos hs0] at hwf0; exact hwf0
          have hcR : __smtx_dt_cons_wf_rec c rR = true := by
            by_cases hsR : native_reflist_contains rR s' = true
            · rw [if_pos hsR] at hwfR; exact hwfR
            · rw [if_neg hsR] at hwfR; exact absurd hwfR (by simp)
          have hs'sub : s' ≠ sub := by
            intro he; subst he; rw [h0] at hs0; exact absurd hs0 (by simp)
          have hsubs' : sub ≠ s' := Ne.symm hs'sub
          have hstreq : native_streq sub s' = false := by simp [native_streq, hsubs']
          have hsubst : __smtx_type_substitute sub X (SmtType.TypeRef s') = SmtType.TypeRef s' := by
            simp [__smtx_type_substitute, native_ite, hstreq]
          show SmtDatatypeCons.cons (__smtx_type_substitute sub X (SmtType.TypeRef s'))
                (__smtx_dtc_substitute sub X c)
             = SmtDatatypeCons.cons (SmtType.TypeRef s') c
          rw [hsubst, subst_noop_dtc sub c X r0 rR h0 hR hc0 hcR]
      | _ =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf0 hwfR
          split at hwf0
          · next hT0 =>
              split at hwfR
              · next hTR =>
                  simp only [__smtx_dtc_substitute]
                  rw [subst_noop_ty sub _ X r0 rR h0 hR hT0 hTR,
                    subst_noop_dtc sub c X r0 rR h0 hR hwf0 hwfR]
              · next => exact absurd hwfR (by simp)
          · next => exact absurd hwf0 (by simp)
end



/-- Two ref-lists are equivalent if they have the same membership. -/
def reflEquiv (r1 r2 : RefList) : Prop :=
  ∀ x, native_reflist_contains r1 x = native_reflist_contains r2 x

theorem reflEquiv_insert {r1 r2 : RefList} (h : reflEquiv r1 r2) (s : native_String) :
    reflEquiv (native_reflist_insert r1 s) (native_reflist_insert r2 s) := by
  intro x
  simp only [native_reflist_contains, native_reflist_insert, List.mem_cons]
  rw [decide_eq_decide]
  have := h x
  simp only [native_reflist_contains] at this
  rw [decide_eq_decide] at this
  exact or_congr_right this

/- wf_rec depends on refs only through membership. -/
mutual
theorem wf_congr_ty :
    (T : SmtType) → {r1 r2 : RefList} → reflEquiv r1 r2 →
      __smtx_type_wf_rec T r1 = true → __smtx_type_wf_rec T r2 = true
  | SmtType.Datatype s d, r1, r2, hEq, hwf => by
      have hc : native_reflist_contains r1 s = native_reflist_contains r2 s := hEq s
      cases hr : native_reflist_contains r1 s
      · have hr2 : native_reflist_contains r2 s = false := by rw [← hc]; exact hr
        have hd : __smtx_dt_wf_rec d (native_reflist_insert r1 s) = true := by
          simpa [__smtx_type_wf_rec, native_ite, hr] using hwf
        have hd2 := wf_congr_dt d (reflEquiv_insert hEq s) hd
        simp [__smtx_type_wf_rec, native_ite, hr2, hd2]
      · simp [__smtx_type_wf_rec, native_ite, hr] at hwf
  | SmtType.TypeRef s, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec] at hwf
  | SmtType.Seq x, r1, r2, hEq, hwf => by simpa [__smtx_type_wf_rec] using hwf
  | SmtType.Set x, r1, r2, hEq, hwf => by simpa [__smtx_type_wf_rec] using hwf
  | SmtType.Map x y, r1, r2, hEq, hwf => by simpa [__smtx_type_wf_rec] using hwf
  | SmtType.FunType x y, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec] at hwf
  | SmtType.DtcAppType x y, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec] at hwf
  | SmtType.None, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec] at hwf
  | SmtType.RegLan, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec] at hwf
  | SmtType.Bool, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec]
  | SmtType.Int, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec]
  | SmtType.Real, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec]
  | SmtType.BitVec n, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec]
  | SmtType.Char, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec]
  | SmtType.USort n, r1, r2, hEq, hwf => by simp [__smtx_type_wf_rec]

theorem wf_congr_dt :
    (W : SmtDatatype) → {r1 r2 : RefList} → reflEquiv r1 r2 →
      __smtx_dt_wf_rec W r1 = true → __smtx_dt_wf_rec W r2 = true
  | SmtDatatype.null, r1, r2, hEq, hwf => by simp [__smtx_dt_wf_rec] at hwf
  | SmtDatatype.sum c SmtDatatype.null, r1, r2, hEq, hwf => by
      simp only [__smtx_dt_wf_rec] at hwf ⊢
      exact wf_congr_dtc c hEq hwf
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), r1, r2, hEq, hwf => by
      simp only [__smtx_dt_wf_rec, native_ite] at hwf ⊢
      have hc : __smtx_dt_cons_wf_rec c r1 = true := by
        cases hcc : __smtx_dt_cons_wf_rec c r1 <;> simp [hcc] at hwf ⊢
      have hd : __smtx_dt_wf_rec (SmtDatatype.sum c2 d2) r1 = true := by rw [hc] at hwf; simpa using hwf
      rw [if_pos (wf_congr_dtc c hEq hc)]; exact wf_congr_dt (SmtDatatype.sum c2 d2) hEq hd

theorem wf_congr_dtc :
    (c : SmtDatatypeCons) → {r1 r2 : RefList} → reflEquiv r1 r2 →
      __smtx_dt_cons_wf_rec c r1 = true → __smtx_dt_cons_wf_rec c r2 = true
  | SmtDatatypeCons.unit, r1, r2, hEq, hwf => by simp [__smtx_dt_cons_wf_rec]
  | SmtDatatypeCons.cons T c, r1, r2, hEq, hwf => by
      cases T with
      | TypeRef s =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf ⊢
          have hs : native_reflist_contains r1 s = true := by
            by_cases hc : native_reflist_contains r1 s = true
            · exact hc
            · rw [if_neg hc] at hwf; exact absurd hwf (by simp)
          have hs2 : native_reflist_contains r2 s = true := by rw [← hEq s]; exact hs
          have hc1 : __smtx_dt_cons_wf_rec c r1 = true := by rw [if_pos hs] at hwf; exact hwf
          rw [if_pos hs2, wf_congr_dtc c hEq hc1]
      | _ =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf ⊢
          split at hwf
          · next hT =>
              have hc1 : __smtx_dt_cons_wf_rec c r1 = true := hwf
              rw [if_pos (wf_congr_ty _ hEq hT), wf_congr_dtc c hEq hc1]
          · next => exact absurd hwf (by simp)
end

/- noStray s D W: every Datatype s ... reachable by the lift's recursion has body = D. Lift is shallow on non-datatype types. -/
mutual
def noStrayTy (s : native_String) (D : SmtDatatype) : SmtType → Bool
  | SmtType.Datatype s2 d2 =>
      native_ite (native_Teq (SmtType.Datatype s D) (SmtType.Datatype s2 d2))
        true
        (native_and (native_not (native_streq s2 s)) (noStrayDt s D d2))
  | _ => true
def noStrayDt (s : native_String) (D : SmtDatatype) : SmtDatatype → Bool
  | SmtDatatype.sum c d => native_and (noStrayDtc s D c) (noStrayDt s D d)
  | SmtDatatype.null => true
def noStrayDtc (s : native_String) (D : SmtDatatype) : SmtDatatypeCons → Bool
  | SmtDatatypeCons.cons T c => native_and (noStrayTy s D T) (noStrayDtc s D c)
  | SmtDatatypeCons.unit => true
end

/- LIFT-WF-PRESERVATION: lifting a noStray wf datatype stays wf once s is added to scope. -/
mutual
theorem lift_wf_pres_dt (s : native_String) (D : SmtDatatype) :
    (W : SmtDatatype) → (refs : RefList) →
      __smtx_dt_wf_rec W refs = true →
      noStrayDt s D W = true →
      __smtx_dt_wf_rec (__smtx_dt_lift s D W) (native_reflist_insert refs s) = true
  | SmtDatatype.null, refs, hwf, _ => by simp [__smtx_dt_wf_rec] at hwf
  | SmtDatatype.sum c SmtDatatype.null, refs, hwf, hns => by
      simp only [__smtx_dt_wf_rec] at hwf
      simp only [noStrayDt, native_and, Bool.and_eq_true] at hns
      show __smtx_dt_wf_rec (SmtDatatype.sum (__smtx_dtc_lift s D c) (__smtx_dt_lift s D SmtDatatype.null))
            (native_reflist_insert refs s) = true
      simp only [__smtx_dt_lift, __smtx_dt_wf_rec]
      exact lift_wf_pres_dtc s D c refs hwf hns.1
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), refs, hwf, hns => by
      simp only [__smtx_dt_wf_rec, native_ite] at hwf
      simp only [noStrayDt, native_and, Bool.and_eq_true] at hns
      have hc : __smtx_dt_cons_wf_rec c refs = true := by
        cases hcc : __smtx_dt_cons_wf_rec c refs <;> simp [hcc] at hwf ⊢
      have hd : __smtx_dt_wf_rec (SmtDatatype.sum c2 d2) refs = true := by rw [hc] at hwf; simpa using hwf
      have hns_d : noStrayDt s D (SmtDatatype.sum c2 d2) = true := by
        simp only [noStrayDt, native_and, Bool.and_eq_true]; exact hns.2
      have hcL := lift_wf_pres_dtc s D c refs hc hns.1
      have hdL := lift_wf_pres_dt s D (SmtDatatype.sum c2 d2) refs hd hns_d
      simp only [__smtx_dt_lift] at hdL ⊢
      simp only [__smtx_dt_wf_rec, native_ite, hcL, if_true]
      exact hdL

theorem lift_wf_pres_dtc (s : native_String) (D : SmtDatatype) :
    (c : SmtDatatypeCons) → (refs : RefList) →
      __smtx_dt_cons_wf_rec c refs = true →
      noStrayDtc s D c = true →
      __smtx_dt_cons_wf_rec (__smtx_dtc_lift s D c) (native_reflist_insert refs s) = true
  | SmtDatatypeCons.unit, refs, _, _ => by simp [__smtx_dtc_lift, __smtx_dt_cons_wf_rec]
  | SmtDatatypeCons.cons T c, refs, hwf, hns => by
      simp only [noStrayDtc, native_and, Bool.and_eq_true] at hns
      simp only [__smtx_dtc_lift]
      cases T with
      | TypeRef s2 =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
          simp only [__smtx_type_lift]
          have hs2 : native_reflist_contains refs s2 = true := by
            by_cases hc : native_reflist_contains refs s2 = true
            · exact hc
            · rw [if_neg hc] at hwf; exact absurd hwf (by simp)
          have hcr : __smtx_dt_cons_wf_rec c refs = true := by rw [if_pos hs2] at hwf; exact hwf
          have hs2' : native_reflist_contains (native_reflist_insert refs s) s2 = true := by
            simp [native_reflist_contains, native_reflist_insert, List.mem_cons]
            right; simpa [native_reflist_contains] using hs2
          simp only [__smtx_dt_cons_wf_rec, native_ite, hs2', if_true]
          exact lift_wf_pres_dtc s D c refs hcr hns.2
      | Datatype s2 d2 =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
          have hns2 : noStrayTy s D (SmtType.Datatype s2 d2) = true := hns.1
          have hcr : __smtx_dt_cons_wf_rec c refs = true := by
            split at hwf
            · exact hwf
            · exact absurd hwf (by simp)
          have hcL := lift_wf_pres_dtc s D c refs hcr hns.2
          have hTwf : __smtx_type_wf_rec (SmtType.Datatype s2 d2) refs = true := by
            split at hwf
            · next h => exact h
            · exact absurd hwf (by simp)
          simp only [__smtx_type_lift]
          by_cases hTeq : native_Teq (SmtType.Datatype s D) (SmtType.Datatype s2 d2) = true
          · -- folded → TypeRef s
            rw [native_ite, if_pos hTeq]
            have hsmem : native_reflist_contains (native_reflist_insert refs s) s = true := by
              simp [native_reflist_contains, native_reflist_insert, List.mem_cons]
            simp only [__smtx_dt_cons_wf_rec, native_ite, hsmem, if_true]
            exact hcL
          · -- not folded → Datatype s2 (lift d2); from noStray, s2 ≠ s
            rw [native_ite, if_neg hTeq]
            have hs2ne : native_streq s2 s = false := by
              simp only [noStrayTy, native_ite, if_neg hTeq, native_and, native_not,
                Bool.and_eq_true] at hns2
              cases hstr : native_streq s2 s
              · rfl
              · simp [hstr] at hns2
            have hd2ns : noStrayDt s D d2 = true := by
              simp only [noStrayTy, native_ite, if_neg hTeq, native_and, native_not,
                Bool.and_eq_true] at hns2
              exact hns2.2
            -- wf of Datatype s2 d2 at refs ⇒ s2 ∉ refs, d2 wf at insert refs s2
            have hns2refs : native_reflist_contains refs s2 = false := by
              cases hc : native_reflist_contains refs s2 <;>
                simp [__smtx_type_wf_rec, native_ite, hc] at hTwf ⊢
            have hd2wf : __smtx_dt_wf_rec d2 (native_reflist_insert refs s2) = true := by
              simp [__smtx_type_wf_rec, native_ite, hns2refs] at hTwf; exact hTwf
            have hs2ne' : s2 ≠ s := by
              intro he; rw [he] at hs2ne; simp [native_streq] at hs2ne
            have hs2notins : native_reflist_contains (native_reflist_insert refs s) s2 = false := by
              simp [native_reflist_contains, native_reflist_insert, List.mem_cons, hs2ne']
              simpa [native_reflist_contains] using hns2refs
            -- recurse on d2 body
            have hd2L := lift_wf_pres_dt s D d2 (native_reflist_insert refs s2) hd2wf hd2ns
            -- congr: insert (insert refs s2) s  ~  insert (insert refs s) s2
            have hEquiv : reflEquiv (native_reflist_insert (native_reflist_insert refs s2) s)
                (native_reflist_insert (native_reflist_insert refs s) s2) := by
              intro x
              simp only [native_reflist_contains, native_reflist_insert, List.mem_cons]
              rw [decide_eq_decide]
              constructor
              · rintro (h | h | h)
                · exact Or.inr (Or.inl h)
                · exact Or.inl h
                · exact Or.inr (Or.inr h)
              · rintro (h | h | h)
                · exact Or.inr (Or.inl h)
                · exact Or.inl h
                · exact Or.inr (Or.inr h)
            have hd2L' := wf_congr_dt (__smtx_dt_lift s D d2) hEquiv hd2L
            have htywf : __smtx_type_wf_rec (SmtType.Datatype s2 (__smtx_dt_lift s D d2))
                (native_reflist_insert refs s) = true := by
              simp only [__smtx_type_wf_rec, native_ite, hs2notins, if_false]
              exact hd2L'
            simp only [__smtx_dt_cons_wf_rec, native_ite, htywf, if_true]
            exact hcL
      | _ =>
          -- non-Datatype, non-TypeRef field: lift is identity; wf_rec refs-independent here
          simp only [__smtx_type_lift]
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf ⊢
          split at hwf
          · next hT =>
              have hcr : __smtx_dt_cons_wf_rec c refs = true := hwf
              have hcL := lift_wf_pres_dtc s D c refs hcr hns.2
              -- non-Datatype field: wf_rec ignores refs, so the if-condition matches hT by defeq
              split
              · exact hcL
              · next hF => exact absurd hT hF
          · next => exact absurd hwf (by simp)
end


/- `noStray` is preserved by an unrelated lift `__smtx_*_lift s1 D1`, provided the target body `D2`
is itself stable under that lift (`lift s1 D1 D2 = D2`). Used to maintain the substitute-recursion
invariant as the substituting datatype is re-lifted under each datatype binder. -/
mutual
theorem noStray_lift_ty (s1 : native_String) (D1 : SmtDatatype)
    (s2 : native_String) (D2 : SmtDatatype) (hD2 : __smtx_dt_lift s1 D1 D2 = D2) :
    (T : SmtType) → noStrayTy s2 D2 T = true →
      noStrayTy s2 D2 (__smtx_type_lift s1 D1 T) = true
  | SmtType.Datatype s3 d3, h => by
      simp only [__smtx_type_lift]
      by_cases hfold : native_Teq (SmtType.Datatype s1 D1) (SmtType.Datatype s3 d3) = true
      · rw [native_ite, if_pos hfold]; simp [noStrayTy]
      · rw [native_ite, if_neg hfold]
        by_cases hm : native_Teq (SmtType.Datatype s2 D2) (SmtType.Datatype s3 d3) = true
        · -- s2 = s3 and D2 = d3
          obtain ⟨hs, hd⟩ : s2 = s3 ∧ D2 = d3 := by simpa [native_Teq] using hm
          subst hs; subst hd
          simp only [noStrayTy, native_ite]
          rw [if_pos (by simp [native_Teq, hD2])]
        · -- not matched: from h, s3 ≠ s2 and noStrayDt s2 D2 d3
          have hsplit : native_streq s3 s2 = false ∧ noStrayDt s2 D2 d3 = true := by
            simp only [noStrayTy, native_ite, if_neg hm] at h
            cases hst : native_streq s3 s2 with
            | false => exact ⟨rfl, by simpa [native_and, native_not, hst] using h⟩
            | true => simp [native_and, native_not, hst] at h
          have hs3ne : s2 ≠ s3 := by
            intro he; subst he; simp [native_streq] at hsplit
          simp only [noStrayTy, native_ite]
          rw [if_neg (by
            intro hbad
            obtain ⟨hs', _⟩ : s2 = s3 ∧ D2 = __smtx_dt_lift s1 D1 d3 := by simpa [native_Teq] using hbad
            exact hs3ne hs')]
          simp only [native_and, native_not, Bool.and_eq_true]
          exact ⟨by simp [hsplit.1], noStray_lift_dt s1 D1 s2 D2 hD2 d3 hsplit.2⟩
  | SmtType.Seq x, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.Set x, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.Map x y, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.FunType x y, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.DtcAppType x y, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.TypeRef s, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.None, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.RegLan, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.Bool, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.Int, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.Real, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.BitVec n, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.Char, h => by simp [noStrayTy, __smtx_type_lift]
  | SmtType.USort n, h => by simp [noStrayTy, __smtx_type_lift]

theorem noStray_lift_dt (s1 : native_String) (D1 : SmtDatatype)
    (s2 : native_String) (D2 : SmtDatatype) (hD2 : __smtx_dt_lift s1 D1 D2 = D2) :
    (W : SmtDatatype) → noStrayDt s2 D2 W = true →
      noStrayDt s2 D2 (__smtx_dt_lift s1 D1 W) = true
  | SmtDatatype.null, h => by simp [noStrayDt, __smtx_dt_lift]
  | SmtDatatype.sum c d, h => by
      simp only [noStrayDt, native_and, Bool.and_eq_true] at h
      simp only [__smtx_dt_lift, noStrayDt, native_and, Bool.and_eq_true]
      exact ⟨noStray_lift_dtc s1 D1 s2 D2 hD2 c h.1, noStray_lift_dt s1 D1 s2 D2 hD2 d h.2⟩

theorem noStray_lift_dtc (s1 : native_String) (D1 : SmtDatatype)
    (s2 : native_String) (D2 : SmtDatatype) (hD2 : __smtx_dt_lift s1 D1 D2 = D2) :
    (c : SmtDatatypeCons) → noStrayDtc s2 D2 c = true →
      noStrayDtc s2 D2 (__smtx_dtc_lift s1 D1 c) = true
  | SmtDatatypeCons.unit, h => by simp [noStrayDtc, __smtx_dtc_lift]
  | SmtDatatypeCons.cons T c, h => by
      simp only [noStrayDtc, native_and, Bool.and_eq_true] at h
      simp only [__smtx_dtc_lift, noStrayDtc, native_and, Bool.and_eq_true]
      exact ⟨noStray_lift_ty s1 D1 s2 D2 hD2 T h.1, noStray_lift_dtc s1 D1 s2 D2 hD2 c h.2⟩
end


/- `noDt s W`: `W` has no `Datatype s …` reachable by the lift's recursion. The SMT lift `__smtx_*_lift
s D` is then the identity (nothing matches the fold pattern `Datatype s D`). -/
mutual
def noDtTy (s : native_String) : SmtType → Bool
  | SmtType.Datatype s2 d2 => native_and (native_not (native_streq s2 s)) (noDtDt s d2)
  | _ => true
def noDtDt (s : native_String) : SmtDatatype → Bool
  | SmtDatatype.sum c d => native_and (noDtDtc s c) (noDtDt s d)
  | SmtDatatype.null => true
def noDtDtc (s : native_String) : SmtDatatypeCons → Bool
  | SmtDatatypeCons.cons T c => native_and (noDtTy s T) (noDtDtc s c)
  | SmtDatatypeCons.unit => true
end

mutual
theorem lift_noop_no_dt_ty (s : native_String) (D : SmtDatatype) :
    (T : SmtType) → noDtTy s T = true → __smtx_type_lift s D T = T
  | SmtType.Datatype s2 d2, h => by
      simp only [noDtTy, native_and, native_not, Bool.and_eq_true] at h
      have hs2 : native_streq s2 s = false := by
        cases hst : native_streq s2 s
        · rfl
        · simp [hst] at h
      have hsne : ¬ (s2 = s) := by intro he; subst he; simp [native_streq] at hs2
      simp only [__smtx_type_lift, native_ite]
      rw [if_neg (by
        intro hbad
        obtain ⟨he, _⟩ : s = s2 ∧ D = d2 := by simpa [native_Teq] using hbad
        exact hsne he.symm)]
      rw [lift_noop_no_dt_dt s D d2 h.2]
  | SmtType.Seq x, h => by simp [__smtx_type_lift]
  | SmtType.Set x, h => by simp [__smtx_type_lift]
  | SmtType.Map x y, h => by simp [__smtx_type_lift]
  | SmtType.FunType x y, h => by simp [__smtx_type_lift]
  | SmtType.DtcAppType x y, h => by simp [__smtx_type_lift]
  | SmtType.TypeRef s2, h => by simp [__smtx_type_lift]
  | SmtType.None, h => by simp [__smtx_type_lift]
  | SmtType.RegLan, h => by simp [__smtx_type_lift]
  | SmtType.Bool, h => by simp [__smtx_type_lift]
  | SmtType.Int, h => by simp [__smtx_type_lift]
  | SmtType.Real, h => by simp [__smtx_type_lift]
  | SmtType.BitVec n, h => by simp [__smtx_type_lift]
  | SmtType.Char, h => by simp [__smtx_type_lift]
  | SmtType.USort n, h => by simp [__smtx_type_lift]

theorem lift_noop_no_dt_dt (s : native_String) (D : SmtDatatype) :
    (W : SmtDatatype) → noDtDt s W = true → __smtx_dt_lift s D W = W
  | SmtDatatype.null, h => by simp [__smtx_dt_lift]
  | SmtDatatype.sum c d, h => by
      simp only [noDtDt, native_and, Bool.and_eq_true] at h
      simp only [__smtx_dt_lift]
      rw [lift_noop_no_dt_dtc s D c h.1, lift_noop_no_dt_dt s D d h.2]

theorem lift_noop_no_dt_dtc (s : native_String) (D : SmtDatatype) :
    (c : SmtDatatypeCons) → noDtDtc s c = true → __smtx_dtc_lift s D c = c
  | SmtDatatypeCons.unit, h => by simp [__smtx_dtc_lift]
  | SmtDatatypeCons.cons T c, h => by
      simp only [noDtDtc, native_and, Bool.and_eq_true] at h
      simp only [__smtx_dtc_lift]
      rw [lift_noop_no_dt_ty s D T h.1, lift_noop_no_dt_dtc s D c h.2]
end


/- If `s` is already in scope (`s ∈ refs`), a well-formed `W` has no `Datatype s …` at all (any such
binder would alias `s` and fail wf's no-aliasing check). Discharges the `noDt` side conditions in the
substitute recursion (the body under a `Datatype s` binder has no further `Datatype s`). -/
mutual
theorem noDt_of_wf_ty (s : native_String) :
    (T : SmtType) → (refs : RefList) → __smtx_type_wf_rec T refs = true →
      native_reflist_contains refs s = true → noDtTy s T = true
  | SmtType.Datatype s2 d2, refs, hwf, hmem => by
      have hns2 : native_reflist_contains refs s2 = false := by
        cases hc : native_reflist_contains refs s2 <;>
          simp [__smtx_type_wf_rec, native_ite, hc] at hwf ⊢
      have hd2 : __smtx_dt_wf_rec d2 (native_reflist_insert refs s2) = true := by
        simp [__smtx_type_wf_rec, native_ite, hns2] at hwf; exact hwf
      have hsne : native_streq s2 s = false := by
        cases hst : native_streq s2 s
        · rfl
        · exfalso
          have heq : s2 = s := by simpa [native_streq] using hst
          subst heq; rw [hmem] at hns2; simp at hns2
      have hmem2 : native_reflist_contains (native_reflist_insert refs s2) s = true := by
        simp [native_reflist_contains, native_reflist_insert, List.mem_cons]
        right; simpa [native_reflist_contains] using hmem
      simp only [noDtTy, native_and, native_not, Bool.and_eq_true]
      exact ⟨by simp [hsne], noDt_of_wf_dt s d2 (native_reflist_insert refs s2) hd2 hmem2⟩
  | SmtType.Seq x, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.Set x, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.Map x y, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.FunType x y, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.DtcAppType x y, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.TypeRef s2, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.None, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.RegLan, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.Bool, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.Int, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.Real, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.BitVec n, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.Char, refs, hwf, hmem => by simp [noDtTy]
  | SmtType.USort n, refs, hwf, hmem => by simp [noDtTy]

theorem noDt_of_wf_dt (s : native_String) :
    (W : SmtDatatype) → (refs : RefList) → __smtx_dt_wf_rec W refs = true →
      native_reflist_contains refs s = true → noDtDt s W = true
  | SmtDatatype.null, refs, hwf, _ => by simp [__smtx_dt_wf_rec] at hwf
  | SmtDatatype.sum c SmtDatatype.null, refs, hwf, hmem => by
      simp only [__smtx_dt_wf_rec] at hwf
      simp only [noDtDt, native_and, Bool.and_eq_true]
      exact ⟨noDt_of_wf_dtc s c refs hwf hmem, by simp [noDtDt]⟩
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), refs, hwf, hmem => by
      simp only [__smtx_dt_wf_rec, native_ite] at hwf
      have hc : __smtx_dt_cons_wf_rec c refs = true := by
        cases hcc : __smtx_dt_cons_wf_rec c refs <;> simp [hcc] at hwf ⊢
      have hd : __smtx_dt_wf_rec (SmtDatatype.sum c2 d2) refs = true := by rw [hc] at hwf; simpa using hwf
      have h1 := noDt_of_wf_dtc s c refs hc hmem
      have h2 := noDt_of_wf_dt s (SmtDatatype.sum c2 d2) refs hd hmem
      simp only [noDtDt, native_and, Bool.and_eq_true]
      refine ⟨h1, ?_⟩
      simpa only [noDtDt, native_and, Bool.and_eq_true] using h2

theorem noDt_of_wf_dtc (s : native_String) :
    (c : SmtDatatypeCons) → (refs : RefList) → __smtx_dt_cons_wf_rec c refs = true →
      native_reflist_contains refs s = true → noDtDtc s c = true
  | SmtDatatypeCons.unit, refs, _, _ => by simp [noDtDtc]
  | SmtDatatypeCons.cons T c, refs, hwf, hmem => by
      cases T with
      | TypeRef s2 =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
          have hcr : __smtx_dt_cons_wf_rec c refs = true := by
            by_cases hc : native_reflist_contains refs s2 = true
            · rw [if_pos hc] at hwf; exact hwf
            · rw [if_neg hc] at hwf; exact absurd hwf (by simp)
          simp only [noDtDtc, native_and, Bool.and_eq_true]
          exact ⟨by simp [noDtTy], noDt_of_wf_dtc s c refs hcr hmem⟩
      | _ =>
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
          split at hwf
          · next hT =>
              simp only [noDtDtc, native_and, Bool.and_eq_true]
              exact ⟨noDt_of_wf_ty s _ refs hT hmem, noDt_of_wf_dtc s c refs hwf hmem⟩
          · next => exact absurd hwf (by simp)
end

end Smtm
