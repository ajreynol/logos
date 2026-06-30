import Cpc.SmtModel
import Cpc.Proofs.SmtWfCompat

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
      have hd : dtAllWf d (native_reflist_insert refs s) = true :=
        (dtAllWf_of_type_wf_rec_datatype s d refs h).2
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
    (d : SmtDatatype) → (refs : RefList) → dtAllWf d refs = true → hasFreeDt sub refs d = false
  | SmtDatatype.null, refs, h => by simp [dtAllWf] at h
  | SmtDatatype.sum c SmtDatatype.null, refs, h => by
      simp only [dtAllWf] at h
      have hC := hasFreeDtc_eq_false_of_wf sub c refs h
      rw [hasFreeDt, hC, hasFreeDt]; rfl
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), refs, h => by
      simp only [dtAllWf, native_ite] at h
      have hc : __smtx_dt_cons_wf_rec c refs = true := by
        cases hcc : __smtx_dt_cons_wf_rec c refs <;> simp [hcc] at h ⊢
      have hd : dtAllWf (SmtDatatype.sum c2 d2) refs = true := by
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

theorem hasFreeDtc_tail_false_of_cons_false
    (sub : native_String) (refs : RefList) (T : SmtType) (c : SmtDatatypeCons)
    (h : hasFreeDtc sub refs (SmtDatatypeCons.cons T c) = false) :
    hasFreeDtc sub refs c = false := by
  cases T <;> simp [hasFreeDtc, native_or, Bool.or_eq_false_iff] at h
  all_goals exact h.2

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
      have hns0 : native_reflist_contains r0 s' = false := (dtAllWf_of_type_wf_rec_datatype s' X r0 hwf0).1
      have hX0 : dtAllWf X (native_reflist_insert r0 s') = true := (dtAllWf_of_type_wf_rec_datatype s' X r0 hwf0).2
      have hnsR : native_reflist_contains rR s' = false := (dtAllWf_of_type_wf_rec_datatype s' X rR hwfR).1
      have hXR : dtAllWf X (native_reflist_insert rR s') = true := (dtAllWf_of_type_wf_rec_datatype s' X rR hwfR).2
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
      dtAllWf W r0 = true →
      dtAllWf W rR = true →
      __smtx_dt_lift s D W = W
  | SmtDatatype.null, _, _, _, _, hwf0, _ => by simp [dtAllWf] at hwf0
  | SmtDatatype.sum c SmtDatatype.null, r0, rR, h0, hR, hwf0, hwfR => by
      simp only [dtAllWf] at hwf0 hwfR
      show SmtDatatype.sum (__smtx_dtc_lift s D c) SmtDatatype.null = SmtDatatype.sum c SmtDatatype.null
      rw [lift_noop_dtc s sub D hsne hFree c r0 rR h0 hR hwf0 hwfR]
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), r0, rR, h0, hR, hwf0, hwfR => by
      simp only [dtAllWf, native_ite] at hwf0 hwfR
      have hc0 : __smtx_dt_cons_wf_rec c r0 = true := by
        cases hcc : __smtx_dt_cons_wf_rec c r0 <;> simp [hcc] at hwf0 ⊢
      have hd0 : dtAllWf (SmtDatatype.sum c2 d2) r0 = true := by rw [hc0] at hwf0; simpa using hwf0
      have hcR : __smtx_dt_cons_wf_rec c rR = true := by
        cases hcc : __smtx_dt_cons_wf_rec c rR <;> simp [hcc] at hwfR ⊢
      have hdR : dtAllWf (SmtDatatype.sum c2 d2) rR = true := by rw [hcR] at hwfR; simpa using hwfR
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

/- If `hasFree…` says `sub` is absent in a scope that does not already bind `sub`,
then substituting `sub` is a no-op. `TypeRef` is only a well-scoped datatype-field
form, so the type-level lemma excludes a bare `TypeRef`. -/
mutual
theorem subst_noop_no_free_ty (sub : native_String) :
    (T : SmtType) → (X : SmtDatatype) → (refs : RefList) →
      (∀ s, T ≠ SmtType.TypeRef s) →
      native_reflist_contains refs sub = false →
      hasFreeTy sub refs T = false →
      __smtx_type_substitute sub X T = T
  | SmtType.Datatype s d, X, refs, _hNoRef, hNot, hFree => by
      simp only [hasFreeTy] at hFree
      simp only [__smtx_type_substitute]
      by_cases hs : sub = s
      · subst hs
        rw [native_ite, if_pos (by simp [native_streq])]
      · have hst : native_streq sub s = false := by
          simp [native_streq, hs]
        have hNot' : native_reflist_contains (native_reflist_insert refs s) sub = false := by
          simp [native_reflist_contains, native_reflist_insert, List.mem_cons]
          constructor
          · exact hs
          · simpa [native_reflist_contains] using hNot
        rw [native_ite, if_neg (by simpa [native_streq] using hs)]
        congr 1
        exact subst_noop_no_free_dt sub d (__smtx_dt_lift s d X)
          (native_reflist_insert refs s) hNot' hFree
  | SmtType.TypeRef s, X, refs, hNoRef, _hNot, _hFree => by
      exact False.elim (hNoRef s rfl)
  | SmtType.Seq A, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.Set A, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.Map A B, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.FunType A B, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.DtcAppType A B, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.None, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.RegLan, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.Bool, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.Int, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.Real, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.BitVec n, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.Char, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]
  | SmtType.USort n, X, refs, _hNoRef, _hNot, _hFree => by simp [__smtx_type_substitute]

theorem subst_noop_no_free_dt (sub : native_String) :
    (W : SmtDatatype) → (X : SmtDatatype) → (refs : RefList) →
      native_reflist_contains refs sub = false →
      hasFreeDt sub refs W = false →
      __smtx_dt_substitute sub X W = W
  | SmtDatatype.null, X, refs, hNot, hFree => by simp [__smtx_dt_substitute]
  | SmtDatatype.sum c d, X, refs, hNot, hFree => by
      simp only [hasFreeDt, native_or, Bool.or_eq_false_iff] at hFree
      simp only [__smtx_dt_substitute]
      rw [subst_noop_no_free_dtc sub c X refs hNot hFree.1,
        subst_noop_no_free_dt sub d X refs hNot hFree.2]

theorem subst_noop_no_free_dtc (sub : native_String) :
    (c : SmtDatatypeCons) → (X : SmtDatatype) → (refs : RefList) →
      native_reflist_contains refs sub = false →
      hasFreeDtc sub refs c = false →
      __smtx_dtc_substitute sub X c = c
  | SmtDatatypeCons.unit, X, refs, hNot, hFree => by simp [__smtx_dtc_substitute]
  | SmtDatatypeCons.cons T c, X, refs, hNot, hFree => by
      cases T with
      | TypeRef s =>
          simp only [hasFreeDtc, native_or, Bool.or_eq_false_iff] at hFree
          have hsne : sub ≠ s := by
            intro hs
            subst hs
            simp [native_and, native_not, hNot, native_streq] at hFree
          have hst : native_streq sub s = false := by
            simp [native_streq, hsne]
          simp only [__smtx_dtc_substitute]
          rw [subst_noop_no_free_dtc sub c X refs hNot hFree.2]
          simp [__smtx_type_substitute, native_ite, hst]
      | _ =>
          simp only [hasFreeDtc, native_or, Bool.or_eq_false_iff] at hFree
          simp only [__smtx_dtc_substitute]
          rw [subst_noop_no_free_dtc sub c X refs hNot hFree.2]
          rw [subst_noop_no_free_ty sub _ X refs (by intro s h; cases h) hNot hFree.1]
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
      have hns0 : native_reflist_contains r0 s' = false := (dtAllWf_of_type_wf_rec_datatype s' Y r0 hwf0).1
      have hY0 : dtAllWf Y (native_reflist_insert r0 s') = true := (dtAllWf_of_type_wf_rec_datatype s' Y r0 hwf0).2
      have hnsR : native_reflist_contains rR s' = false := (dtAllWf_of_type_wf_rec_datatype s' Y rR hwfR).1
      have hYR : dtAllWf Y (native_reflist_insert rR s') = true := (dtAllWf_of_type_wf_rec_datatype s' Y rR hwfR).2
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
      simp only [__smtx_type_substitute, native_ite, hstreq]
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
      dtAllWf W r0 = true →
      dtAllWf W rR = true →
      __smtx_dt_substitute sub X W = W
  | SmtDatatype.null, _, _, _, _, _, hwf0, _ => by simp [dtAllWf] at hwf0
  | SmtDatatype.sum c SmtDatatype.null, X, r0, rR, h0, hR, hwf0, hwfR => by
      simp only [dtAllWf] at hwf0 hwfR
      show SmtDatatype.sum (__smtx_dtc_substitute sub X c) SmtDatatype.null = SmtDatatype.sum c SmtDatatype.null
      rw [subst_noop_dtc sub c X r0 rR h0 hR hwf0 hwfR]
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), X, r0, rR, h0, hR, hwf0, hwfR => by
      simp only [dtAllWf, native_ite] at hwf0 hwfR
      have hc0 : __smtx_dt_cons_wf_rec c r0 = true := by
        cases hcc : __smtx_dt_cons_wf_rec c r0 <;> simp [hcc] at hwf0 ⊢
      have hd0 : dtAllWf (SmtDatatype.sum c2 d2) r0 = true := by rw [hc0] at hwf0; simpa using hwf0
      have hcR : __smtx_dt_cons_wf_rec c rR = true := by
        cases hcc : __smtx_dt_cons_wf_rec c rR <;> simp [hcc] at hwfR ⊢
      have hdR : dtAllWf (SmtDatatype.sum c2 d2) rR = true := by rw [hcR] at hwfR; simpa using hwfR
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
theorem noDt_lift_ty (s sub : native_String) (D : SmtDatatype) :
    (T : SmtType) → noDtTy sub T = true → noDtTy sub (__smtx_type_lift s D T) = true
  | SmtType.Datatype s2 d2, h => by
      have hParts : native_streq s2 sub = false ∧ noDtDt sub d2 = true := by
        simpa [noDtTy, native_and, native_not, Bool.and_eq_true] using h
      simp only [__smtx_type_lift]
      by_cases hFold : native_Teq (SmtType.Datatype s D) (SmtType.Datatype s2 d2) = true
      · rw [native_ite, if_pos hFold]
        simp [noDtTy]
      · rw [native_ite, if_neg hFold]
        simp only [noDtTy, native_and, native_not, Bool.and_eq_true]
        exact ⟨by
          cases hst : native_streq s2 sub <;> simp [hst] at hParts ⊢,
          noDt_lift_dt s sub D d2 hParts.2⟩
  | SmtType.Seq x, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Set x, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Map x y, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.FunType x y, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.DtcAppType x y, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.TypeRef s2, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.None, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.RegLan, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Bool, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Int, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Real, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.BitVec w, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Char, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.USort i, h => by simp [__smtx_type_lift, noDtTy]

theorem noDt_lift_dt (s sub : native_String) (D : SmtDatatype) :
    (W : SmtDatatype) → noDtDt sub W = true → noDtDt sub (__smtx_dt_lift s D W) = true
  | SmtDatatype.null, h => by simp [__smtx_dt_lift, noDtDt]
  | SmtDatatype.sum c d, h => by
      have hParts : noDtDtc sub c = true ∧ noDtDt sub d = true := by
        simpa [noDtDt, native_and, Bool.and_eq_true] using h
      simp only [__smtx_dt_lift, noDtDt, native_and, Bool.and_eq_true]
      exact ⟨noDt_lift_dtc s sub D c hParts.1, noDt_lift_dt s sub D d hParts.2⟩

theorem noDt_lift_dtc (s sub : native_String) (D : SmtDatatype) :
    (c : SmtDatatypeCons) → noDtDtc sub c = true → noDtDtc sub (__smtx_dtc_lift s D c) = true
  | SmtDatatypeCons.unit, h => by simp [__smtx_dtc_lift, noDtDtc]
  | SmtDatatypeCons.cons T c, h => by
      have hParts : noDtTy sub T = true ∧ noDtDtc sub c = true := by
        simpa [noDtDtc, native_and, Bool.and_eq_true] using h
      simp only [__smtx_dtc_lift, noDtDtc, native_and, Bool.and_eq_true]
      exact ⟨noDt_lift_ty s sub D T hParts.1, noDt_lift_dtc s sub D c hParts.2⟩
end

private theorem smtx_dt_cons_wf_tail_of_cons
    {T : SmtType} {c : SmtDatatypeCons} {refs : RefList}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases T <;> simp [__smtx_dt_cons_wf_rec, native_ite] at h ⊢
  all_goals first | exact h.2 | exact h.2.2

private theorem smtx_dt_cons_wf_head_of_cons_not_typeref
    {T : SmtType} {c : SmtDatatypeCons} {refs : RefList}
    (hNoTypeRef : ∀ r, T ≠ SmtType.TypeRef r)
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true) :
    __smtx_type_wf_rec T refs = true := by
  cases T with
  | None =>
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at h
  | Bool =>
      simp [__smtx_type_wf_rec]
  | Int =>
      simp [__smtx_type_wf_rec]
  | Real =>
      simp [__smtx_type_wf_rec]
  | RegLan =>
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at h
  | BitVec w =>
      simp [__smtx_type_wf_rec]
  | Map A B =>
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at h ⊢
      exact h.1
  | Set A =>
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at h ⊢
      exact h.1
  | Seq A =>
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at h ⊢
      exact h.1
  | Char =>
      simp [__smtx_type_wf_rec]
  | Datatype s D =>
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at h ⊢
      exact h.1
  | TypeRef r =>
      exact False.elim (hNoTypeRef r rfl)
  | USort u =>
      simp [__smtx_type_wf_rec]
  | FunType A B =>
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at h
  | DtcAppType A B =>
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at h

/- A one-sided version of `lift_noop_*`: if `W` is well-formed in a context where `sub`
is absent, and `W` contains no `Datatype sub ...` binder that could bind the target's
free `sub`, then lifting a datatype whose body has a free `sub` is a no-op. This is the
proof-side shape needed for translated tuple components: tuple construction gives WF at
the empty context, while `noDt` rules out the only binder that could hide the free ref. -/
mutual
theorem lift_noop_of_wf_no_dt_ty (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (T : SmtType) → (refs : RefList) →
      native_reflist_contains refs sub = false →
      __smtx_type_wf_rec T refs = true →
      noDtTy sub T = true →
      __smtx_type_lift s D T = T
  | SmtType.Datatype s' X, refs, hNot, hWf, hNoDt => by
      have hNoDt' : native_streq s' sub = false ∧ noDtDt sub X = true := by
        simpa [noDtTy, native_and, native_not, Bool.and_eq_true] using hNoDt
      have hNoRefs : native_reflist_contains refs s' = false := (dtAllWf_of_type_wf_rec_datatype s' X refs hWf).1
      have hXWf : dtAllWf X (native_reflist_insert refs s') = true := (dtAllWf_of_type_wf_rec_datatype s' X refs hWf).2
      have hSubNeS' : sub ≠ s' := by
        intro hEq
        subst hEq
        simp [native_streq] at hNoDt'
      have hNot' : native_reflist_contains (native_reflist_insert refs s') sub = false := by
        have hSubNotMem : sub ∉ refs := by
          simpa [native_reflist_contains] using hNot
        simp [native_reflist_contains, native_reflist_insert, List.mem_cons,
          hSubNeS', hSubNotMem]
      simp only [__smtx_type_lift]
      have hNoFold :
          ¬ native_Teq (SmtType.Datatype s D) (SmtType.Datatype s' X) = true := by
        intro hFold
        have hEq : SmtType.Datatype s D = SmtType.Datatype s' X :=
          of_decide_eq_true (by simpa [native_Teq] using hFold)
        injection hEq with hs hD
        subst hs
        subst hD
        have hFreeFalse :
            hasFreeDt sub (native_reflist_insert refs s) D = false :=
          hasFreeDt_eq_false_of_wf sub D (native_reflist_insert refs s) hXWf
        have hRefsEq :
            native_reflist_contains (native_reflist_insert refs s) sub =
              native_reflist_contains (native_reflist_insert native_reflist_nil s) sub := by
          have hSubNotMem : sub ∉ refs := by
            simpa [native_reflist_contains] using hNot
          simp [native_reflist_contains, native_reflist_insert, List.mem_cons,
            hsne, hSubNotMem, native_reflist_nil]
        have hFreeTrue :
            hasFreeDt sub (native_reflist_insert refs s) D = true := by
          rw [hasFreeDt_refs_irrel sub D (native_reflist_insert refs s)
            (native_reflist_insert native_reflist_nil s) hRefsEq]
          exact hFree
        rw [hFreeFalse] at hFreeTrue
        cases hFreeTrue
      rw [native_ite, if_neg hNoFold]
      congr 1
      exact lift_noop_of_wf_no_dt_dt s sub D hsne hFree X
        (native_reflist_insert refs s') hNot' hXWf hNoDt'.2
  | SmtType.TypeRef s', refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_lift]
  | SmtType.Seq X, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_lift]
  | SmtType.Set X, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_lift]
  | SmtType.Map X Y, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_lift]
  | SmtType.FunType X Y, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.DtcAppType X Y, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.None, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.RegLan, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Bool, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_lift]
  | SmtType.Int, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_lift]
  | SmtType.Real, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_lift]
  | SmtType.BitVec w, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_lift]
  | SmtType.Char, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_lift]
  | SmtType.USort i, refs, hNot, hWf, hNoDt => by
      simp [__smtx_type_lift]

theorem lift_noop_of_wf_no_dt_dt (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (W : SmtDatatype) → (refs : RefList) →
      native_reflist_contains refs sub = false →
      dtAllWf W refs = true →
      noDtDt sub W = true →
      __smtx_dt_lift s D W = W
  | SmtDatatype.null, refs, hNot, hWf, hNoDt => by
      simp [dtAllWf] at hWf
  | SmtDatatype.sum c d, refs, hNot, hWf, hNoDt => by
      simp only [noDtDt, native_and, Bool.and_eq_true] at hNoDt
      have hCons : __smtx_dt_cons_wf_rec c refs = true := by
        cases hC : __smtx_dt_cons_wf_rec c refs <;>
          cases d <;> simp [dtAllWf, native_ite, hC] at hWf ⊢
      cases d with
      | null =>
          simp [__smtx_dt_lift,
            lift_noop_of_wf_no_dt_dtc s sub D hsne hFree c refs hNot hCons hNoDt.1]
      | sum cTail dTail =>
          have hTail :
              dtAllWf (SmtDatatype.sum cTail dTail) refs = true := by
            simpa [dtAllWf, native_ite, hCons] using hWf
          have hC :=
            lift_noop_of_wf_no_dt_dtc s sub D hsne hFree c refs hNot hCons hNoDt.1
          have hD :=
            lift_noop_of_wf_no_dt_dt s sub D hsne hFree
              (SmtDatatype.sum cTail dTail) refs hNot hTail hNoDt.2
          change
            SmtDatatype.sum (__smtx_dtc_lift s D c)
                (__smtx_dt_lift s D (SmtDatatype.sum cTail dTail)) =
              SmtDatatype.sum c (SmtDatatype.sum cTail dTail)
          rw [hC, hD]

theorem lift_noop_of_wf_no_dt_dtc (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (c : SmtDatatypeCons) → (refs : RefList) →
      native_reflist_contains refs sub = false →
      __smtx_dt_cons_wf_rec c refs = true →
      noDtDtc sub c = true →
      __smtx_dtc_lift s D c = c
  | SmtDatatypeCons.unit, refs, hNot, hWf, hNoDt => by
      simp [__smtx_dtc_lift]
  | SmtDatatypeCons.cons T c, refs, hNot, hWf, hNoDt => by
      simp only [noDtDtc, native_and, Bool.and_eq_true] at hNoDt
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        smtx_dt_cons_wf_tail_of_cons hWf
      by_cases hTypeRef : ∃ r, T = SmtType.TypeRef r
      · obtain ⟨r, rfl⟩ := hTypeRef
        simp [__smtx_dtc_lift, __smtx_type_lift,
          lift_noop_of_wf_no_dt_dtc s sub D hsne hFree c refs hNot hTail hNoDt.2]
      · have hNoTypeRef : ∀ r, T ≠ SmtType.TypeRef r := by
          intro r hEq
          exact hTypeRef ⟨r, hEq⟩
        have hHead : __smtx_type_wf_rec T refs = true :=
          smtx_dt_cons_wf_head_of_cons_not_typeref
            (T := T) (c := c) (refs := refs) hNoTypeRef hWf
        have hT :=
          lift_noop_of_wf_no_dt_ty s sub D hsne hFree T refs hNot hHead hNoDt.1
        have hC :=
          lift_noop_of_wf_no_dt_dtc s sub D hsne hFree c refs hNot hTail hNoDt.2
        simp [__smtx_dtc_lift, hT, hC]
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
      have hns2 : native_reflist_contains refs s2 = false := (dtAllWf_of_type_wf_rec_datatype s2 d2 refs hwf).1
      have hd2 : dtAllWf d2 (native_reflist_insert refs s2) = true := (dtAllWf_of_type_wf_rec_datatype s2 d2 refs hwf).2
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
    (W : SmtDatatype) → (refs : RefList) → dtAllWf W refs = true →
      native_reflist_contains refs s = true → noDtDt s W = true
  | SmtDatatype.null, refs, hwf, _ => by simp [dtAllWf] at hwf
  | SmtDatatype.sum c SmtDatatype.null, refs, hwf, hmem => by
      simp only [dtAllWf] at hwf
      simp only [noDtDt, native_and, Bool.and_eq_true]
      exact ⟨noDt_of_wf_dtc s c refs hwf hmem, by simp⟩
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), refs, hwf, hmem => by
      simp only [dtAllWf, native_ite] at hwf
      have hc : __smtx_dt_cons_wf_rec c refs = true := by
        cases hcc : __smtx_dt_cons_wf_rec c refs <;> simp [hcc] at hwf ⊢
      have hd : dtAllWf (SmtDatatype.sum c2 d2) refs = true := by rw [hc] at hwf; simpa using hwf
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


