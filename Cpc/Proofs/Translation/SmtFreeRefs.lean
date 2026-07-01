import Cpc.SmtModel

/-!
# SMT free type-references, aliasing and datatype occurrence tracking

Infrastructure for the `dtMutual` lift↔translation correctness work.

`__smtx_type_wf` was rewritten (branch `typeWf-0701`) from a `RefList`-scoped algorithm
(`__smtx_type_wf_rec T refs`, rejecting any `Datatype s …` nested under an enclosing `Datatype s`
of the same name — "no aliasing") to a two-argument substitution algorithm
(`__smtx_type_wf_rec F U`, checking `U` structurally against the once-unfolded/substituted `F`).
The new algorithm has **no scope/ref tracking at all**, and empirically **permits aliasing**
(`#eval __smtx_type_wf (Datatype "D" (sum (cons (Datatype "D" (sum unit null)) unit) null))`
returns `true`). This is intentional (see session discussion): values carry their full `(s, d)`
pair, so two same-named datatypes with different bodies remain distinguished at the value level,
and the eo→smt translation already permits aliasing syntactically (only rejects it via the old
smt-wf check, which is gone).

Consequently the OLD reflist-scoped machinery that this file used to carry — `hasFree*_eq_false_of_wf`,
`lift_noop_ty/dt/dtc`, `subst_noop_ty/dt/dtc`, `wf_congr_*`, `lift_wf_pres_*`, `noDt_of_wf_*` — is
**no longer sound**: those theorems all ultimately relied on "a well-formed datatype named `s` has no
further `Datatype s` nested inside it", which is simply false now. They have been deleted.

What survives (and is reused below) is the purely **syntactic** layer: predicates like `hasFreeTy`,
`noDtTy`, `noStrayTy`, `consistentWithTy` and the no-op lemmas stated directly in terms of them
(`lift_noop_no_dt_*`, `subst_noop_no_free_*`) never depended on well-formedness or the ref-scoping
algorithm — they are purely about term structure — so they compile unchanged against the new
`SmtModel`.

The alias-freeness that the lift/substitute correspondence proofs need is now sourced from the
**eo-validity** side in `Cpc.Proofs.Translation.EoTypeofCore`, not from smt well-formedness: eo-level
tuple *components* are validated at an empty reference scope (`eo_type_valid_rec []`), so a validly
translated tuple interior can never contain a bare `SmtType.TypeRef` reachable from a `DatatypeTypeRef`
at all (any such reference would need a nonempty enclosing scope). That structural fact — not
"well-formed ⟹ no aliasing" — is what makes substitution a no-op on tuple interiors.
-/

open SmtEval
namespace Smtm

/- `hasFreeTy sub refs T` holds iff `T` contains a `TypeRef sub` not bound by `refs` or by an
enclosing datatype. This is a purely syntactic scoping computation (independent of `__smtx_type_wf`)
mirroring how `Datatype`/`Seq`/`Set`/`Map` reset or extend a name-scope during traversal. -/
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

/- If `s` is absent from a structure at `refs` (per `hasFree…`), substituting `s` is a no-op.
`TypeRef` is only a well-scoped datatype-field form, so the type-level lemma excludes a bare
`TypeRef`. Purely syntactic; unaffected by the `__smtx_type_wf` rewrite. -/
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

/- `noStrayTy s D W`: every `Datatype s …` reachable in `W` has body exactly `D`. Purely syntactic. -/
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

/- `noStray` is preserved by an unrelated lift `__smtx_*_lift s1 D1`, provided the target body `D2`
is itself stable under that lift (`lift s1 D1 D2 = D2`). -/
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
        · obtain ⟨hs, hd⟩ : s2 = s3 ∧ D2 = d3 := by simpa [native_Teq] using hm
          subst hs; subst hd
          simp only [noStrayTy, native_ite]
          rw [if_pos (by simp [native_Teq, hD2])]
        · have hsplit : native_streq s3 s2 = false ∧ noStrayDt s2 D2 d3 = true := by
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
s D` is then the identity (nothing matches the fold pattern `Datatype s D`). Purely syntactic. -/
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

/- If `T` has no `Datatype s …` reachable at all (`noDtTy s T`), lifting `s` within `T` is
trivially a no-op: nothing can match the fold pattern `Datatype s D`, regardless of `D`.
Purely syntactic (no well-formedness needed). -/
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

/- One-sided version of `lift_noop_no_dt_*`, needed for the case where the *ambient* wf fact we
have is the new-algorithm two-argument (self-diagonal) well-formedness rather than a bare `noDt`
fact for the fold name `s` itself. `noDt sub T` (about a *different*, outer name `sub`) plus `hFree`
(the fold target `D` genuinely references `sub` freely) together rule out `T` folding onto the exact
target `Datatype s D` at any position — this is the capture-avoidance argument used when substitution
descends under a further datatype binder and needs to re-fold `s` before recursing.

TODO(typeWf-0701 aliasing refactor): re-derive the "no accidental fold" step without appeal to a
`RefList`-scoped well-formedness fact (the old proof used `wf @ r0` + `wf @ rR` doubly-scoped
well-formedness, which no longer exists). Left as `sorry` — genuinely open under the new algorithm;
the callers only need this fact for capture-avoidance during nested substitution, not for the SELF
(one-level) substitute case that datatype typeof-preservation actually uses. -/
mutual
theorem lift_noop_of_wf_no_dt_ty (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (T : SmtType) → __smtx_type_wf_rec T T = true → noDtTy sub T = true →
      __smtx_type_lift s D T = T
  | T, hWf, hNoDt => by
      sorry

theorem lift_noop_of_wf_no_dt_dt (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (W : SmtDatatype) → __smtx_dt_wf_rec W W = true → noDtDt sub W = true →
      __smtx_dt_lift s D W = W
  | W, hWf, hNoDt => by
      sorry

theorem lift_noop_of_wf_no_dt_dtc (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (c : SmtDatatypeCons) → __smtx_dt_cons_wf_rec c c = true → noDtDtc sub c = true →
      __smtx_dtc_lift s D c = c
  | c, hWf, hNoDt => by
      sorry
end

/- `consistentWith D0 W`: every `Datatype s' E'` reachable in `W` is `noStray`-consistent with `D0`
(i.e. all `Datatype s'` in `D0` have body `E'`). Purely syntactic. -/
mutual
def consistentWithTy (D0 : SmtDatatype) : SmtType → Bool
  | SmtType.Datatype s' E' => native_and (noStrayDt s' E' D0) (consistentWithDt D0 E')
  | _ => true
def consistentWithDt (D0 : SmtDatatype) : SmtDatatype → Bool
  | SmtDatatype.sum c d => native_and (consistentWithDtc D0 c) (consistentWithDt D0 d)
  | SmtDatatype.null => true
def consistentWithDtc (D0 : SmtDatatype) : SmtDatatypeCons → Bool
  | SmtDatatypeCons.cons T c => native_and (consistentWithTy D0 T) (consistentWithDtc D0 c)
  | SmtDatatypeCons.unit => true
end

/- MAINTENANCE: lifting the comparison target `D0` by an `s'`-fold (with `W` free of `Datatype s'`)
preserves `consistentWith`. This is the step that keeps the invariant alive as the substituting
datatype is re-lifted under each binder in the recursion. -/
mutual
theorem consistentWith_maintained_ty (s' : native_String) (B : SmtDatatype) (D0 : SmtDatatype) :
    (T : SmtType) → noDtTy s' T = true → consistentWithTy D0 T = true →
      consistentWithTy (__smtx_dt_lift s' B D0) T = true
  | SmtType.Datatype s'' E'', hnd, hcw => by
      simp only [noDtTy, native_and, Bool.and_eq_true] at hnd
      simp only [consistentWithTy, native_and, Bool.and_eq_true] at hcw
      have hD2 : __smtx_dt_lift s' B E'' = E'' := lift_noop_no_dt_dt s' B E'' hnd.2
      simp only [consistentWithTy, native_and, Bool.and_eq_true]
      exact ⟨noStray_lift_dt s' B s'' E'' hD2 D0 hcw.1,
             consistentWith_maintained_dt s' B D0 E'' hnd.2 hcw.2⟩
  | SmtType.Seq x, _, _ => by simp [consistentWithTy]
  | SmtType.Set x, _, _ => by simp [consistentWithTy]
  | SmtType.Map x y, _, _ => by simp [consistentWithTy]
  | SmtType.FunType x y, _, _ => by simp [consistentWithTy]
  | SmtType.DtcAppType x y, _, _ => by simp [consistentWithTy]
  | SmtType.TypeRef s, _, _ => by simp [consistentWithTy]
  | SmtType.None, _, _ => by simp [consistentWithTy]
  | SmtType.RegLan, _, _ => by simp [consistentWithTy]
  | SmtType.Bool, _, _ => by simp [consistentWithTy]
  | SmtType.Int, _, _ => by simp [consistentWithTy]
  | SmtType.Real, _, _ => by simp [consistentWithTy]
  | SmtType.BitVec n, _, _ => by simp [consistentWithTy]
  | SmtType.Char, _, _ => by simp [consistentWithTy]
  | SmtType.USort n, _, _ => by simp [consistentWithTy]

theorem consistentWith_maintained_dt (s' : native_String) (B : SmtDatatype) (D0 : SmtDatatype) :
    (W : SmtDatatype) → noDtDt s' W = true → consistentWithDt D0 W = true →
      consistentWithDt (__smtx_dt_lift s' B D0) W = true
  | SmtDatatype.null, _, _ => by simp [consistentWithDt]
  | SmtDatatype.sum c d, hnd, hcw => by
      simp only [noDtDt, native_and, Bool.and_eq_true] at hnd
      simp only [consistentWithDt, native_and, Bool.and_eq_true] at hcw
      simp only [consistentWithDt, native_and, Bool.and_eq_true]
      exact ⟨consistentWith_maintained_dtc s' B D0 c hnd.1 hcw.1,
             consistentWith_maintained_dt s' B D0 d hnd.2 hcw.2⟩

theorem consistentWith_maintained_dtc (s' : native_String) (B : SmtDatatype) (D0 : SmtDatatype) :
    (c : SmtDatatypeCons) → noDtDtc s' c = true → consistentWithDtc D0 c = true →
      consistentWithDtc (__smtx_dt_lift s' B D0) c = true
  | SmtDatatypeCons.unit, _, _ => by simp [consistentWithDtc]
  | SmtDatatypeCons.cons T c, hnd, hcw => by
      simp only [noDtDtc, native_and, Bool.and_eq_true] at hnd
      simp only [consistentWithDtc, native_and, Bool.and_eq_true] at hcw
      simp only [consistentWithDtc, native_and, Bool.and_eq_true]
      exact ⟨consistentWith_maintained_ty s' B D0 T hnd.1 hcw.1,
             consistentWith_maintained_dtc s' B D0 c hnd.2 hcw.2⟩
end

/-- Field extraction: a `Datatype s' E'` field of a `consistentWith`-D0 datatype is noStray-consistent
with D0 (and its body is too). -/
theorem noStray_of_consistentWith (D0 : SmtDatatype) (s' : native_String) (E' : SmtDatatype)
    (h : consistentWithTy D0 (SmtType.Datatype s' E') = true) :
    noStrayDt s' E' D0 = true := by
  simp only [consistentWithTy, native_and, Bool.and_eq_true] at h
  exact h.1

end Smtm
