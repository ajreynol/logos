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
      by_cases hfold : native_streq s1 s3 = true
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
      by_cases hFold : native_streq s s2 = true
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
        have he : s = s2 := by simpa [native_streq] using hbad
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

/-! ### Substitution images

`imgTy refs F U` says `F` is obtained from `U` by substituting (via `__smtx_*_substitute`)
some of the free type references of `U` whose names are tracked by `refs`: a `TypeRef x` leaf
is either untouched or (when `x ∈ refs`) replaced by a full `Datatype x …`; a `Datatype` node
keeps its name with an image body; all other nodes are untouched. This is the invariant the
two-argument `__smtx_*_wf_rec` recursion maintains between its full (first) and unfolded
(second) arguments: it starts on the diagonal (`img*_refl`) and self-substitutes at each
`Datatype` node (`img*_subst`). -/
mutual
def imgTy (refs : RefList) (F : SmtType) : SmtType → Prop
  | SmtType.TypeRef x =>
      F = SmtType.TypeRef x ∨
        (native_reflist_contains refs x = true ∧ ∃ e, F = SmtType.Datatype x e)
  | SmtType.Datatype s dU => ∃ dF, F = SmtType.Datatype s dF ∧ imgDt refs dF dU
  | U => F = U
def imgDt (refs : RefList) (F : SmtDatatype) : SmtDatatype → Prop
  | SmtDatatype.sum cU dU =>
      ∃ cF dF, F = SmtDatatype.sum cF dF ∧ imgDtc refs cF cU ∧ imgDt refs dF dU
  | SmtDatatype.null => F = SmtDatatype.null
def imgDtc (refs : RefList) (F : SmtDatatypeCons) : SmtDatatypeCons → Prop
  | SmtDatatypeCons.cons TU cU =>
      ∃ TF cF, F = SmtDatatypeCons.cons TF cF ∧ imgTy refs TF TU ∧ imgDtc refs cF cU
  | SmtDatatypeCons.unit => F = SmtDatatypeCons.unit
end

mutual
theorem imgTy_refl (refs : RefList) : (T : SmtType) → imgTy refs T T
  | SmtType.TypeRef x => Or.inl rfl
  | SmtType.Datatype s d => ⟨d, rfl, imgDt_refl refs d⟩
  | SmtType.Bool => rfl
  | SmtType.Int => rfl
  | SmtType.Real => rfl
  | SmtType.BitVec n => rfl
  | SmtType.Char => rfl
  | SmtType.USort n => rfl
  | SmtType.Seq x => rfl
  | SmtType.Set x => rfl
  | SmtType.Map x y => rfl
  | SmtType.FunType x y => rfl
  | SmtType.DtcAppType x y => rfl
  | SmtType.None => rfl
  | SmtType.RegLan => rfl
theorem imgDt_refl (refs : RefList) : (d : SmtDatatype) → imgDt refs d d
  | SmtDatatype.null => rfl
  | SmtDatatype.sum c d => ⟨c, d, rfl, imgDtc_refl refs c, imgDt_refl refs d⟩
theorem imgDtc_refl (refs : RefList) : (c : SmtDatatypeCons) → imgDtc refs c c
  | SmtDatatypeCons.unit => rfl
  | SmtDatatypeCons.cons T c => ⟨T, c, rfl, imgTy_refl refs T, imgDtc_refl refs c⟩
end

mutual
theorem imgTy_weaken {refs refs' : RefList}
    (hsub : ∀ x, native_reflist_contains refs x = true →
      native_reflist_contains refs' x = true) :
    (U : SmtType) → (F : SmtType) → imgTy refs F U → imgTy refs' F U
  | SmtType.TypeRef x, F, h => by
      rcases h with hTF | ⟨hMem, e, hTF⟩
      · exact Or.inl hTF
      · exact Or.inr ⟨hsub x hMem, e, hTF⟩
  | SmtType.Datatype s dU, F, h => by
      rcases h with ⟨dF, hTF, hD⟩
      exact ⟨dF, hTF, imgDt_weaken hsub dU dF hD⟩
  | SmtType.Bool, F, h => h
  | SmtType.Int, F, h => h
  | SmtType.Real, F, h => h
  | SmtType.BitVec n, F, h => h
  | SmtType.Char, F, h => h
  | SmtType.USort n, F, h => h
  | SmtType.Seq x, F, h => h
  | SmtType.Set x, F, h => h
  | SmtType.Map x y, F, h => h
  | SmtType.FunType x y, F, h => h
  | SmtType.DtcAppType x y, F, h => h
  | SmtType.None, F, h => h
  | SmtType.RegLan, F, h => h
theorem imgDt_weaken {refs refs' : RefList}
    (hsub : ∀ x, native_reflist_contains refs x = true →
      native_reflist_contains refs' x = true) :
    (dU : SmtDatatype) → (dF : SmtDatatype) → imgDt refs dF dU → imgDt refs' dF dU
  | SmtDatatype.null, dF, h => h
  | SmtDatatype.sum cU dU, dF, h => by
      rcases h with ⟨cF, dF', hEq, hC, hD⟩
      exact ⟨cF, dF', hEq, imgDtc_weaken hsub cU cF hC, imgDt_weaken hsub dU dF' hD⟩
theorem imgDtc_weaken {refs refs' : RefList}
    (hsub : ∀ x, native_reflist_contains refs x = true →
      native_reflist_contains refs' x = true) :
    (cU : SmtDatatypeCons) → (cF : SmtDatatypeCons) → imgDtc refs cF cU → imgDtc refs' cF cU
  | SmtDatatypeCons.unit, cF, h => h
  | SmtDatatypeCons.cons TU cU, cF, h => by
      rcases h with ⟨TF, cF', hEq, hT, hC⟩
      exact ⟨TF, cF', hEq, imgTy_weaken hsub TU TF hT, imgDtc_weaken hsub cU cF' hC⟩
end

private theorem contains_insert_of_contains {refs : RefList} {x : native_String}
    (s : native_String) (h : native_reflist_contains refs x = true) :
    native_reflist_contains (native_reflist_insert refs s) x = true := by
  simp [native_reflist_contains, native_reflist_insert] at h ⊢
  exact Or.inr h

mutual
theorem imgTy_subst (s : native_String) (δ : SmtDatatype) {refs : RefList} :
    (U : SmtType) → (F : SmtType) → imgTy refs F U →
      imgTy (native_reflist_insert refs s) (__smtx_type_substitute s δ F) U
  | SmtType.TypeRef x, F, h => by
      rcases h with rfl | ⟨hMem, e, rfl⟩
      · by_cases hxs : s = x
        · subst hxs
          refine Or.inr ⟨by simp [native_reflist_contains, native_reflist_insert], δ, ?_⟩
          simp [__smtx_type_substitute, native_ite, native_streq]
        · have hst : native_streq s x = false := by simp [native_streq, hxs]
          exact Or.inl (by simp [__smtx_type_substitute, native_ite, hst])
      · exact Or.inr ⟨contains_insert_of_contains s hMem,
          native_ite (native_streq s x) e
            (__smtx_dt_substitute s (__smtx_dt_lift x e δ) e), rfl⟩
  | SmtType.Datatype s2 dU, F, h => by
      rcases h with ⟨dF, rfl, hD⟩
      by_cases hs : s = s2
      · subst hs
        refine ⟨dF, by simp [__smtx_type_substitute, native_ite, native_streq], ?_⟩
        exact imgDt_weaken (fun x hx => contains_insert_of_contains s hx) dU dF hD
      · have hst : native_streq s s2 = false := by simp [native_streq, hs]
        exact ⟨__smtx_dt_substitute s (__smtx_dt_lift s2 dF δ) dF,
          by simp [__smtx_type_substitute, native_ite, hst],
          imgDt_subst s (__smtx_dt_lift s2 dF δ) dU dF hD⟩
  | SmtType.Bool, F, h => by cases h; rfl
  | SmtType.Int, F, h => by cases h; rfl
  | SmtType.Real, F, h => by cases h; rfl
  | SmtType.BitVec n, F, h => by cases h; rfl
  | SmtType.Char, F, h => by cases h; rfl
  | SmtType.USort n, F, h => by cases h; rfl
  | SmtType.Seq x, F, h => by cases h; rfl
  | SmtType.Set x, F, h => by cases h; rfl
  | SmtType.Map x y, F, h => by cases h; rfl
  | SmtType.FunType x y, F, h => by cases h; rfl
  | SmtType.DtcAppType x y, F, h => by cases h; rfl
  | SmtType.None, F, h => by cases h; rfl
  | SmtType.RegLan, F, h => by cases h; rfl
theorem imgDt_subst (s : native_String) (δ : SmtDatatype) {refs : RefList} :
    (dU : SmtDatatype) → (dF : SmtDatatype) → imgDt refs dF dU →
      imgDt (native_reflist_insert refs s) (__smtx_dt_substitute s δ dF) dU
  | SmtDatatype.null, dF, h => by cases h; rfl
  | SmtDatatype.sum cU dU, dF, h => by
      rcases h with ⟨cF, dF', rfl, hC, hD⟩
      exact ⟨__smtx_dtc_substitute s δ cF, __smtx_dt_substitute s δ dF',
        by simp [__smtx_dt_substitute],
        imgDtc_subst s δ cU cF hC, imgDt_subst s δ dU dF' hD⟩
theorem imgDtc_subst (s : native_String) (δ : SmtDatatype) {refs : RefList} :
    (cU : SmtDatatypeCons) → (cF : SmtDatatypeCons) → imgDtc refs cF cU →
      imgDtc (native_reflist_insert refs s) (__smtx_dtc_substitute s δ cF) cU
  | SmtDatatypeCons.unit, cF, h => by cases h; rfl
  | SmtDatatypeCons.cons TU cU, cF, h => by
      rcases h with ⟨TF, cF', rfl, hT, hC⟩
      exact ⟨__smtx_type_substitute s δ TF, __smtx_dtc_substitute s δ cF',
        by simp [__smtx_dtc_substitute],
        imgTy_subst s δ TU TF hT, imgDtc_subst s δ cU cF' hC⟩
end

/-- Splits a generic (non-skip) constructor-field step of `__smtx_dt_cons_wf_rec`. -/
private theorem dt_cons_wf_rec_parts
    {TF TU : SmtType} {cF cU : SmtDatatypeCons}
    (hNotSpecial : ¬ ∃ sF dF r, TF = SmtType.Datatype sF dF ∧ TU = SmtType.TypeRef r)
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF)
        (SmtDatatypeCons.cons TU cU) = true) :
    __smtx_type_wf_rec TF TU = true ∧ __smtx_dt_cons_wf_rec cF cU = true := by
  cases TF <;> cases TU <;>
    simp [__smtx_dt_cons_wf_rec, native_ite, native_and] at h hNotSpecial ⊢
  all_goals
    first
    | exact h
    | exact ⟨h.1.2, h.2⟩
    | exact ⟨h.2.1, h.2.2⟩
    | contradiction

/-- Reduces `hasFreeDtc` on a non-`TypeRef` head field. -/
private theorem hasFreeDtc_cons_generic
    (sub : native_String) (refs : RefList) {T : SmtType} (c : SmtDatatypeCons)
    (hT : ∀ x, T ≠ SmtType.TypeRef x) :
    hasFreeDtc sub refs (SmtDatatypeCons.cons T c) =
      native_or (hasFreeTy sub refs T) (hasFreeDtc sub refs c) := by
  cases T with
  | TypeRef x => exact absurd rfl (hT x)
  | _ => simp [hasFreeDtc]

/-! ### Well-formedness excludes free type references

The new-algorithm replacement for the deleted reflist-scoped
`hasFree*_eq_false_of_wf`: a type that is well-formed against a substitution image of
itself (`imgTy`) has no type reference free over the image scope. Every `TypeRef` accepted
by the wf recursion is accepted through the skip case, whose image invariant certifies the
referenced name is in scope. -/
mutual
theorem hasFreeTy_eq_false_of_wf_img (sub : native_String) :
    (U : SmtType) → (F : SmtType) → (refs : RefList) →
      imgTy refs F U → __smtx_type_wf_rec F U = true →
      hasFreeTy sub refs U = false
  | SmtType.Datatype s dU, F, refs, hImg, hWf => by
      rcases hImg with ⟨dF, rfl, hD⟩
      have hWf' : __smtx_dt_wf_rec (__smtx_dt_substitute s dF dF) dU = true := by
        simpa [__smtx_type_wf_rec] using hWf
      have hImg' : imgDt (native_reflist_insert refs s)
          (__smtx_dt_substitute s dF dF) dU :=
        imgDt_subst s dF dU dF hD
      simp only [hasFreeTy]
      exact hasFreeDt_eq_false_of_wf_img sub dU _ _ hImg' hWf'
  | SmtType.Seq x, F, refs, hImg, hWf => by
      cases hImg
      have hx : __smtx_type_wf_rec x x = true := by
        simp only [__smtx_type_wf_rec, native_and, Bool.and_eq_true] at hWf
        exact hWf.1.2
      simp only [hasFreeTy]
      exact hasFreeTy_eq_false_of_wf_img sub x x native_reflist_nil (imgTy_refl _ x) hx
  | SmtType.Set x, F, refs, hImg, hWf => by
      cases hImg
      have hx : __smtx_type_wf_rec x x = true := by
        simp only [__smtx_type_wf_rec, native_and, Bool.and_eq_true] at hWf
        exact hWf.1.2
      simp only [hasFreeTy]
      exact hasFreeTy_eq_false_of_wf_img sub x x native_reflist_nil (imgTy_refl _ x) hx
  | SmtType.Map x y, F, refs, hImg, hWf => by
      cases hImg
      have hParts : __smtx_type_wf_rec x x = true ∧ __smtx_type_wf_rec y y = true := by
        simp only [__smtx_type_wf_rec, native_and, Bool.and_eq_true] at hWf
        exact ⟨hWf.1.1.2, hWf.2.1.2⟩
      simp only [hasFreeTy, native_or, Bool.or_eq_false_iff]
      exact ⟨hasFreeTy_eq_false_of_wf_img sub x x native_reflist_nil (imgTy_refl _ x)
          hParts.1,
        hasFreeTy_eq_false_of_wf_img sub y y native_reflist_nil (imgTy_refl _ y)
          hParts.2⟩
  | SmtType.TypeRef x, F, refs, hImg, hWf => by simp [hasFreeTy]
  | SmtType.Bool, F, refs, hImg, hWf => by simp [hasFreeTy]
  | SmtType.Int, F, refs, hImg, hWf => by simp [hasFreeTy]
  | SmtType.Real, F, refs, hImg, hWf => by simp [hasFreeTy]
  | SmtType.BitVec n, F, refs, hImg, hWf => by simp [hasFreeTy]
  | SmtType.Char, F, refs, hImg, hWf => by simp [hasFreeTy]
  | SmtType.USort n, F, refs, hImg, hWf => by simp [hasFreeTy]
  | SmtType.FunType x y, F, refs, hImg, hWf => by simp [hasFreeTy]
  | SmtType.DtcAppType x y, F, refs, hImg, hWf => by simp [hasFreeTy]
  | SmtType.None, F, refs, hImg, hWf => by simp [hasFreeTy]
  | SmtType.RegLan, F, refs, hImg, hWf => by simp [hasFreeTy]

theorem hasFreeDt_eq_false_of_wf_img (sub : native_String) :
    (dU : SmtDatatype) → (dF : SmtDatatype) → (refs : RefList) →
      imgDt refs dF dU → __smtx_dt_wf_rec dF dU = true →
      hasFreeDt sub refs dU = false
  | SmtDatatype.null, dF, refs, hImg, hWf => by simp [hasFreeDt]
  | SmtDatatype.sum cU dU, dF, refs, hImg, hWf => by
      rcases hImg with ⟨cF, dF', rfl, hC, hD⟩
      have hParts :
          __smtx_dt_cons_wf_rec cF cU = true ∧ __smtx_dt_wf_rec dF' dU = true := by
        simp only [__smtx_dt_wf_rec, native_ite] at hWf
        cases hc : __smtx_dt_cons_wf_rec cF cU <;> simp [hc] at hWf ⊢
        exact hWf
      simp only [hasFreeDt, native_or, Bool.or_eq_false_iff]
      exact ⟨hasFreeDtc_eq_false_of_wf_img sub cU cF refs hC hParts.1,
        hasFreeDt_eq_false_of_wf_img sub dU dF' refs hD hParts.2⟩

theorem hasFreeDtc_eq_false_of_wf_img (sub : native_String) :
    (cU : SmtDatatypeCons) → (cF : SmtDatatypeCons) → (refs : RefList) →
      imgDtc refs cF cU → __smtx_dt_cons_wf_rec cF cU = true →
      hasFreeDtc sub refs cU = false
  | SmtDatatypeCons.unit, cF, refs, hImg, hWf => by simp [hasFreeDtc]
  | SmtDatatypeCons.cons TU cU, cF, refs, hImg, hWf => by
      rcases hImg with ⟨TF, cF', rfl, hT, hC⟩
      by_cases hRef : ∃ x, TU = SmtType.TypeRef x
      · rcases hRef with ⟨x, rfl⟩
        rcases hT with rfl | ⟨hMem, e, rfl⟩
        · exfalso
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, native_and] at hWf
        · have hTail : __smtx_dt_cons_wf_rec cF' cU = true := by
            simpa [__smtx_dt_cons_wf_rec] using hWf
          have hbit : native_and (native_streq x sub)
              (native_not (native_reflist_contains refs sub)) = false := by
            by_cases hxs : x = sub
            · subst hxs
              simp [native_and, native_not, hMem]
            · simp [native_and, native_streq, hxs]
          simp only [hasFreeDtc, native_or, Bool.or_eq_false_iff]
          exact ⟨by simpa using hbit,
            hasFreeDtc_eq_false_of_wf_img sub cU cF' refs hC hTail⟩
      · have hNS : ¬ ∃ sF dF r, TF = SmtType.Datatype sF dF ∧ TU = SmtType.TypeRef r := by
          rintro ⟨sF, dF, r, -, hTU⟩
          exact hRef ⟨r, hTU⟩
        have hParts := dt_cons_wf_rec_parts hNS hWf
        rw [hasFreeDtc_cons_generic sub refs cU (fun x hx => hRef ⟨x, hx⟩)]
        simp only [native_or, Bool.or_eq_false_iff]
        exact ⟨hasFreeTy_eq_false_of_wf_img sub TU TF refs hT hParts.1,
          hasFreeDtc_eq_false_of_wf_img sub cU cF' refs hC hParts.2⟩
end

/-- Diagonal corollary: a diagonally well-formed type has no free type references at all. -/
theorem hasFreeTy_eq_false_of_wf (sub : native_String) (T : SmtType)
    (hWf : __smtx_type_wf_rec T T = true) :
    hasFreeTy sub native_reflist_nil T = false :=
  hasFreeTy_eq_false_of_wf_img sub T T native_reflist_nil (imgTy_refl _ T) hWf

/- One-sided version of `lift_noop_no_dt_*` for the case where the ambient fact is
well-formedness plus `noStray` consistency rather than a bare `noDt` fact for the fold
name `s` itself. `noStray s D W` reduces every `Datatype s …` node reachable in `W` to the
exact fold target `Datatype s D`; `noDt sub W` (about a *different*, outer name `sub`) plus
`hFree` (the fold target `D` genuinely references `sub` freely) then rule out those exact
copies: any such copy of `D` would carry a `TypeRef sub` free over the enclosing scope (no
binder is named `sub`, by `noDt`), which well-formedness excludes
(`hasFree*_eq_false_of_wf_img`). Hence nothing `s`-named survives at a lift-reachable
position and the (name-keyed) lift is a no-op. The `dt`/`dtc` levels take the paired
(full/unfolded) wf form together with its substitution-image invariant — that is what the
wf recursion actually provides under a `Datatype` binder; the `ty` level keeps its diagonal
signature. -/
mutual
theorem lift_noop_of_wf_no_dt_dt (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (W : SmtDatatype) → (F : SmtDatatype) → (refs : RefList) →
      imgDt refs F W → __smtx_dt_wf_rec F W = true → noDtDt sub W = true →
      noStrayDt s D W = true →
      native_reflist_contains refs sub = false →
      __smtx_dt_lift s D W = W
  | SmtDatatype.null, F, refs, hImg, hWf, hNoDt, hStray, hSub => by simp [__smtx_dt_lift]
  | SmtDatatype.sum cU dU, F, refs, hImg, hWf, hNoDt, hStray, hSub => by
      rcases hImg with ⟨cF, dF, rfl, hC, hD⟩
      have hParts :
          __smtx_dt_cons_wf_rec cF cU = true ∧ __smtx_dt_wf_rec dF dU = true := by
        simp only [__smtx_dt_wf_rec, native_ite] at hWf
        cases hc : __smtx_dt_cons_wf_rec cF cU <;> simp [hc] at hWf ⊢
        exact hWf
      have hNoDtParts : noDtDtc sub cU = true ∧ noDtDt sub dU = true := by
        simpa [noDtDt, native_and, Bool.and_eq_true] using hNoDt
      have hStrayParts : noStrayDtc s D cU = true ∧ noStrayDt s D dU = true := by
        simpa [noStrayDt, native_and, Bool.and_eq_true] using hStray
      simp only [__smtx_dt_lift]
      rw [lift_noop_of_wf_no_dt_dtc s sub D hsne hFree cU cF refs hC hParts.1
          hNoDtParts.1 hStrayParts.1 hSub,
        lift_noop_of_wf_no_dt_dt s sub D hsne hFree dU dF refs hD hParts.2
          hNoDtParts.2 hStrayParts.2 hSub]

theorem lift_noop_of_wf_no_dt_dtc (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (c : SmtDatatypeCons) → (F : SmtDatatypeCons) → (refs : RefList) →
      imgDtc refs F c → __smtx_dt_cons_wf_rec F c = true → noDtDtc sub c = true →
      noStrayDtc s D c = true →
      native_reflist_contains refs sub = false →
      __smtx_dtc_lift s D c = c
  | SmtDatatypeCons.unit, F, refs, hImg, hWf, hNoDt, hStray, hSub => by simp [__smtx_dtc_lift]
  | SmtDatatypeCons.cons TU cU, F, refs, hImg, hWf, hNoDt, hStray, hSub => by
      rcases hImg with ⟨TF, cF, rfl, hT, hC⟩
      have hNoDtParts : noDtTy sub TU = true ∧ noDtDtc sub cU = true := by
        simpa [noDtDtc, native_and, Bool.and_eq_true] using hNoDt
      have hStrayParts : noStrayTy s D TU = true ∧ noStrayDtc s D cU = true := by
        simpa [noStrayDtc, native_and, Bool.and_eq_true] using hStray
      by_cases hRefU : ∃ x, TU = SmtType.TypeRef x
      · rcases hRefU with ⟨x, rfl⟩
        rcases hT with rfl | ⟨hMem, e, rfl⟩
        · exfalso
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, native_and] at hWf
        · have hTail : __smtx_dt_cons_wf_rec cF cU = true := by
            simpa [__smtx_dt_cons_wf_rec] using hWf
          simp only [__smtx_dtc_lift, __smtx_type_lift]
          rw [lift_noop_of_wf_no_dt_dtc s sub D hsne hFree cU cF refs hC hTail
            hNoDtParts.2 hStrayParts.2 hSub]
      · have hNS : ¬ ∃ sF dF r, TF = SmtType.Datatype sF dF ∧ TU = SmtType.TypeRef r := by
          rintro ⟨sF, dF, r, -, hTU⟩
          exact hRefU ⟨r, hTU⟩
        have hParts := dt_cons_wf_rec_parts hNS hWf
        have hTailEq :=
          lift_noop_of_wf_no_dt_dtc s sub D hsne hFree cU cF refs hC hParts.2
            hNoDtParts.2 hStrayParts.2 hSub
        simp only [__smtx_dtc_lift]
        rw [hTailEq]
        cases TU with
        | Datatype s2 d2 =>
            rcases hT with ⟨dF2, rfl, hD2⟩
            have hs2sub : native_streq s2 sub = false ∧ noDtDt sub d2 = true := by
              have h0 := hNoDtParts.1
              simp only [noDtTy, native_and, native_not, Bool.and_eq_true] at h0
              cases hst : native_streq s2 sub
              · exact ⟨rfl, by simpa [hst] using h0⟩
              · simp [hst] at h0
            have hs2ne : s2 ≠ sub := by
              intro he
              subst he
              simp [native_streq] at hs2sub
            have hDt2 :
                __smtx_dt_wf_rec (__smtx_dt_substitute s2 dF2 dF2) d2 = true := by
              simpa [__smtx_type_wf_rec] using hParts.1
            have hImg2 : imgDt (native_reflist_insert refs s2)
                (__smtx_dt_substitute s2 dF2 dF2) d2 :=
              imgDt_subst s2 dF2 d2 dF2 hD2
            have hSub2 :
                native_reflist_contains (native_reflist_insert refs s2) sub = false := by
              simp [native_reflist_contains, native_reflist_insert] at hSub ⊢
              exact ⟨fun he => hs2ne he.symm, hSub⟩
            -- the exact fold target cannot occur (it would carry a free `sub` reference)
            have hNotFold :
                native_Teq (SmtType.Datatype s D) (SmtType.Datatype s2 d2) = false := by
              cases hFold : native_Teq (SmtType.Datatype s D) (SmtType.Datatype s2 d2)
              · rfl
              · exfalso
                obtain ⟨hs', hd'⟩ : s = s2 ∧ D = d2 := by simpa [native_Teq] using hFold
                subst hs'
                subst hd'
                have hNoFree : hasFreeDt sub (native_reflist_insert refs s) D = false :=
                  hasFreeDt_eq_false_of_wf_img sub D _ _ hImg2 hDt2
                have hFree' : hasFreeDt sub (native_reflist_insert refs s) D = true := by
                  rw [hasFreeDt_refs_irrel sub D _ (native_reflist_insert native_reflist_nil s)
                    (by
                      rw [hSub2]
                      have : native_reflist_contains
                          (native_reflist_insert native_reflist_nil s) sub = false := by
                        simp [native_reflist_contains, native_reflist_insert,
                          native_reflist_nil]
                        exact fun he => hsne he
                      rw [this])]
                  exact hFree
                rw [hFree'] at hNoFree
                cases hNoFree
            -- name-keyed lift: the name cannot match either, by `noStray`
            have hStray' : native_not (native_streq s2 s) = true ∧
                noStrayDt s D d2 = true := by
              have hStrayT := hStrayParts.1
              simp only [noStrayTy, native_ite, hNotFold] at hStrayT
              rw [if_neg (by simp)] at hStrayT
              simpa [native_and, Bool.and_eq_true] using hStrayT
            have hNotName : native_streq s s2 = false := by
              have h21 : native_streq s2 s = false := by
                have h0 := hStray'.1
                cases h : native_streq s2 s
                · rfl
                · rw [h] at h0
                  simp [native_not] at h0
              cases h : native_streq s s2
              · rfl
              · exfalso
                have hEq : s = s2 := by simpa [native_streq] using h
                subst hEq
                simp [native_streq] at h21
            have hStrayD2 : noStrayDt s D d2 = true := hStray'.2
            simp only [__smtx_type_lift, native_ite]
            rw [if_neg (by simp [hNotName])]
            congr 2
            exact lift_noop_of_wf_no_dt_dt s sub D hsne hFree d2 _ _ hImg2 hDt2
              hs2sub.2 hStrayD2 hSub2
        | TypeRef x => exact absurd ⟨x, rfl⟩ hRefU
        | Bool => simp [__smtx_type_lift]
        | Int => simp [__smtx_type_lift]
        | Real => simp [__smtx_type_lift]
        | BitVec n => simp [__smtx_type_lift]
        | Char => simp [__smtx_type_lift]
        | USort n => simp [__smtx_type_lift]
        | Seq x => simp [__smtx_type_lift]
        | Set x => simp [__smtx_type_lift]
        | Map x y => simp [__smtx_type_lift]
        | FunType x y => simp [__smtx_type_lift]
        | DtcAppType x y => simp [__smtx_type_lift]
        | None => simp [__smtx_type_lift]
        | RegLan => simp [__smtx_type_lift]
end

theorem lift_noop_of_wf_no_dt_ty (s sub : native_String) (D : SmtDatatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = true) :
    (T : SmtType) → __smtx_type_wf_rec T T = true → noDtTy sub T = true →
      noStrayTy s D T = true →
      __smtx_type_lift s D T = T
  | SmtType.Datatype s2 d2, hWf, hNoDt, hStray => by
      have hs2sub : native_streq s2 sub = false ∧ noDtDt sub d2 = true := by
        simp only [noDtTy, native_and, native_not, Bool.and_eq_true] at hNoDt
        cases hst : native_streq s2 sub
        · exact ⟨rfl, by simpa [hst] using hNoDt⟩
        · simp [hst] at hNoDt
      have hs2ne : s2 ≠ sub := by
        intro he
        subst he
        simp [native_streq] at hs2sub
      have hDt : __smtx_dt_wf_rec (__smtx_dt_substitute s2 d2 d2) d2 = true := by
        simpa [__smtx_type_wf_rec] using hWf
      have hImg : imgDt (native_reflist_insert native_reflist_nil s2)
          (__smtx_dt_substitute s2 d2 d2) d2 :=
        imgDt_subst s2 d2 d2 d2 (imgDt_refl _ d2)
      have hSub2 :
          native_reflist_contains
            (native_reflist_insert native_reflist_nil s2) sub = false := by
        simp [native_reflist_contains, native_reflist_insert, native_reflist_nil]
        exact fun he => hs2ne he.symm
      have hNotFold :
          native_Teq (SmtType.Datatype s D) (SmtType.Datatype s2 d2) = false := by
        cases hFold : native_Teq (SmtType.Datatype s D) (SmtType.Datatype s2 d2)
        · rfl
        · exfalso
          obtain ⟨hs', hd'⟩ : s = s2 ∧ D = d2 := by simpa [native_Teq] using hFold
          subst hs'
          subst hd'
          have hNoFree :
              hasFreeDt sub (native_reflist_insert native_reflist_nil s) D = false :=
            hasFreeDt_eq_false_of_wf_img sub D _ _ hImg hDt
          rw [hFree] at hNoFree
          cases hNoFree
      have hStray' : native_not (native_streq s2 s) = true ∧
          noStrayDt s D d2 = true := by
        simp only [noStrayTy, native_ite, hNotFold] at hStray
        rw [if_neg (by simp)] at hStray
        simpa [native_and, Bool.and_eq_true] using hStray
      have hNotName : native_streq s s2 = false := by
        have h21 : native_streq s2 s = false := by
          have h0 := hStray'.1
          cases h : native_streq s2 s
          · rfl
          · rw [h] at h0
            simp [native_not] at h0
        cases h : native_streq s s2
        · rfl
        · exfalso
          have hEq : s = s2 := by simpa [native_streq] using h
          subst hEq
          simp [native_streq] at h21
      have hStrayD2 : noStrayDt s D d2 = true := hStray'.2
      simp only [__smtx_type_lift, native_ite]
      rw [if_neg (by simp [hNotName])]
      rw [lift_noop_of_wf_no_dt_dt s sub D hsne hFree d2 _ _ hImg hDt hs2sub.2
        hStrayD2 hSub2]
  | SmtType.TypeRef x, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.Bool, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.Int, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.Real, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.BitVec n, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.Char, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.USort n, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.Seq x, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.Set x, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.Map x y, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.FunType x y, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.DtcAppType x y, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.None, _, _, _ => by simp [__smtx_type_lift]
  | SmtType.RegLan, _, _, _ => by simp [__smtx_type_lift]

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

/-! ### Scoped aliasing rejection implies `noDt` for every name in scope

The `__smtx_*_no_alias_rec` conjunct of the new well-formedness forbids any `Datatype x …`
node below an enclosing binder named `x`. In particular, once a name `s` is in scope, no
`Datatype s …` occurs at any reachable position — which is exactly `noDt s`. This is the
bridge that lets well-formedness feed the `noDt` side conditions of the lift machinery. -/
mutual
theorem noDtTy_of_no_alias (s : native_String) :
    (T : SmtType) → (refs : RefList) →
      native_reflist_contains refs s = true →
      __smtx_type_no_alias_rec refs T = true →
      noDtTy s T = true
  | SmtType.Datatype s2 d2, refs, hMem, h => by
      have hparts : native_reflist_contains refs s2 = false ∧
          __smtx_dt_no_alias_rec (native_reflist_insert refs s2) d2 = true := by
        cases hc : native_reflist_contains refs s2 <;>
          simp [__smtx_type_no_alias_rec, native_ite, hc] at h ⊢
        exact h
      have hne : s2 ≠ s := by
        intro he
        subst he
        rw [hMem] at hparts
        exact absurd hparts.1 (by simp)
      have hMem' : native_reflist_contains (native_reflist_insert refs s2) s = true := by
        simp only [native_reflist_contains, native_reflist_insert] at hMem ⊢
        simp only [List.mem_cons, decide_eq_true_eq] at hMem ⊢
        exact Or.inr hMem
      simp only [noDtTy, native_and, native_not, Bool.and_eq_true]
      exact ⟨by simp [native_streq, hne],
        noDtDt_of_no_alias s d2 (native_reflist_insert refs s2) hMem' hparts.2⟩
  | SmtType.TypeRef x, _, _, _ => by simp [noDtTy]
  | SmtType.Bool, _, _, _ => by simp [noDtTy]
  | SmtType.Int, _, _, _ => by simp [noDtTy]
  | SmtType.Real, _, _, _ => by simp [noDtTy]
  | SmtType.BitVec n, _, _, _ => by simp [noDtTy]
  | SmtType.Char, _, _, _ => by simp [noDtTy]
  | SmtType.USort n, _, _, _ => by simp [noDtTy]
  | SmtType.Seq x, _, _, _ => by simp [noDtTy]
  | SmtType.Set x, _, _, _ => by simp [noDtTy]
  | SmtType.Map x y, _, _, _ => by simp [noDtTy]
  | SmtType.FunType x y, _, _, _ => by simp [noDtTy]
  | SmtType.DtcAppType x y, _, _, _ => by simp [noDtTy]
  | SmtType.None, _, _, _ => by simp [noDtTy]
  | SmtType.RegLan, _, _, _ => by simp [noDtTy]

theorem noDtDt_of_no_alias (s : native_String) :
    (d : SmtDatatype) → (refs : RefList) →
      native_reflist_contains refs s = true →
      __smtx_dt_no_alias_rec refs d = true →
      noDtDt s d = true
  | SmtDatatype.null, _, _, _ => by simp [noDtDt]
  | SmtDatatype.sum c d, refs, hMem, h => by
      have hparts : __smtx_dt_cons_no_alias_rec refs c = true ∧
          __smtx_dt_no_alias_rec refs d = true := by
        cases hc : __smtx_dt_cons_no_alias_rec refs c <;>
          simp [__smtx_dt_no_alias_rec, native_ite, hc] at h ⊢
        exact h
      simp only [noDtDt, native_and, Bool.and_eq_true]
      exact ⟨noDtDtc_of_no_alias s c refs hMem hparts.1,
        noDtDt_of_no_alias s d refs hMem hparts.2⟩

theorem noDtDtc_of_no_alias (s : native_String) :
    (c : SmtDatatypeCons) → (refs : RefList) →
      native_reflist_contains refs s = true →
      __smtx_dt_cons_no_alias_rec refs c = true →
      noDtDtc s c = true
  | SmtDatatypeCons.unit, _, _, _ => by simp [noDtDtc]
  | SmtDatatypeCons.cons T c, refs, hMem, h => by
      have hparts : __smtx_type_no_alias_rec refs T = true ∧
          __smtx_dt_cons_no_alias_rec refs c = true := by
        cases hT : __smtx_type_no_alias_rec refs T <;>
          simp [__smtx_dt_cons_no_alias_rec, native_ite, hT] at h ⊢
        exact h
      simp only [noDtDtc, native_and, Bool.and_eq_true]
      exact ⟨noDtTy_of_no_alias s T refs hMem hparts.1,
        noDtDtc_of_no_alias s c refs hMem hparts.2⟩
end

end Smtm
