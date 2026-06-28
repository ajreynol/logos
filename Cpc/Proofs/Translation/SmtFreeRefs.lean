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

end Smtm
