import Cpc.SmtModel

/-!
# Well-formedness compatibility shim

The `dtMutual` well-formedness refactor merged the old `__smtx_dt_wf_rec : SmtDatatype → RefList →
Bool` (which meant "every constructor is well-formed in scope `refs`") into a four-argument
`__smtx_dt_wf_rec s refs haveBase d` that *also* tracks a reachable base constructor.

A large body of translation/canonical proofs were written against the old two-argument shape.
Rather than restate each of them, this module provides `dtAllWf`, a proof-side replica of the *old*
function (identical equations), together with the bridge `dtAllWf_of_dt_wf_rec` showing the new
`__smtx_dt_wf_rec` entails it.  Old proofs port by swapping `__smtx_dt_wf_rec` → `dtAllWf`, and the
points where `__smtx_type_wf_rec` is unfolded at a `Datatype` use `dtAllWf_of_type_wf_rec_datatype`.
-/

open SmtEval
namespace Smtm

/-- Proof-side replica of the pre-merge `__smtx_dt_wf_rec`: every constructor of `d` is well-formed
in scope `refs` (and `d` is non-empty). -/
def dtAllWf : SmtDatatype → RefList → native_Bool
  | SmtDatatype.null, _refs => false
  | (SmtDatatype.sum c SmtDatatype.null), refs => (__smtx_dt_cons_wf_rec c refs)
  | (SmtDatatype.sum c d), refs => (native_ite (__smtx_dt_cons_wf_rec c refs) (dtAllWf d refs) false)

/-- The new `__smtx_dt_wf_rec` implies the old all-constructors-well-formed predicate.  Generalised
over the `haveBase` accumulator: a `true` accumulator only "rescues" the empty tail. -/
theorem dtAllWf_of_dt_wf_rec_gen (s : native_String) (refs : RefList) :
    ∀ (d : SmtDatatype) (hb : native_Bool),
      __smtx_dt_wf_rec s refs hb d = true →
        (d = SmtDatatype.null ∧ hb = true) ∨ dtAllWf d (native_reflist_insert refs s) = true
  | SmtDatatype.null, hb, h => by
      left; exact ⟨rfl, by simpa [__smtx_dt_wf_rec] using h⟩
  | (SmtDatatype.sum c d), hb, h => by
      right
      simp only [__smtx_dt_wf_rec, native_and, Bool.and_eq_true] at h
      have hcons : __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true := h.1
      rcases dtAllWf_of_dt_wf_rec_gen s refs d _ h.2 with ⟨hnull, _⟩ | hrest
      · subst hnull; simpa [dtAllWf] using hcons
      · cases d with
        | null => simp [dtAllWf] at hrest
        | sum c2 d2 => simp [dtAllWf, native_ite, hcons, hrest]

theorem dtAllWf_of_dt_wf_rec (s : native_String) (refs : RefList) (d : SmtDatatype)
    (h : __smtx_dt_wf_rec s refs false d = true) :
    dtAllWf d (native_reflist_insert refs s) = true := by
  rcases dtAllWf_of_dt_wf_rec_gen s refs d false h with ⟨_, hb⟩ | hr
  · exact absurd hb (by simp)
  · exact hr

/-- Unfolding `__smtx_type_wf_rec` at a `Datatype`, in old-shape terms. -/
theorem dtAllWf_of_type_wf_rec_datatype (s : native_String) (d : SmtDatatype) (refs : RefList)
    (h : __smtx_type_wf_rec (SmtType.Datatype s d) refs = true) :
    native_reflist_contains refs s = false ∧ dtAllWf d (native_reflist_insert refs s) = true := by
  cases hc : native_reflist_contains refs s <;>
    simp [__smtx_type_wf_rec, native_ite, hc] at h ⊢
  exact dtAllWf_of_dt_wf_rec s refs d h

/-- Unfold `__smtx_type_wf_rec` at a `Datatype` to the raw (new) `__smtx_dt_wf_rec`. -/
theorem dt_wf_rec_of_type_wf_rec_datatype (s : native_String) (d : SmtDatatype) (refs : RefList)
    (h : __smtx_type_wf_rec (SmtType.Datatype s d) refs = true) :
    __smtx_dt_wf_rec s refs false d = true := by
  cases hc : native_reflist_contains refs s <;>
    simp [__smtx_type_wf_rec, native_ite, hc] at h ⊢
  exact h

/-- For a single-constructor datatype, well-formedness yields that its constructor is a *base*
(well-formed without the datatype's own name in scope). -/
theorem dt_cons_base_of_single (s : native_String) (C : SmtDatatypeCons) (refs : RefList)
    (h : __smtx_dt_wf_rec s refs false (SmtDatatype.sum C SmtDatatype.null) = true) :
    __smtx_dt_cons_wf_rec C refs = true := by
  simp only [__smtx_dt_wf_rec, native_or, native_and, Bool.and_eq_true, Bool.false_or] at h
  exact h.2

/-- Build well-formedness of a single-constructor datatype from its constructor being well-formed
(with the name in scope) and a base (well-formed without the name). -/
theorem type_wf_rec_datatype_single_of (s : native_String) (C : SmtDatatypeCons) (refs : RefList)
    (hContains : native_reflist_contains refs s = false)
    (hAll : __smtx_dt_cons_wf_rec C (native_reflist_insert refs s) = true)
    (hBase : __smtx_dt_cons_wf_rec C refs = true) :
    __smtx_type_wf_rec (SmtType.Datatype s (SmtDatatype.sum C SmtDatatype.null)) refs = true := by
  simp [__smtx_type_wf_rec, native_ite, hContains, __smtx_dt_wf_rec, native_and, native_or,
    hAll, hBase]

end Smtm
