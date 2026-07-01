import Cpc.Proofs.Translation.Base
import Cpc.Proofs.Translation.Datatypes
import Cpc.Proofs.Translation.Inversions
import Cpc.Proofs.Translation.SmtFreeRefs
import Cpc.Proofs.TypePreservation.BitVecPrep
import Cpc.Proofs.TypePreservation.Common
import Cpc.Proofs.TypePreservation.CoreArith
import Cpc.Proofs.TypePreservation.Datatypes
import Cpc.Proofs.TypePreservation.SeqStringRegex

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

attribute [local simp] native_streq native_and native_ite

/-!
These lemmas isolate EO-side `__eo_typeof` facts that are awkward to reduce
directly inside the translation proofs.

They let the main translation theorem make progress on the direct constructor
cases while we continue filling in the EO typing story separately.
-/

private theorem smtx_type_wf_rec_of_type_wf
    {T : SmtType}
    (hNotReg : T ≠ SmtType.RegLan)
    (hNotFun : ∀ A B : SmtType, T ≠ SmtType.FunType A B)
    (hNotIFun : ∀ A B : SmtType, T ≠ SmtType.FunType A B)
    (h : __smtx_type_wf T = true) :
    __smtx_type_wf_rec T T = true := by
  cases T <;>
    simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and] at h hNotReg ⊢
  case FunType A B =>
    exact False.elim (hNotFun A B rfl)
  all_goals first | exact h | exact h.2 | exact h.2.2

private theorem smtx_datatype_type_wf_rec_parts_local
    {s : native_String} {d : SmtDatatype} {refs : RefList}
    (h : __smtx_type_wf_rec (SmtType.Datatype s d) refs = true) :
    native_reflist_contains refs s = false ∧
      __smtx_dt_wf_rec d (native_reflist_insert refs s) = true := by
  cases hRefs : native_reflist_contains refs s <;>
    simp [__smtx_type_wf_rec, native_ite, hRefs] at h ⊢
  exact h

private theorem smtx_datatype_field_wf_rec_parts_local
    {s : native_String} {d : SmtDatatype} {refs : RefList}
    (h : smtx_type_field_wf_rec (SmtType.Datatype s d) refs) :
    native_reflist_contains refs s = false ∧
      __smtx_dt_wf_rec d (native_reflist_insert refs s) = true :=
  smtx_datatype_type_wf_rec_parts_local (by
    simpa [smtx_type_field_wf_rec] using h)

/-- Computes `__smtx_typeof_guard` under a non-`None` premise. -/
theorem smtx_typeof_guard_of_non_none
    (T U : SmtType) (h : T ≠ SmtType.None) :
    __smtx_typeof_guard T U = U := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq] at h ⊢

/-- Extracts well-formedness through a non-`None` guard. -/
theorem smtx_type_wf_guard_of_true
    (T U : SmtType)
    (h : __smtx_type_wf (__smtx_typeof_guard T U) = true) :
    __smtx_type_wf U = true := by
  cases T <;>
    simp [__smtx_typeof_guard, native_ite, native_Teq, __smtx_type_wf,
      __smtx_type_wf_component, native_and] at h ⊢
  case None =>
    exact False.elim (by
      simp [__smtx_type_wf_rec
        ] at h)
  all_goals
    exact h

/-- Extracts the element well-formedness from a guarded sequence type. -/
theorem smtx_type_wf_guarded_seq_component_of_true
    (T : SmtType)
    (h : __smtx_type_wf (__smtx_typeof_guard T (SmtType.Seq T)) = true) :
    __smtx_type_wf T = true :=
  seq_type_wf_component_of_wf (smtx_type_wf_guard_of_true T (SmtType.Seq T) h)

/-- Extracts the element well-formedness from a guarded set type. -/
theorem smtx_type_wf_guarded_set_component_of_true
    (T : SmtType)
    (h : __smtx_type_wf (__smtx_typeof_guard T (SmtType.Set T)) = true) :
    __smtx_type_wf T = true :=
  set_type_wf_component_of_wf (smtx_type_wf_guard_of_true T (SmtType.Set T) h)

/-- A translated EO type cannot be non-`None` if the EO term is `Stuck`. -/
theorem eo_term_ne_stuck_of_smt_type_non_none
    (T : Term) (h : __eo_to_smt_type T ≠ SmtType.None) :
    T ≠ Term.Stuck := by
  intro hStuck
  subst hStuck
  exact h rfl

/- Proof-side validity predicates for the EO type fragment meant to survive translation.

`eo_type_valid_rec` is the recursive/component predicate: it describes EO types
that may appear under datatype fields, function arguments, maps, sets, and tuple
extensions.  `RegLan` is intentionally not valid there, because SMT-LIB's
`__smtx_type_wf_rec` rejects it as a component even though `__smtx_type_wf`
accepts it as a top-level type.  The top-level wrapper `eo_type_valid` below is
the predicate to use for `__eo_typeof` results.
-/
mutual

def eo_type_valid_rec (refs : List native_String) : Term -> Prop
  | Term.Bool => True
  | Term.DatatypeType s d =>
      __eo_reserved_datatype_name s = false ∧ eo_datatype_valid_rec (s :: refs) d
  | Term.DatatypeTypeRef s => __eo_reserved_datatype_name s = false ∧ s ∈ refs
  | Term.DtcAppType T U => eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U
  | Term.USort _ => True
  | Term.Apply (Term.Apply Term.FunType T1) T2 =>
      eo_type_valid_rec [] T1 ∧ eo_type_valid_rec [] T2
  | Term.UOp UserOp.Int => True
  | Term.UOp UserOp.Real => True
  | Term.UOp UserOp.Char => True
  | Term.UOp UserOp.UnitTuple => True
  | Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) => native_zleq 0 n = true
  | Term.Apply (Term.UOp UserOp.Seq) T => eo_type_valid_rec [] T
  | Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U =>
      eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U
  | Term.Apply (Term.UOp UserOp.Set) T => eo_type_valid_rec [] T
  | Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U =>
      eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U ∧
        __smtx_type_wf (__eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U)) =
          true
  | _ => False

def eo_datatype_cons_valid_rec (refs : List native_String) : DatatypeCons -> Prop
  | DatatypeCons.unit => True
  | DatatypeCons.cons T c =>
      eo_type_valid_rec refs T ∧ eo_datatype_cons_valid_rec refs c

def eo_datatype_valid_rec (refs : List native_String) : Datatype -> Prop
  | Datatype.null => True
  | Datatype.sum c d =>
      eo_datatype_cons_valid_rec refs c ∧ eo_datatype_valid_rec refs d

end

def eo_type_valid : Term -> Prop
  | Term.UOp UserOp.RegLan => True
  | T => eo_type_valid_rec [] T

/-- Valid EO types always translate to a non-`None` SMT type. -/
theorem eo_type_valid_rec_non_none :
    ∀ {refs : List native_String} {T : Term},
      eo_type_valid_rec refs T -> __eo_to_smt_type T ≠ SmtType.None
  | refs, Term.UOp op, h => by
      cases op with
      | Int =>
          simp [__eo_to_smt_type]
      | Real =>
          simp [__eo_to_smt_type]
      | Char =>
          simp [__eo_to_smt_type]
      | UnitTuple =>
          simp [__eo_to_smt_type]
      | _ =>
          exfalso
          simp [eo_type_valid_rec] at h
  | refs, Term.Bool, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.USort i, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.DatatypeType s d, h => by
      rcases h with ⟨hReserved, _⟩
      simp [__eo_to_smt_type, hReserved, native_ite]
  | refs, Term.DatatypeTypeRef s, h => by
      rcases h with ⟨hReserved, _⟩
      simp [__eo_to_smt_type, hReserved, native_ite]
  | refs, Term.DtcAppType T U, h => by
      rcases h with ⟨hT, hU⟩
      have hTNN : __eo_to_smt_type T ≠ SmtType.None := eo_type_valid_rec_non_none hT
      have hUNN : __eo_to_smt_type U ≠ SmtType.None := eo_type_valid_rec_non_none hU
      simp [__eo_to_smt_type, hTNN, hUNN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply (Term.Apply Term.FunType T1) T2, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T1 ∧ eo_type_valid_rec [] T2) with ⟨hT1, hT2⟩
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None := eo_type_valid_rec_non_none hT1
      have hT2NN : __eo_to_smt_type T2 ≠ SmtType.None := eo_type_valid_rec_non_none hT2
      simp [eo_to_smt_type_fun, hT1NN, hT2NN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h => by
      have hz : native_zleq 0 n = true := by
        simpa [eo_type_valid_rec] using h
      simp [__eo_to_smt_type, native_ite, hz]
  | refs, Term.Apply (Term.UOp UserOp.Seq) T, h => by
      have hT : eo_type_valid_rec [] T := by
        simpa [eo_type_valid_rec] using h
      have hTNN : __eo_to_smt_type T ≠ SmtType.None := eo_type_valid_rec_non_none hT
      simp [__eo_to_smt_type, hTNN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply (Term.UOp UserOp.Set) T, h => by
      have hT : eo_type_valid_rec [] T := by
        simpa [eo_type_valid_rec] using h
      have hTNN : __eo_to_smt_type T ≠ SmtType.None := eo_type_valid_rec_non_none hT
      simp [__eo_to_smt_type, hTNN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U) with ⟨hT, hU⟩
      have hTNN : __eo_to_smt_type T ≠ SmtType.None := eo_type_valid_rec_non_none hT
      have hUNN : __eo_to_smt_type U ≠ SmtType.None := eo_type_valid_rec_non_none hU
      simp [__eo_to_smt_type, hTNN, hUNN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U ∧
          __smtx_type_wf (__eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U)) =
            true) with ⟨_hT, _hU, hWf⟩
      let raw := __eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U)
      have hRawNN : raw ≠ SmtType.None := by
        intro hNone
        have hWf' : __smtx_type_wf raw = true := by
          simpa [raw] using hWf
        simp [hNone, __smtx_type_wf, __smtx_type_wf_component,
          __smtx_type_wf_rec, native_and] at hWf'
      have hWfRaw : __smtx_type_wf raw = true := by
        simpa [raw] using hWf
      change native_ite (__smtx_type_wf raw) raw SmtType.None ≠ SmtType.None
      simp [native_ite, hWfRaw, hRawNN]
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
                  have hz : native_zleq 0 n = true := by
                    simpa [eo_type_valid_rec] using h
                  simp [__eo_to_smt_type, native_ite, hz]
              | _ =>
                  exfalso
                  simp [eo_type_valid_rec] at h
          | Seq =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using h
              have hXNN : __eo_to_smt_type x ≠ SmtType.None :=
                eo_type_valid_rec_non_none (refs := []) hx
              simp [__eo_to_smt_type, hXNN, __smtx_typeof_guard, native_ite, native_Teq]
          | Set =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using h
              have hXNN : __eo_to_smt_type x ≠ SmtType.None :=
                eo_type_valid_rec_non_none (refs := []) hx
              simp [__eo_to_smt_type, hXNN, __smtx_typeof_guard, native_ite, native_Teq]
          | _ =>
              exfalso
              simp [eo_type_valid_rec] at h
      | Apply g y =>
          cases g with
          | FunType =>
              rcases (by simpa [eo_type_valid_rec] using h :
                eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
              have hyNN : __eo_to_smt_type y ≠ SmtType.None := eo_type_valid_rec_non_none hy
              have hxNN : __eo_to_smt_type x ≠ SmtType.None := eo_type_valid_rec_non_none hx
              simp [eo_to_smt_type_fun, hyNN, hxNN, __smtx_typeof_guard, native_ite, native_Teq]
          | UOp op =>
              cases op with
              | Array =>
                  rcases (by simpa [eo_type_valid_rec] using h :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
                  have hyNN : __eo_to_smt_type y ≠ SmtType.None := eo_type_valid_rec_non_none hy
                  have hxNN : __eo_to_smt_type x ≠ SmtType.None := eo_type_valid_rec_non_none hx
                  simp [__eo_to_smt_type, hyNN, hxNN, __smtx_typeof_guard,
                    native_ite, native_Teq]
              | Tuple =>
                  rcases (by simpa [eo_type_valid_rec] using h :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x ∧
                      __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) =
                        true) with ⟨_hy, _hx, hWf⟩
                  let raw := __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)
                  have hRawNN : raw ≠ SmtType.None := by
                    intro hNone
                    have hWf' : __smtx_type_wf raw = true := by
                      simpa [raw] using hWf
                    simp [hNone, __smtx_type_wf, __smtx_type_wf_component,
                      __smtx_type_wf_rec, native_and] at hWf'
                  have hWfRaw : __smtx_type_wf raw = true := by
                    simpa [raw] using hWf
                  change native_ite (__smtx_type_wf raw) raw SmtType.None ≠ SmtType.None
                  simp [native_ite, hWfRaw, hRawNN]
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

/-- Top-level valid EO types always translate to a non-`None` SMT type. -/
theorem eo_type_valid_non_none {T : Term} :
    eo_type_valid T -> __eo_to_smt_type T ≠ SmtType.None := by
  cases T with
  | UOp op =>
      cases op with
      | RegLan =>
          intro _
          simp [__eo_to_smt_type]
      | _ =>
          intro h
          exact eo_type_valid_rec_non_none (refs := []) (T := Term.UOp _) h
  | _ =>
      intro h
      exact eo_type_valid_rec_non_none (refs := []) h

theorem eo_type_valid_rec_not_stuck
    {refs : RefList} {T : Term}
    (h : eo_type_valid_rec refs T) :
    T ≠ Term.Stuck := by
  intro hStuck
  subst hStuck
  simp [eo_type_valid_rec] at h

theorem eo_type_valid_not_stuck
    {T : Term}
    (h : eo_type_valid T) :
    T ≠ Term.Stuck := by
  cases T with
  | UOp op =>
      intro hStuck
      cases hStuck
  | _ =>
      exact eo_type_valid_rec_not_stuck (refs := []) (by
        simpa [eo_type_valid] using h)

/- On valid EO types, `__eo_to_smt_type` is injective. -/
mutual

private theorem eo_to_smt_type_unique_of_valid_rec_apply
    (refs : List native_String) :
    ∀ {T U : Term},
      eo_type_valid_rec refs T ->
      __eo_to_smt_type T = __eo_to_smt_type U ->
      T = U
  | Term.UOp op, U, hValid, hEq => by
      cases op with
      | Int =>
          have hU : __eo_to_smt_type U = SmtType.Int := by
            simpa using hEq.symm
          exact (eo_to_smt_type_eq_int hU).symm
      | Real =>
          have hU : __eo_to_smt_type U = SmtType.Real := by
            simpa using hEq.symm
          exact (eo_to_smt_type_eq_real hU).symm
      | Char =>
          have hU : __eo_to_smt_type U = SmtType.Char := by
            simpa using hEq.symm
          exact (eo_to_smt_type_eq_char hU).symm
      | UnitTuple =>
          let tupleTy :=
            SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
          have hField :
              smtx_type_field_wf_rec
                (__eo_to_smt_type (Term.UOp UserOp.UnitTuple)) native_reflist_nil := by
            change smtx_type_field_wf_rec tupleTy native_reflist_nil
            have hInh : native_inhabited_type tupleTy = true := by
              classical
              simp [tupleTy, native_inhabited_type, native_and, native_ite, native_not,
                native_veq, native_Teq, __smtx_type_default, __smtx_type_default_rec,
                __smtx_datatype_default,
                __smtx_datatype_cons_default, __smtx_typeof_value,
                __smtx_typeof_dt_cons_value_rec, __smtx_dt_substitute,
                __smtx_dtc_substitute]
            have hRec : __smtx_type_wf_rec tupleTy tupleTy = true := by
              simp [tupleTy, __smtx_type_wf_rec,
                __smtx_dt_wf_rec, __smtx_dt_cons_wf_rec, native_reflist_contains,
                native_reflist_nil, native_ite]
            simpa [smtx_type_field_wf_rec, tupleTy] using hRec
          exact
            eo_to_smt_type_injective_of_field_wf_rec
              (T := Term.UOp UserOp.UnitTuple) (U := U)
              (A := __eo_to_smt_type (Term.UOp UserOp.UnitTuple))
              (refs := native_reflist_nil) rfl hEq.symm hField
      | _ =>
          simp [eo_type_valid_rec] at hValid
  | Term.Bool, U, _hValid, hEq => by
      have hU : __eo_to_smt_type U = SmtType.Bool := by
        simpa using hEq.symm
      exact (eo_to_smt_type_eq_bool hU).symm
  | Term.USort i, U, _hValid, hEq => by
      have hU : __eo_to_smt_type U = SmtType.USort i := by
        simpa using hEq.symm
      exact (eo_to_smt_type_eq_usort hU).symm
  | Term.DatatypeType s d, U, hValid, hEq => by
      rcases hValid with ⟨hReserved, hD⟩
      have hU :
          __eo_to_smt_type U = SmtType.Datatype s (__eo_to_smt_datatype d) := by
        simpa [__eo_to_smt_type, hReserved, native_ite] using hEq.symm
      rcases eo_to_smt_type_eq_datatype_non_tuple
          (eo_unreserved_datatype_name_ne_tuple hReserved) hU with
        ⟨d0, hUShape, hd0⟩
      subst U
      have hd : d = d0 :=
        eo_to_smt_datatype_unique_of_valid_rec_apply (s :: refs) hD hd0.symm
      subst d0
      rfl
  | Term.DatatypeTypeRef s, U, hValid, hEq => by
      rcases hValid with ⟨hReserved, _hMem⟩
      have hU : __eo_to_smt_type U = SmtType.TypeRef s := by
        simpa [__eo_to_smt_type, hReserved, native_ite] using hEq.symm
      exact (eo_to_smt_type_eq_typeref hU).symm
  | Term.DtcAppType T1 T2, U, hValid, hEq => by
      rcases hValid with ⟨hT1, hT2⟩
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT1
      have hT2NN : __eo_to_smt_type T2 ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT2
      have hU :
          __eo_to_smt_type U =
            SmtType.DtcAppType (__eo_to_smt_type T1) (__eo_to_smt_type T2) := by
        simp [__eo_to_smt_type, hT1NN, hT2NN, __smtx_typeof_guard,
          native_ite, native_Teq] at hEq
        simp [hEq]
      rcases eo_to_smt_type_eq_dtc_app hU with
        ⟨U1, U2, hUShape, hU1, hU2⟩
      subst U
      have hSub1 : T1 = U1 :=
        eo_to_smt_type_unique_of_valid_rec_apply [] hT1 hU1.symm
      have hSub2 : T2 = U2 :=
        eo_to_smt_type_unique_of_valid_rec_apply [] hT2 hU2.symm
      subst U1
      subst U2
      rfl
  | Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), U, hValid, hEq => by
      have hz : native_zleq 0 n = true := by
        simpa [eo_type_valid_rec] using hValid
      have hU : __eo_to_smt_type U = SmtType.BitVec (native_int_to_nat n) := by
        simpa [__eo_to_smt_type, native_ite, hz] using hEq.symm
      have hUShape := eo_to_smt_type_eq_bitvec hU
      subst U
      have hnNonneg : 0 <= n := by
        simpa [native_zleq, SmtEval.native_zleq] using hz
      have hNatInt : native_nat_to_int (native_int_to_nat n) = n := by
        simp [native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
          SmtEval.native_int_to_nat, Int.toNat_of_nonneg hnNonneg]
      rw [hNatInt]
  | Term.Apply (Term.UOp UserOp.Seq) T1, U, hValid, hEq => by
      have hT1 : eo_type_valid_rec [] T1 := by
        simpa [eo_type_valid_rec] using hValid
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT1
      have hU : __eo_to_smt_type U = SmtType.Seq (__eo_to_smt_type T1) := by
        simp [__eo_to_smt_type, hT1NN, __smtx_typeof_guard, native_ite, native_Teq] at hEq
        simp [hEq]
      rcases eo_to_smt_type_eq_seq hU with ⟨U1, hUShape, hU1⟩
      subst U
      have hSub : T1 = U1 :=
        eo_to_smt_type_unique_of_valid_rec_apply [] hT1 hU1.symm
      subst U1
      rfl
  | Term.Apply (Term.UOp UserOp.Set) T1, U, hValid, hEq => by
      have hT1 : eo_type_valid_rec [] T1 := by
        simpa [eo_type_valid_rec] using hValid
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT1
      have hU : __eo_to_smt_type U = SmtType.Set (__eo_to_smt_type T1) := by
        simp [__eo_to_smt_type, hT1NN, __smtx_typeof_guard, native_ite, native_Teq] at hEq
        simp [hEq]
      rcases eo_to_smt_type_eq_set hU with ⟨U1, hUShape, hU1⟩
      subst U
      have hSub : T1 = U1 :=
        eo_to_smt_type_unique_of_valid_rec_apply [] hT1 hU1.symm
      subst U1
      rfl
  | Term.Apply (Term.Apply Term.FunType T1) T2, U, hValid, hEq => by
      rcases (by simpa [eo_type_valid_rec] using hValid :
        eo_type_valid_rec [] T1 ∧ eo_type_valid_rec [] T2) with ⟨hT1, hT2⟩
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT1
      have hT2NN : __eo_to_smt_type T2 ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT2
      have hU :
          __eo_to_smt_type U =
            SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2) := by
        simp [eo_to_smt_type_fun, hT1NN, hT2NN, __smtx_typeof_guard,
          native_ite, native_Teq] at hEq
        simp [hEq]
      rcases eo_to_smt_type_eq_fun hU with
        ⟨U1, U2, hUShape, hU1, hU2⟩
      subst U
      have hSub1 : T1 = U1 :=
        eo_to_smt_type_unique_of_valid_rec_apply [] hT1 hU1.symm
      have hSub2 : T2 = U2 :=
        eo_to_smt_type_unique_of_valid_rec_apply [] hT2 hU2.symm
      subst U1
      subst U2
      rfl
  | Term.Apply (Term.Apply (Term.UOp UserOp.Array) T1) T2, U, hValid, hEq => by
      rcases (by simpa [eo_type_valid_rec] using hValid :
        eo_type_valid_rec [] T1 ∧ eo_type_valid_rec [] T2) with ⟨hT1, hT2⟩
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT1
      have hT2NN : __eo_to_smt_type T2 ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT2
      have hU :
          __eo_to_smt_type U =
            SmtType.Map (__eo_to_smt_type T1) (__eo_to_smt_type T2) := by
        simp [__eo_to_smt_type, hT1NN, hT2NN, __smtx_typeof_guard,
          native_ite, native_Teq] at hEq
        simp [hEq]
      rcases eo_to_smt_type_eq_map hU with
        ⟨U1, U2, hUShape, hU1, hU2⟩
      subst U
      have hSub1 : T1 = U1 :=
        eo_to_smt_type_unique_of_valid_rec_apply [] hT1 hU1.symm
      have hSub2 : T2 = U2 :=
        eo_to_smt_type_unique_of_valid_rec_apply [] hT2 hU2.symm
      subst U1
      subst U2
      rfl
  | Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2, U, hValid, hEq => by
      rcases (by simpa [eo_type_valid_rec] using hValid :
        eo_type_valid_rec [] T1 ∧ eo_type_valid_rec [] T2 ∧
          __smtx_type_wf
            (__eo_to_smt_type_tuple (__eo_to_smt_type T1) (__eo_to_smt_type T2)) =
            true) with ⟨_hT1, _hT2, hWf⟩
      let raw := __eo_to_smt_type_tuple (__eo_to_smt_type T1) (__eo_to_smt_type T2)
      have hWfRaw : __smtx_type_wf raw = true := by
        simpa [raw] using hWf
      have hTy :
          __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2) =
            raw := by
        change native_ite (__smtx_type_wf raw) raw SmtType.None = raw
        simp [native_ite, hWfRaw]
      have hField :
          smtx_type_field_wf_rec
            (__eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2))
            native_reflist_nil := by
        rw [hTy]
        exact smtx_type_field_wf_rec_of_type_wf_rec
          (smtx_type_wf_rec_of_type_wf
            (by
              simpa [raw] using
                (eo_to_smt_type_tuple_ne_reglan
                  (__eo_to_smt_type T1) (__eo_to_smt_type T2)))
            (by
              intro A B
              simpa [raw] using
                eo_to_smt_type_tuple_ne_fun (__eo_to_smt_type T1) (__eo_to_smt_type T2) A B)
            (by
              intro A B
              simpa [raw] using
                eo_to_smt_type_tuple_ne_ifun (__eo_to_smt_type T1) (__eo_to_smt_type T2) A B)
            hWfRaw)
      exact
        eo_to_smt_type_injective_of_field_wf_rec
          (T := Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2) (U := U)
          (A := __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2))
          (refs := native_reflist_nil) rfl hEq.symm hField
  | Term.Apply f x, U, hValid, hEq => by
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  have hz : native_zleq 0 n = true := by
                    simpa [eo_type_valid_rec] using hValid
                  have hU : __eo_to_smt_type U = SmtType.BitVec (native_int_to_nat n) := by
                    simpa [__eo_to_smt_type, native_ite, hz] using hEq.symm
                  have hUShape := eo_to_smt_type_eq_bitvec hU
                  subst U
                  have hnNonneg : 0 <= n := by
                    simpa [native_zleq, SmtEval.native_zleq] using hz
                  have hNatInt : native_nat_to_int (native_int_to_nat n) = n := by
                    simp [native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
                      SmtEval.native_int_to_nat, Int.toNat_of_nonneg hnNonneg]
                  rw [hNatInt]
              | _ =>
                  simp [eo_type_valid_rec] at hValid
          | Seq =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using hValid
              have hxNN : __eo_to_smt_type x ≠ SmtType.None :=
                eo_type_valid_rec_non_none hx
              have hU : __eo_to_smt_type U = SmtType.Seq (__eo_to_smt_type x) := by
                simpa [__eo_to_smt_type, hxNN, __smtx_typeof_guard, native_ite,
                  native_Teq] using hEq.symm
              rcases eo_to_smt_type_eq_seq hU with ⟨U1, hUShape, hU1⟩
              subst U
              have hSub : x = U1 :=
                eo_to_smt_type_unique_of_valid_rec_apply [] hx hU1.symm
              subst U1
              rfl
          | Set =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using hValid
              have hxNN : __eo_to_smt_type x ≠ SmtType.None :=
                eo_type_valid_rec_non_none hx
              have hU : __eo_to_smt_type U = SmtType.Set (__eo_to_smt_type x) := by
                simpa [__eo_to_smt_type, hxNN, __smtx_typeof_guard, native_ite,
                  native_Teq] using hEq.symm
              rcases eo_to_smt_type_eq_set hU with ⟨U1, hUShape, hU1⟩
              subst U
              have hSub : x = U1 :=
                eo_to_smt_type_unique_of_valid_rec_apply [] hx hU1.symm
              subst U1
              rfl
          | _ =>
              simp [eo_type_valid_rec] at hValid
      | Apply g y =>
          cases g with
          | FunType =>
              rcases (by simpa [eo_type_valid_rec] using hValid :
                eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
              have hyNN : __eo_to_smt_type y ≠ SmtType.None :=
                eo_type_valid_rec_non_none hy
              have hxNN : __eo_to_smt_type x ≠ SmtType.None :=
                eo_type_valid_rec_non_none hx
              have hU :
                  __eo_to_smt_type U =
                    SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x) := by
                simpa [eo_to_smt_type_fun, hyNN, hxNN, __smtx_typeof_guard,
                  native_ite, native_Teq] using hEq.symm
              rcases eo_to_smt_type_eq_fun hU with
                ⟨U1, U2, hUShape, hU1, hU2⟩
              subst U
              have hSub1 : y = U1 :=
                eo_to_smt_type_unique_of_valid_rec_apply [] hy hU1.symm
              have hSub2 : x = U2 :=
                eo_to_smt_type_unique_of_valid_rec_apply [] hx hU2.symm
              subst U1
              subst U2
              rfl
          | UOp op =>
              cases op with
              | Array =>
                  rcases (by simpa [eo_type_valid_rec] using hValid :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
                  have hyNN : __eo_to_smt_type y ≠ SmtType.None :=
                    eo_type_valid_rec_non_none hy
                  have hxNN : __eo_to_smt_type x ≠ SmtType.None :=
                    eo_type_valid_rec_non_none hx
                  have hU :
                      __eo_to_smt_type U =
                        SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x) := by
                    simpa [__eo_to_smt_type, hyNN, hxNN, __smtx_typeof_guard,
                      native_ite, native_Teq] using hEq.symm
                  rcases eo_to_smt_type_eq_map hU with
                    ⟨U1, U2, hUShape, hU1, hU2⟩
                  subst U
                  have hSub1 : y = U1 :=
                    eo_to_smt_type_unique_of_valid_rec_apply [] hy hU1.symm
                  have hSub2 : x = U2 :=
                    eo_to_smt_type_unique_of_valid_rec_apply [] hx hU2.symm
                  subst U1
                  subst U2
                  rfl
              | Tuple =>
                  rcases (by simpa [eo_type_valid_rec] using hValid :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x ∧
                      __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) =
                        true) with ⟨_hy, _hx, hWf⟩
                  let raw := __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)
                  have hWfRaw : __smtx_type_wf raw = true := by
                    simpa [raw] using hWf
                  have hTy :
                      __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) y) x) =
                        raw := by
                    change native_ite (__smtx_type_wf raw) raw SmtType.None = raw
                    simp [native_ite, hWfRaw]
                  have hField :
                      smtx_type_field_wf_rec
                        (__eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) y) x))
                        native_reflist_nil := by
                    rw [hTy]
                    exact smtx_type_field_wf_rec_of_type_wf_rec
                      (smtx_type_wf_rec_of_type_wf
                        (by
                          simpa [raw] using
                            (eo_to_smt_type_tuple_ne_reglan
                              (__eo_to_smt_type y) (__eo_to_smt_type x)))
                        (by
                          intro A B
                          simpa [raw] using
                            eo_to_smt_type_tuple_ne_fun (__eo_to_smt_type y) (__eo_to_smt_type x) A B)
                        (by
                          intro A B
                          simpa [raw] using
                            eo_to_smt_type_tuple_ne_ifun (__eo_to_smt_type y) (__eo_to_smt_type x) A B)
                        hWfRaw)
                  exact
                    eo_to_smt_type_injective_of_field_wf_rec
                      (T := Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) y) x) (U := U)
                      (A := __eo_to_smt_type
                        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) y) x))
                      (refs := native_reflist_nil) rfl hEq.symm hField
              | _ =>
                  simp [eo_type_valid_rec] at hValid
          | _ =>
              simp [eo_type_valid_rec] at hValid
      | _ =>
          simp [eo_type_valid_rec] at hValid
  | Term.__eo_List, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.__eo_List_nil, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.__eo_List_cons, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Boolean b, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Numeral n, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Rational q, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.String s, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Binary w n, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Type, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Stuck, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.FunType, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Var name T, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.DtCons s d i, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.DtSel s d i j, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.UConst i T, U, hValid, _hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.UOp1 op x, U, hValid, _hEq => by
      cases op <;> simp [eo_type_valid_rec] at hValid
  | Term.UOp2 op x y, U, hValid, _hEq => by
      cases op <;> simp [eo_type_valid_rec] at hValid
  | Term.UOp3 op x y z, U, hValid, _hEq => by
      cases op <;> simp [eo_type_valid_rec] at hValid

private theorem eo_to_smt_datatype_cons_unique_of_valid_rec_apply
    (refs : List native_String) :
    ∀ {c c' : DatatypeCons},
      eo_datatype_cons_valid_rec refs c ->
      __eo_to_smt_datatype_cons c = __eo_to_smt_datatype_cons c' ->
      c = c'
  | DatatypeCons.unit, c', _hValid, hEq => by
      cases c' <;> simp [__eo_to_smt_datatype_cons] at hEq
      rfl
  | DatatypeCons.cons T c, c', hValid, hEq => by
      rcases hValid with ⟨hT, hC⟩
      cases c' with
      | unit =>
          simp [__eo_to_smt_datatype_cons] at hEq
      | cons U c' =>
          simp [__eo_to_smt_datatype_cons] at hEq
          rcases hEq with ⟨hTU, hCC⟩
          have hT' : T = U :=
            eo_to_smt_type_unique_of_valid_rec_apply refs hT hTU
          have hC' : c = c' :=
            eo_to_smt_datatype_cons_unique_of_valid_rec_apply refs hC hCC
          subst U
          subst c'
          rfl

private theorem eo_to_smt_datatype_unique_of_valid_rec_apply
    (refs : List native_String) :
    ∀ {d d' : Datatype},
      eo_datatype_valid_rec refs d ->
      __eo_to_smt_datatype d = __eo_to_smt_datatype d' ->
      d = d'
  | Datatype.null, d', _hValid, hEq => by
      cases d' <;> simp [__eo_to_smt_datatype] at hEq
      rfl
  | Datatype.sum c d, d', hValid, hEq => by
      rcases hValid with ⟨hC, hD⟩
      cases d' with
      | null =>
          simp [__eo_to_smt_datatype] at hEq
      | sum c' d' =>
          simp [__eo_to_smt_datatype] at hEq
          rcases hEq with ⟨hCC, hDD⟩
          have hC' : c = c' :=
            eo_to_smt_datatype_cons_unique_of_valid_rec_apply refs hC hCC
          have hD' : d = d' :=
            eo_to_smt_datatype_unique_of_valid_rec_apply refs hD hDD
          subst c'
          subst d'
          rfl

end

/-- Injectivity of EO-to-SMT type translation on the proof-side valid fragment. -/
theorem eo_to_smt_type_eq_of_valid_rec
    {refs : List native_String} {T U : Term}
    (hValid : eo_type_valid_rec refs T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  exact eo_to_smt_type_unique_of_valid_rec_apply refs hValid hEq

/-- Top-level specialization of `eo_to_smt_type_eq_of_valid_rec`. -/
theorem eo_to_smt_type_eq_of_valid
    {T U : Term}
    (hValid : eo_type_valid_rec [] T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  exact eo_to_smt_type_eq_of_valid_rec hValid hEq

private theorem cons_subset
    {refs refs' : List native_String} {s : native_String}
    (hsub : ∀ t, t ∈ refs -> t ∈ refs') :
    ∀ t, t ∈ s :: refs -> t ∈ s :: refs' := by
  intro t ht
  simp at ht ⊢
  rcases ht with rfl | ht
  · exact Or.inl rfl
  · exact Or.inr (hsub t ht)

/- Weakening EO validity along ref-list inclusion. -/
mutual

private theorem eo_type_valid_rec_weaken
    {refs refs' : List native_String} :
    ∀ {T : Term},
      eo_type_valid_rec refs T ->
      (∀ t, t ∈ refs -> t ∈ refs') ->
      eo_type_valid_rec refs' T
  | Term.UOp op, h, _ => by
      cases op <;> simp [eo_type_valid_rec] at h ⊢
  | Term.Bool, _h, _ => by
      simp [eo_type_valid_rec]
  | Term.DatatypeType s d, h, hsub => by
      rcases h with ⟨hReserved, hD⟩
      exact ⟨hReserved, eo_datatype_valid_rec_weaken hD (cons_subset hsub)⟩
  | Term.DatatypeTypeRef s, h, hsub => by
      rcases h with ⟨hReserved, hMem⟩
      exact ⟨hReserved, hsub s hMem⟩
  | Term.DtcAppType T U, h, _ => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.USort i, _h, _ => by
      simp [eo_type_valid_rec]
  | Term.Apply (Term.Apply Term.FunType T1) T2, h, _ => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h, _ => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply (Term.UOp UserOp.Seq) T, h, _ => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U, h, _ => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply (Term.UOp UserOp.Set) T, h, _ => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U, h, _ => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply f x, h, _ => by
      cases f with
      | UOp op =>
          cases op <;>
            try (cases x <;> simp [eo_type_valid_rec] at h)
          all_goals
            try simp [eo_type_valid_rec] at h ⊢
            try exact h
      | Apply g y =>
          cases g with
          | FunType =>
              simp [eo_type_valid_rec] at h ⊢
              exact h
          | UOp op =>
              cases op <;>
                try (simp [eo_type_valid_rec] at h ⊢)
              all_goals
                try simp [eo_type_valid_rec] at h ⊢
                try exact h
          | _ =>
              simp [eo_type_valid_rec] at h
      | _ =>
          simp [eo_type_valid_rec] at h
  | Term.__eo_List, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.__eo_List_nil, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.__eo_List_cons, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.Boolean b, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.Numeral n, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.Rational q, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.String s, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.Binary w n, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.Type, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.Stuck, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.FunType, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.Var name T, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.DtCons s d i, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.DtSel s d i j, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.UConst i T, h, _ => by
      simp [eo_type_valid_rec] at h
  | Term.UOp1 op x, h, _ => by
      cases op <;> simp [eo_type_valid_rec] at h
  | Term.UOp2 op x y, h, _ => by
      cases op <;> simp [eo_type_valid_rec] at h
  | Term.UOp3 op x y z, h, _ => by
      cases op <;> simp [eo_type_valid_rec] at h

private theorem eo_datatype_cons_valid_rec_weaken
    {refs refs' : List native_String} :
    ∀ {c : DatatypeCons},
      eo_datatype_cons_valid_rec refs c ->
      (∀ t, t ∈ refs -> t ∈ refs') ->
      eo_datatype_cons_valid_rec refs' c
  | DatatypeCons.unit, _h, _ => by
      simp [eo_datatype_cons_valid_rec]
  | DatatypeCons.cons T c, h, hsub => by
      rcases h with ⟨hT, hC⟩
      exact ⟨eo_type_valid_rec_weaken hT hsub,
        eo_datatype_cons_valid_rec_weaken hC hsub⟩

private theorem eo_datatype_valid_rec_weaken
    {refs refs' : List native_String} :
    ∀ {d : Datatype},
      eo_datatype_valid_rec refs d ->
      (∀ t, t ∈ refs -> t ∈ refs') ->
      eo_datatype_valid_rec refs' d
  | Datatype.null, _h, _ => by
      simp [eo_datatype_valid_rec]
  | Datatype.sum c d, h, hsub => by
      rcases h with ⟨hC, hD⟩
      exact ⟨eo_datatype_cons_valid_rec_weaken hC hsub,
        eo_datatype_valid_rec_weaken hD hsub⟩

end

/- EO validity can discard references to reserved datatype names. -/
mutual

private theorem eo_type_valid_rec_refine_reserved
    {refs refs' : List native_String} {r : native_String}
    (hr : __eo_reserved_datatype_name r = true)
    (hsub : ∀ t, t ∈ refs -> t ∈ refs' ∨ t = r) :
    ∀ {T : Term}, eo_type_valid_rec refs T -> eo_type_valid_rec refs' T
  | Term.UOp op, h => by
      cases op <;> simp [eo_type_valid_rec] at h ⊢
  | Term.Bool, _h => by
      simp [eo_type_valid_rec]
  | Term.DatatypeType s d, h => by
      rcases h with ⟨hReserved, hD⟩
      have hsubCons : ∀ t, t ∈ s :: refs -> t ∈ s :: refs' ∨ t = r := by
        intro t ht
        simp at ht ⊢
        rcases ht with rfl | ht
        · exact Or.inl (Or.inl rfl)
        · rcases hsub t ht with ht' | hr'
          · exact Or.inl (Or.inr ht')
          · exact Or.inr hr'
      exact ⟨hReserved, eo_datatype_valid_rec_refine_reserved hr hsubCons hD⟩
  | Term.DatatypeTypeRef s, h => by
      rcases h with ⟨hReserved, hMem⟩
      rcases hsub s hMem with hMem' | hs
      · exact ⟨hReserved, hMem'⟩
      · subst s
        rw [hr] at hReserved
        cases hReserved
  | Term.DtcAppType T U, h => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.USort i, _h => by
      simp [eo_type_valid_rec]
  | Term.Apply (Term.Apply Term.FunType T1) T2, h => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply (Term.UOp UserOp.Seq) T, h => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U, h => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply (Term.UOp UserOp.Set) T, h => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U, h => by
      simp [eo_type_valid_rec] at h ⊢
      exact h
  | Term.Apply f x, h => by
      cases f with
      | UOp op =>
          cases op <;>
            try (cases x <;> simp [eo_type_valid_rec] at h)
          all_goals
            try simp [eo_type_valid_rec] at h ⊢
            try exact h
      | Apply g y =>
          cases g with
          | FunType =>
              simp [eo_type_valid_rec] at h ⊢
              exact h
          | UOp op =>
              cases op <;>
                try (simp [eo_type_valid_rec] at h ⊢)
              all_goals
                try simp [eo_type_valid_rec] at h ⊢
                try exact h
          | _ =>
              simp [eo_type_valid_rec] at h
      | _ =>
          simp [eo_type_valid_rec] at h
  | Term.__eo_List, h => by
      simp [eo_type_valid_rec] at h
  | Term.__eo_List_nil, h => by
      simp [eo_type_valid_rec] at h
  | Term.__eo_List_cons, h => by
      simp [eo_type_valid_rec] at h
  | Term.Boolean b, h => by
      simp [eo_type_valid_rec] at h
  | Term.Numeral n, h => by
      simp [eo_type_valid_rec] at h
  | Term.Rational q, h => by
      simp [eo_type_valid_rec] at h
  | Term.String s, h => by
      simp [eo_type_valid_rec] at h
  | Term.Binary w n, h => by
      simp [eo_type_valid_rec] at h
  | Term.Type, h => by
      simp [eo_type_valid_rec] at h
  | Term.Stuck, h => by
      simp [eo_type_valid_rec] at h
  | Term.FunType, h => by
      simp [eo_type_valid_rec] at h
  | Term.Var name T, h => by
      simp [eo_type_valid_rec] at h
  | Term.DtCons s d i, h => by
      simp [eo_type_valid_rec] at h
  | Term.DtSel s d i j, h => by
      simp [eo_type_valid_rec] at h
  | Term.UConst i T, h => by
      simp [eo_type_valid_rec] at h
  | Term.UOp1 op x, h => by
      cases op <;> simp [eo_type_valid_rec] at h
  | Term.UOp2 op x y, h => by
      cases op <;> simp [eo_type_valid_rec] at h
  | Term.UOp3 op x y z, h => by
      cases op <;> simp [eo_type_valid_rec] at h

private theorem eo_datatype_cons_valid_rec_refine_reserved
    {refs refs' : List native_String} {r : native_String}
    (hr : __eo_reserved_datatype_name r = true)
    (hsub : ∀ t, t ∈ refs -> t ∈ refs' ∨ t = r) :
    ∀ {c : DatatypeCons},
      eo_datatype_cons_valid_rec refs c ->
      eo_datatype_cons_valid_rec refs' c
  | DatatypeCons.unit, _h => by
      simp [eo_datatype_cons_valid_rec]
  | DatatypeCons.cons T c, h => by
      rcases h with ⟨hT, hC⟩
      exact ⟨eo_type_valid_rec_refine_reserved hr hsub hT,
        eo_datatype_cons_valid_rec_refine_reserved hr hsub hC⟩

private theorem eo_datatype_valid_rec_refine_reserved
    {refs refs' : List native_String} {r : native_String}
    (hr : __eo_reserved_datatype_name r = true)
    (hsub : ∀ t, t ∈ refs -> t ∈ refs' ∨ t = r) :
    ∀ {d : Datatype},
      eo_datatype_valid_rec refs d ->
      eo_datatype_valid_rec refs' d
  | Datatype.null, _h => by
      simp [eo_datatype_valid_rec]
  | Datatype.sum c d, h => by
      rcases h with ⟨hC, hD⟩
      exact ⟨eo_datatype_cons_valid_rec_refine_reserved hr hsub hC,
        eo_datatype_valid_rec_refine_reserved hr hsub hD⟩

end

/- Lifting (re-folding a datatype occurrence back to a `TypeRef`) preserves validity,
provided the re-folded name is in scope. The lift is shallow at the type level, so the
only non-identity case is a top-level `DatatypeType`. -/
mutual

private theorem eo_type_lift_preserves_valid (s0 : native_String) (d0 : Datatype)
    {T : Term} {refs : List native_String}
    (hMem : s0 ∈ refs) (hValid : eo_type_valid_rec refs T) :
    eo_type_valid_rec refs (__eo_type_lift s0 d0 T) := by
  cases T with
  | DatatypeType s2 d2 =>
      rcases hValid with ⟨hRes, hD⟩
      simp only [__eo_type_lift]
      by_cases hteq : native_teq (Term.DatatypeType s0 d0) (Term.DatatypeType s2 d2) = true
      · rw [native_ite, if_pos hteq]
        have hEq : Term.DatatypeType s0 d0 = Term.DatatypeType s2 d2 := of_decide_eq_true hteq
        injection hEq with hs hd
        subst hs
        exact ⟨hRes, hMem⟩
      · rw [native_ite, if_neg hteq]
        exact ⟨hRes, eo_datatype_lift_preserves_valid s0 d0 (List.mem_cons_of_mem _ hMem) hD⟩
  | _ => exact hValid

private theorem eo_datatype_cons_lift_preserves_valid (s0 : native_String) (d0 : Datatype)
    {c : DatatypeCons} {refs : List native_String}
    (hMem : s0 ∈ refs) (hValid : eo_datatype_cons_valid_rec refs c) :
    eo_datatype_cons_valid_rec refs (__eo_dtc_lift s0 d0 c) := by
  cases c with
  | unit => exact hValid
  | cons T c =>
      rcases hValid with ⟨hT, hC⟩
      exact ⟨eo_type_lift_preserves_valid s0 d0 hMem hT,
        eo_datatype_cons_lift_preserves_valid s0 d0 hMem hC⟩

private theorem eo_datatype_lift_preserves_valid (s0 : native_String) (d0 : Datatype)
    {d : Datatype} {refs : List native_String}
    (hMem : s0 ∈ refs) (hValid : eo_datatype_valid_rec refs d) :
    eo_datatype_valid_rec refs (__eo_dt_lift s0 d0 d) := by
  cases d with
  | null => exact hValid
  | sum c d =>
      rcases hValid with ⟨hC, hD⟩
      exact ⟨eo_datatype_cons_lift_preserves_valid s0 d0 hMem hC,
        eo_datatype_lift_preserves_valid s0 d0 hMem hD⟩

end

/- Substituting a valid datatype for a valid type-reference preserves datatype validity. -/
mutual

private theorem eo_datatype_cons_valid_rec_substitute
    (s : native_String) (dsub : Datatype) (refs : List native_String)
    (hSub : eo_datatype_valid_rec (s :: refs) dsub) :
    ∀ {c : DatatypeCons},
      eo_datatype_cons_valid_rec (s :: refs) c ->
      eo_datatype_cons_valid_rec refs (__eo_dtc_substitute s dsub c)
  | DatatypeCons.unit, _h => by
      simp [eo_datatype_cons_valid_rec, __eo_dtc_substitute]
  | DatatypeCons.cons T c, h => by
      rcases h with ⟨hT, hC⟩
      have hC' := eo_datatype_cons_valid_rec_substitute s dsub refs hSub hC
      cases T with
      | DatatypeType s2 d2 =>
          rcases hT with ⟨hReserved, hD2⟩
          by_cases hs : s = s2
          · subst s2
            have hD2' : eo_datatype_valid_rec (s :: refs) d2 := by
              apply eo_datatype_valid_rec_weaken hD2
              intro t ht
              cases ht with
              | head =>
                  simp
              | tail _ ht =>
                  exact ht
            have hT' : eo_type_valid_rec refs (Term.DatatypeType s d2) :=
              ⟨hReserved, hD2'⟩
            simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec, eo_type_valid_rec,
              native_ite, native_streq] using And.intro hT' hC'
          · have hD2' : eo_datatype_valid_rec (s2 :: refs)
                (__eo_dt_substitute s (__eo_dt_lift s2 d2 dsub) d2) := by
              have hSub' : eo_datatype_valid_rec (s :: s2 :: refs) dsub := by
                apply eo_datatype_valid_rec_weaken hSub
                intro t ht
                simp at ht ⊢
                rcases ht with rfl | ht
                · exact Or.inl rfl
                · exact Or.inr (Or.inr ht)
              have hD2swap : eo_datatype_valid_rec (s :: s2 :: refs) d2 := by
                apply eo_datatype_valid_rec_weaken hD2
                intro t ht
                simp at ht ⊢
                rcases ht with rfl | rfl | ht
                · exact Or.inr (Or.inl rfl)
                · exact Or.inl rfl
                · exact Or.inr (Or.inr ht)
              have hSubLifted : eo_datatype_valid_rec (s :: s2 :: refs)
                  (__eo_dt_lift s2 d2 dsub) :=
                eo_datatype_lift_preserves_valid s2 d2 (by simp) hSub'
              exact eo_datatype_valid_rec_substitute s (__eo_dt_lift s2 d2 dsub)
                (s2 :: refs) hSubLifted hD2swap
            have hT' :
                eo_type_valid_rec refs
                  (Term.DatatypeType s2 (__eo_dt_substitute s (__eo_dt_lift s2 d2 dsub) d2)) :=
              ⟨hReserved, hD2'⟩
            simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec, eo_type_valid_rec,
              hs, native_ite, native_streq] using And.intro hT' hC'
      | DatatypeTypeRef s2 =>
          rcases hT with ⟨hReserved, hMem⟩
          by_cases hs : s2 = s
          · subst s2
            have hT' : eo_type_valid_rec refs (Term.DatatypeType s dsub) :=
              ⟨hReserved, hSub⟩
            simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec, eo_type_valid_rec,
              native_ite, native_teq] using And.intro hT' hC'
          · have hMem' : s2 ∈ refs := by
              simpa [hs] using hMem
            have hT' : eo_type_valid_rec refs (Term.DatatypeTypeRef s2) :=
              ⟨hReserved, hMem'⟩
            simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec, eo_type_valid_rec,
              native_ite, native_teq, hs] using And.intro hT' hC'
      | UOp op =>
          cases op <;>
            try (simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec,
              eo_type_valid_rec, native_ite, native_teq] using And.intro hT hC')
          all_goals simp [eo_type_valid_rec] at hT
      | Bool =>
          simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec, eo_type_valid_rec,
            native_ite, native_teq] using And.intro trivial hC'
      | USort i =>
          simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec, eo_type_valid_rec,
            native_ite, native_teq] using And.intro trivial hC'
      | DtcAppType T1 T2 =>
          simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec, eo_type_valid_rec,
            native_ite, native_teq] using And.intro hT hC'
      | Apply f x =>
          cases f with
          | UOp op =>
              cases op with
              | BitVec =>
                  cases x with
                  | Numeral n =>
                      simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec,
                        eo_type_valid_rec, native_ite, native_teq] using And.intro hT hC'
                  | _ =>
                      simp [eo_type_valid_rec] at hT
              | Seq =>
                  simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec,
                    eo_type_valid_rec, native_ite, native_teq] using And.intro hT hC'
              | Set =>
                  simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec,
                    eo_type_valid_rec, native_ite, native_teq] using And.intro hT hC'
              | _ =>
                  simp [eo_type_valid_rec] at hT
          | Apply g y =>
              cases g with
              | FunType =>
                  simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec,
                    eo_type_valid_rec, native_ite, native_teq] using And.intro hT hC'
              | UOp op =>
                  cases op with
                  | Array =>
                      simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec,
                        eo_type_valid_rec, native_ite, native_teq] using And.intro hT hC'
                  | Tuple =>
                      simpa [__eo_dtc_substitute, eo_datatype_cons_valid_rec,
                        eo_type_valid_rec, native_ite, native_teq] using And.intro hT hC'
                  | _ =>
                      simp [eo_type_valid_rec] at hT
              | _ =>
                  simp [eo_type_valid_rec] at hT
          | _ =>
              simp [eo_type_valid_rec] at hT
      | __eo_List =>
          simp [eo_type_valid_rec] at hT
      | __eo_List_nil =>
          simp [eo_type_valid_rec] at hT
      | __eo_List_cons =>
          simp [eo_type_valid_rec] at hT
      | Boolean b =>
          simp [eo_type_valid_rec] at hT
      | Numeral n =>
          simp [eo_type_valid_rec] at hT
      | Rational q =>
          simp [eo_type_valid_rec] at hT
      | String str =>
          simp [eo_type_valid_rec] at hT
      | Binary w n =>
          simp [eo_type_valid_rec] at hT
      | «Type» =>
          simp [eo_type_valid_rec] at hT
      | Stuck =>
          simp [eo_type_valid_rec] at hT
      | FunType =>
          simp [eo_type_valid_rec] at hT
      | Var name ty =>
          simp [eo_type_valid_rec] at hT
      | DtCons s0 d0 i0 =>
          simp [eo_type_valid_rec] at hT
      | DtSel s0 d0 i0 j0 =>
          simp [eo_type_valid_rec] at hT
      | UConst i0 ty =>
          simp [eo_type_valid_rec] at hT
      | UOp1 op x =>
          cases op <;> simp [eo_type_valid_rec] at hT
      | UOp2 op x y =>
          cases op <;> simp [eo_type_valid_rec] at hT
      | UOp3 op x y z =>
          cases op <;> simp [eo_type_valid_rec] at hT

private theorem eo_datatype_valid_rec_substitute
    (s : native_String) (dsub : Datatype) (refs : List native_String)
    (hSub : eo_datatype_valid_rec (s :: refs) dsub) :
    ∀ {d : Datatype},
      eo_datatype_valid_rec (s :: refs) d ->
      eo_datatype_valid_rec refs (__eo_dt_substitute s dsub d)
  | Datatype.null, _h => by
      simp [eo_datatype_valid_rec, __eo_dt_substitute]
  | Datatype.sum c d, h => by
      rcases h with ⟨hC, hD⟩
      exact ⟨eo_datatype_cons_valid_rec_substitute s dsub refs hSub hC,
        eo_datatype_valid_rec_substitute s dsub refs hSub hD⟩

end

private theorem eo_to_smt_type_typeof_dt_cons_rec_zero_of_valid
    {T : Term}
    (hT : eo_type_valid_rec [] T) :
    ∀ {c : DatatypeCons} {d : Datatype},
      eo_datatype_cons_valid_rec [] c ->
      eo_datatype_valid_rec [] d ->
      __eo_to_smt_type (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero) =
        __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
          (SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d))
          native_nat_zero ∧
      eo_type_valid_rec [] (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero)
  | DatatypeCons.unit, d, _hC, _hD => by
      have hEq :
          __eo_typeof_dt_cons_rec T (Datatype.sum DatatypeCons.unit d) native_nat_zero = T := by
        cases T <;> simp [__eo_typeof_dt_cons_rec, eo_type_valid_rec] at hT ⊢
      refine ⟨?_, ?_⟩
      · rw [hEq]
        simp [__smtx_typeof_dt_cons_rec]
      · rw [hEq]
        exact hT
  | DatatypeCons.cons U c, d, hC, hD => by
      rcases hC with ⟨hU, hC⟩
      have hRec :=
        eo_to_smt_type_typeof_dt_cons_rec_zero_of_valid (T := T) hT hC hD
      have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
        eo_type_valid_rec_non_none hU
      have hRecNN :
          __eo_to_smt_type
              (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero) ≠
            SmtType.None :=
        eo_type_valid_rec_non_none hRec.2
      have hEq :
          __eo_typeof_dt_cons_rec T (Datatype.sum (DatatypeCons.cons U c) d) native_nat_zero =
            Term.DtcAppType U (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero) := by
        cases T <;> simp [__eo_typeof_dt_cons_rec, eo_type_valid_rec] at hT ⊢
      have hRecTyNN :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
              (SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d))
              native_nat_zero ≠
            SmtType.None := by
        rw [← hRec.1]
        exact hRecNN
      refine ⟨?_, ?_⟩
      · rw [hEq, eo_to_smt_type_dtc_app, hRec.1]
        simp [__smtx_typeof_dt_cons_rec, __eo_to_smt_datatype_cons,
          hUNN, hRecTyNN, __smtx_typeof_guard, native_ite, native_Teq]
      · rw [hEq]
        exact ⟨hU, hRec.2⟩

private theorem eo_to_smt_type_typeof_dt_cons_rec_of_valid
    {T : Term}
    (hT : eo_type_valid_rec [] T) :
    ∀ {d : Datatype} {i : native_Nat},
      eo_datatype_valid_rec [] d ->
      __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) (__eo_to_smt_datatype d) i ≠
        SmtType.None ->
      __eo_to_smt_type (__eo_typeof_dt_cons_rec T d i) =
        __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) (__eo_to_smt_datatype d) i ∧
      eo_type_valid_rec [] (__eo_typeof_dt_cons_rec T d i)
  | Datatype.null, i, _hD, hNN => by
      exact False.elim (hNN (by simp [__smtx_typeof_dt_cons_rec]))
  | Datatype.sum c d, native_nat_zero, hD, _hNN => by
      exact eo_to_smt_type_typeof_dt_cons_rec_zero_of_valid (T := T) hT hD.1 hD.2
  | Datatype.sum c d, native_nat_succ i, hD, hNN => by
      have hNN' :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) (__eo_to_smt_datatype d) i ≠
            SmtType.None := by
        simpa [__eo_to_smt_datatype, __smtx_typeof_dt_cons_rec] using hNN
      have hEq :
          __eo_typeof_dt_cons_rec T (Datatype.sum c d) (native_nat_succ i) =
            __eo_typeof_dt_cons_rec T d i := by
        cases T <;> cases c <;> simp [__eo_typeof_dt_cons_rec]
      have hSmtEq :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
              (__eo_to_smt_datatype (Datatype.sum c d)) (native_nat_succ i) =
            __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) (__eo_to_smt_datatype d) i := by
        simp [__eo_to_smt_datatype, __smtx_typeof_dt_cons_rec]
      rw [hEq, hSmtEq]
      exact eo_to_smt_type_typeof_dt_cons_rec_of_valid (T := T) hT hD.2 hNN'

theorem native_reflist_contains_true
    {refs : RefList} {s : native_String}
    (h : native_reflist_contains refs s = true) :
    s ∈ refs := by
  simpa [native_reflist_contains] using h

private theorem smtx_typeof_guard_ne_typeref
    (T U : SmtType)
    (hU : ∀ s, U ≠ SmtType.TypeRef s) :
    ∀ s, __smtx_typeof_guard T U ≠ SmtType.TypeRef s := by
  intro s h
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq] at h
  all_goals
    first
    | exact hU s h
    | cases h

private theorem smtx_type_field_wf_rec_to_type_wf_rec_of_not_typeref
    {T : SmtType} {refs : RefList}
    (hNoRef : ∀ s, T ≠ SmtType.TypeRef s)
    (h : smtx_type_field_wf_rec T refs) :
    __smtx_type_wf_rec T refs = true := by
  cases T <;> simp [smtx_type_field_wf_rec] at h hNoRef ⊢
  all_goals
    first
    | exact h
    | exact False.elim (hNoRef _ rfl)

/- Well-formed translated EO fields have proof-side valid EO shapes. -/
mutual

theorem eo_type_valid_of_smt_field_wf_rec
    (refs : RefList) :
    ∀ {T : Term},
      smtx_type_field_wf_rec (__eo_to_smt_type T) refs ->
      eo_type_valid_rec refs T
  | Term.UOp op, h => by
      cases op with
      | Int => simp [eo_type_valid_rec]
      | Real => simp [eo_type_valid_rec]
      | Char => simp [eo_type_valid_rec]
      | UnitTuple => simp [eo_type_valid_rec]
      | _ =>
          exfalso
          simp [__eo_to_smt_type, smtx_type_field_wf_rec,
            __smtx_type_wf_rec] at h
  | Term.Bool, _ => by
      simp [eo_type_valid_rec]
  | Term.USort i, _ => by
      simp [eo_type_valid_rec]
  | Term.DatatypeType s d, h => by
      by_cases hReservedTrue : __eo_reserved_datatype_name s = true
      · exfalso
        simp [__eo_to_smt_type, hReservedTrue, native_ite, smtx_type_field_wf_rec,
          __smtx_type_wf_rec] at h
      · have hReservedFalse : __eo_reserved_datatype_name s = false := by
          cases hName : __eo_reserved_datatype_name s <;> simp [hName] at hReservedTrue ⊢
        have hTypeWf :
            __smtx_type_wf_rec (SmtType.Datatype s (__eo_to_smt_datatype d)) refs =
              true := by
          simpa [__eo_to_smt_type, hReservedFalse, native_ite, smtx_type_field_wf_rec] using h
        have hDt :
            __smtx_dt_wf_rec (__eo_to_smt_datatype d) (s :: refs) = true := by
          have hParts :
              native_reflist_contains refs s = false ∧
                __smtx_dt_wf_rec (__eo_to_smt_datatype d)
                  (native_reflist_insert refs s) = true := by
            cases hRefs : native_reflist_contains refs s <;>
              simp [__smtx_type_wf_rec, native_ite, hRefs] at hTypeWf ⊢
            exact hTypeWf
          simpa [native_reflist_insert] using hParts.2
        exact ⟨hReservedFalse, eo_datatype_valid_of_smt_wf_rec (s :: refs) hDt⟩
  | Term.DatatypeTypeRef s, h => by
      by_cases hReservedTrue : __eo_reserved_datatype_name s = true
      · exfalso
        simp [__eo_to_smt_type, hReservedTrue, native_ite, smtx_type_field_wf_rec,
          __smtx_type_wf_rec] at h
      · have hReservedFalse : __eo_reserved_datatype_name s = false := by
          cases hName : __eo_reserved_datatype_name s <;> simp [hName] at hReservedTrue ⊢
        have hContains : native_reflist_contains refs s = true := by
          simpa [__eo_to_smt_type, hReservedFalse, native_ite, smtx_type_field_wf_rec] using h
        exact ⟨hReservedFalse, native_reflist_contains_true hContains⟩
  | Term.DtcAppType T U, h => by
      exfalso
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, smtx_type_field_wf_rec,
          __smtx_type_wf_rec, native_ite, native_Teq, hT, hU] at h
  | Term.Apply (Term.Apply Term.FunType T1) T2, h => by
      let choice :=
        native_ite
          (__smtx_is_finite_type
            (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2)))
          (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2))
          (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2))
      have hInnerNoRef :
          ∀ s,
            __smtx_typeof_guard (__eo_to_smt_type T2)
                choice ≠
              SmtType.TypeRef s :=
        smtx_typeof_guard_ne_typeref _ _
          (by
            intro s hRef
            cases hFin :
                __smtx_is_finite_type
                  (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2)) <;>
              simp [choice, native_ite, hFin] at hRef)
      have hGuardWf :
          __smtx_type_wf_rec
              (__smtx_typeof_guard (__eo_to_smt_type T1)
                (__smtx_typeof_guard (__eo_to_smt_type T2)
                  choice)) refs =
            true :=
        smtx_type_field_wf_rec_to_type_wf_rec_of_not_typeref
          (smtx_typeof_guard_ne_typeref _ _ hInnerNoRef)
          (by simpa [eo_to_smt_type_fun, choice] using h)
      have hOuter :
          __smtx_type_wf_rec
              (__smtx_typeof_guard (__eo_to_smt_type T2)
                choice) refs =
            true :=
        smtx_type_wf_rec_guard_of_true (__eo_to_smt_type T1)
          (__smtx_typeof_guard (__eo_to_smt_type T2)
            choice) refs
          hGuardWf
      have hChoice : __smtx_type_wf_rec choice refs = true :=
        smtx_type_wf_rec_guard_of_true (__eo_to_smt_type T2)
          choice refs hOuter
      cases hFin :
          __smtx_is_finite_type
            (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2)) <;>
        simp [choice, native_ite, hFin, __smtx_type_wf_rec] at hChoice
  | Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h => by
      have hn : native_zleq 0 n = true := by
        by_cases hn : native_zleq 0 n = true
        · exact hn
        · exfalso
          simp [__eo_to_smt_type, smtx_type_field_wf_rec, __smtx_type_wf_rec,
            native_ite, hn] at h
      simpa [eo_type_valid_rec] using hn
  | Term.Apply (Term.UOp UserOp.Seq) T, h => by
      have hGuardWf :
          __smtx_type_wf_rec
              (__smtx_typeof_guard (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)))
              refs =
            true :=
        smtx_type_field_wf_rec_to_type_wf_rec_of_not_typeref
          (smtx_typeof_guard_ne_typeref _ _ (by intro s hRef; cases hRef))
          (by simpa [__eo_to_smt_type] using h)
      have hSeq :
          __smtx_type_wf_rec (SmtType.Seq (__eo_to_smt_type T)) refs = true :=
        smtx_type_wf_rec_guard_of_true (__eo_to_smt_type T)
          (SmtType.Seq (__eo_to_smt_type T)) refs
          hGuardWf
      exact eo_type_valid_of_smt_field_wf_rec []
        (smtx_type_field_wf_rec_of_type_wf_rec (seq_type_wf_rec_component_of_wf hSeq))
  | Term.Apply (Term.UOp UserOp.Set) T, h => by
      have hGuardWf :
          __smtx_type_wf_rec
              (__smtx_typeof_guard (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)))
              refs =
            true :=
        smtx_type_field_wf_rec_to_type_wf_rec_of_not_typeref
          (smtx_typeof_guard_ne_typeref _ _ (by intro s hRef; cases hRef))
          (by simpa [__eo_to_smt_type] using h)
      have hSet :
          __smtx_type_wf_rec (SmtType.Set (__eo_to_smt_type T)) refs = true :=
        smtx_type_wf_rec_guard_of_true (__eo_to_smt_type T)
          (SmtType.Set (__eo_to_smt_type T)) refs
          hGuardWf
      exact eo_type_valid_of_smt_field_wf_rec []
        (smtx_type_field_wf_rec_of_type_wf_rec (set_type_wf_rec_component_of_wf hSet))
  | Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U, h => by
      have hInnerNoRef :
          ∀ s,
            __smtx_typeof_guard (__eo_to_smt_type U)
                (SmtType.Map (__eo_to_smt_type T) (__eo_to_smt_type U)) ≠
              SmtType.TypeRef s :=
        smtx_typeof_guard_ne_typeref _ _
          (by intro s hRef; cases hRef)
      have hGuardWf :
          __smtx_type_wf_rec
              (__smtx_typeof_guard (__eo_to_smt_type T)
                (__smtx_typeof_guard (__eo_to_smt_type U)
                  (SmtType.Map (__eo_to_smt_type T) (__eo_to_smt_type U)))) refs =
            true :=
        smtx_type_field_wf_rec_to_type_wf_rec_of_not_typeref
          (smtx_typeof_guard_ne_typeref _ _ hInnerNoRef)
          (by simpa [__eo_to_smt_type] using h)
      have hOuter :
          __smtx_type_wf_rec
              (__smtx_typeof_guard (__eo_to_smt_type U)
                (SmtType.Map (__eo_to_smt_type T) (__eo_to_smt_type U))) refs = true :=
        smtx_type_wf_rec_guard_of_true (__eo_to_smt_type T)
          (__smtx_typeof_guard (__eo_to_smt_type U)
            (SmtType.Map (__eo_to_smt_type T) (__eo_to_smt_type U))) refs
          hGuardWf
      have hMap :
          __smtx_type_wf_rec (SmtType.Map (__eo_to_smt_type T) (__eo_to_smt_type U)) refs =
            true :=
        smtx_type_wf_rec_guard_of_true (__eo_to_smt_type U)
          (SmtType.Map (__eo_to_smt_type T) (__eo_to_smt_type U)) refs hOuter
      rcases map_type_wf_rec_components_of_wf hMap with ⟨hT, hU⟩
      exact ⟨
        eo_type_valid_of_smt_field_wf_rec [] (smtx_type_field_wf_rec_of_type_wf_rec hT),
        eo_type_valid_of_smt_field_wf_rec [] (smtx_type_field_wf_rec_of_type_wf_rec hU)⟩
  | Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U, h => by
      let raw := __eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U)
      have hWf : __smtx_type_wf raw = true := by
        cases hRaw : __smtx_type_wf raw <;>
          simp [raw, __eo_to_smt_type, hRaw, native_ite, smtx_type_field_wf_rec,
            __smtx_type_wf_rec] at h ⊢
      have hRawField :
          smtx_type_field_wf_rec raw native_reflist_nil :=
          smtx_type_field_wf_rec_of_type_wf_rec
          (smtx_type_wf_rec_of_type_wf (by
            simpa [raw] using
              eo_to_smt_type_tuple_ne_reglan (__eo_to_smt_type T) (__eo_to_smt_type U))
            (by
              intro A B
              simpa [raw] using
                eo_to_smt_type_tuple_ne_fun (__eo_to_smt_type T) (__eo_to_smt_type U) A B)
            (by
              intro A B
              simpa [raw] using
                eo_to_smt_type_tuple_ne_ifun (__eo_to_smt_type T) (__eo_to_smt_type U) A B)
            hWf)
      have hParts : eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U := by
        cases hUTrans : __eo_to_smt_type U with
        | Datatype s d =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst s
              cases d with
              | null =>
                  exfalso
                  simp [raw, __eo_to_smt_type_tuple, hUTrans, __smtx_type_wf,
                    __smtx_type_wf_component, __smtx_type_wf_rec, native_and
                    ] at hWf
              | sum c dTail =>
                  cases dTail with
                  | null =>
                      have hRawField' :
                          smtx_type_field_wf_rec
                            (SmtType.Datatype (native_string_lit "@Tuple")
                              (SmtDatatype.sum
                                (SmtDatatypeCons.cons (__eo_to_smt_type T) c)
                                SmtDatatype.null))
                            native_reflist_nil := by
                        by_cases hHeadComp :
                            native_inhabited_type (__eo_to_smt_type T) = true ∧
                              __smtx_type_wf_rec (__eo_to_smt_type T)
                                native_reflist_nil = true
                        · have hCompTrue :
                              __smtx_type_wf_component (__eo_to_smt_type T) = true := by
                            simp [__smtx_type_wf_component, native_and,
                              hHeadComp.1, hHeadComp.2]
                          simpa [raw, __eo_to_smt_type_tuple, hUTrans, hCompTrue,
                            smtx_type_field_wf_rec, __smtx_type_wf_rec,
                            native_ite, native_reflist_nil,
                            native_reflist_contains] using hRawField
                        · exfalso
                          simp [raw, __eo_to_smt_type_tuple, hUTrans, hHeadComp,
                            __smtx_type_wf, __smtx_type_wf_component,
                            __smtx_type_wf_rec, native_and, native_ite] at hWf
                      have hWFParts := smtx_datatype_field_wf_rec_parts_local hRawField'
                      have hConsWF :
                          __smtx_dt_cons_wf_rec
                              (SmtDatatypeCons.cons (__eo_to_smt_type T) c)
                              (native_reflist_insert native_reflist_nil (native_string_lit "@Tuple")) =
                            true := by
                        simpa [__smtx_dt_wf_rec] using hWFParts.2
                      have hHeadFieldWF :
                          smtx_type_field_wf_rec (__eo_to_smt_type T)
                            (native_reflist_insert native_reflist_nil (native_string_lit "@Tuple")) :=
                        smtx_type_field_wf_rec_of_cons_wf hConsWF
                      have hHeadValidInTuple :
                          eo_type_valid_rec (native_reflist_insert native_reflist_nil (native_string_lit "@Tuple")) T :=
                        eo_type_valid_of_smt_field_wf_rec
                          (native_reflist_insert native_reflist_nil (native_string_lit "@Tuple")) hHeadFieldWF
                      have hHeadValid : eo_type_valid_rec [] T := by
                        simpa [native_reflist_nil] using
                          (eo_type_valid_rec_refine_reserved
                            (refs := native_reflist_insert native_reflist_nil (native_string_lit "@Tuple"))
                            (refs' := native_reflist_nil)
                            (r := (native_string_lit "@Tuple")) eo_reserved_datatype_name_tuple
                            (by
                              intro t ht
                              right
                              simpa [native_reflist_insert, native_reflist_nil] using ht)
                            hHeadValidInTuple)
                      have hTailWF :
                          __smtx_dt_cons_wf_rec c
                              (native_reflist_insert native_reflist_nil (native_string_lit "@Tuple")) =
                            true :=
                        smtx_dt_cons_wf_rec_tail_of_true hConsWF
                      have hTailFieldWF :
                          smtx_type_field_wf_rec (__eo_to_smt_type U) native_reflist_nil := by
                        rw [hUTrans]
                        simp [smtx_type_field_wf_rec, __smtx_type_wf_rec, __smtx_dt_wf_rec,
                          hWFParts.1, hTailWF, native_ite]
                      have hTailValid : eo_type_valid_rec [] U := by
                        simpa [native_reflist_nil] using
                          (eo_type_valid_of_smt_field_wf_rec native_reflist_nil hTailFieldWF)
                      exact ⟨hHeadValid, hTailValid⟩
                  | sum cTail dTailTail =>
                      exfalso
                      simp [raw, __eo_to_smt_type_tuple, hUTrans, __smtx_type_wf,
                        __smtx_type_wf_component, __smtx_type_wf_rec,
                        native_and] at hWf
            · exfalso
              cases d with
              | null =>
                  simp [raw, __eo_to_smt_type_tuple, hUTrans, __smtx_type_wf,
                    __smtx_type_wf_component, __smtx_type_wf_rec, native_and
                    ] at hWf
              | sum c dTail =>
                  cases dTail <;>
                    simp [raw, __eo_to_smt_type_tuple, hUTrans, hs, __smtx_type_wf,
                      __smtx_type_wf_component, __smtx_type_wf_rec, native_and,
                      native_ite] at hWf
        | _ =>
            exfalso
            simp [raw, __eo_to_smt_type_tuple, hUTrans, __smtx_type_wf,
              __smtx_type_wf_component, __smtx_type_wf_rec, native_and
              ] at hWf
      simpa [eo_type_valid_rec, raw] using
        (And.intro hParts.1 (And.intro hParts.2 (by simpa [raw] using hWf)))
  | Term.Apply f x, h => by
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  have hn : native_zleq 0 n = true := by
                    by_cases hn : native_zleq 0 n = true
                    · exact hn
                    · exfalso
                      simp [__eo_to_smt_type, smtx_type_field_wf_rec, __smtx_type_wf_rec,
                        native_ite, hn] at h
                  simpa [eo_type_valid_rec] using hn
                | _ =>
                    exfalso
                    simp [__eo_to_smt_type, smtx_type_field_wf_rec, __smtx_type_wf_rec] at h
          | Seq =>
              have hGuardWf :
                  __smtx_type_wf_rec
                      (__smtx_typeof_guard (__eo_to_smt_type x)
                        (SmtType.Seq (__eo_to_smt_type x))) refs =
                    true :=
                smtx_type_field_wf_rec_to_type_wf_rec_of_not_typeref
                  (smtx_typeof_guard_ne_typeref _ _ (by intro s hRef; cases hRef))
                  (by simpa [__eo_to_smt_type] using h)
              have hSeq :
                  __smtx_type_wf_rec (SmtType.Seq (__eo_to_smt_type x)) refs = true :=
                smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
                  (SmtType.Seq (__eo_to_smt_type x)) refs hGuardWf
              exact eo_type_valid_of_smt_field_wf_rec []
                (smtx_type_field_wf_rec_of_type_wf_rec (seq_type_wf_rec_component_of_wf hSeq))
          | Set =>
              have hGuardWf :
                  __smtx_type_wf_rec
                      (__smtx_typeof_guard (__eo_to_smt_type x)
                        (SmtType.Set (__eo_to_smt_type x))) refs =
                    true :=
                smtx_type_field_wf_rec_to_type_wf_rec_of_not_typeref
                  (smtx_typeof_guard_ne_typeref _ _ (by intro s hRef; cases hRef))
                  (by simpa [__eo_to_smt_type] using h)
              have hSet :
                  __smtx_type_wf_rec (SmtType.Set (__eo_to_smt_type x)) refs = true :=
                smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
                  (SmtType.Set (__eo_to_smt_type x)) refs hGuardWf
              exact eo_type_valid_of_smt_field_wf_rec []
                (smtx_type_field_wf_rec_of_type_wf_rec (set_type_wf_rec_component_of_wf hSet))
          | _ =>
              exfalso
              simp [__eo_to_smt_type, smtx_type_field_wf_rec,
                __smtx_type_wf_rec] at h
      | Apply g y =>
          cases g with
          | FunType =>
              let choice :=
                native_ite
                  (__smtx_is_finite_type
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)))
                  (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))
                  (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))
              have hInnerNoRef :
                  ∀ s,
                    __smtx_typeof_guard (__eo_to_smt_type x)
                        choice ≠
                      SmtType.TypeRef s :=
                smtx_typeof_guard_ne_typeref _ _
                  (by
                    intro s hRef
                    cases hFin :
                        __smtx_is_finite_type
                          (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                      simp [choice, native_ite, hFin] at hRef)
              have hGuardWf :
                  __smtx_type_wf_rec
                      (__smtx_typeof_guard (__eo_to_smt_type y)
                        (__smtx_typeof_guard (__eo_to_smt_type x)
                          choice)) refs =
                    true :=
                smtx_type_field_wf_rec_to_type_wf_rec_of_not_typeref
                  (smtx_typeof_guard_ne_typeref _ _ hInnerNoRef)
                  (by simpa [eo_to_smt_type_fun, choice] using h)
              have hOuter :
                  __smtx_type_wf_rec
                      (__smtx_typeof_guard (__eo_to_smt_type x)
                        choice) refs =
                    true :=
                smtx_type_wf_rec_guard_of_true (__eo_to_smt_type y)
                  (__smtx_typeof_guard (__eo_to_smt_type x)
                    choice) refs
                  hGuardWf
              have hChoice : __smtx_type_wf_rec choice refs = true :=
                smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
                  choice refs hOuter
              cases hFin :
                  __smtx_is_finite_type
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                simp [choice, native_ite, hFin, __smtx_type_wf_rec] at hChoice
          | UOp op =>
              cases op with
              | Array =>
                  have hInnerNoRef :
                      ∀ s,
                        __smtx_typeof_guard (__eo_to_smt_type x)
                            (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x)) ≠
                          SmtType.TypeRef s :=
                    smtx_typeof_guard_ne_typeref _ _
                      (by intro s hRef; cases hRef)
                  have hGuardWf :
                      __smtx_type_wf_rec
                          (__smtx_typeof_guard (__eo_to_smt_type y)
                            (__smtx_typeof_guard (__eo_to_smt_type x)
                              (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x)))) refs =
                        true :=
                    smtx_type_field_wf_rec_to_type_wf_rec_of_not_typeref
                      (smtx_typeof_guard_ne_typeref _ _ hInnerNoRef)
                      (by simpa [__eo_to_smt_type] using h)
                  have hOuter :
                      __smtx_type_wf_rec
                          (__smtx_typeof_guard (__eo_to_smt_type x)
                            (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x))) refs =
                        true :=
                    smtx_type_wf_rec_guard_of_true (__eo_to_smt_type y)
                      (__smtx_typeof_guard (__eo_to_smt_type x)
                        (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x))) refs
                      hGuardWf
                  have hMap :
                      __smtx_type_wf_rec
                          (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x)) refs = true :=
                    smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
                      (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x)) refs hOuter
                  rcases map_type_wf_rec_components_of_wf hMap with ⟨hy, hx⟩
                  exact ⟨
                    eo_type_valid_of_smt_field_wf_rec [] (smtx_type_field_wf_rec_of_type_wf_rec hy),
                    eo_type_valid_of_smt_field_wf_rec [] (smtx_type_field_wf_rec_of_type_wf_rec hx)⟩
              | Tuple =>
                  let raw := __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)
                  have hWf : __smtx_type_wf raw = true := by
                    cases hRaw : __smtx_type_wf raw <;>
                      simp [raw, __eo_to_smt_type, hRaw, native_ite, smtx_type_field_wf_rec,
                        __smtx_type_wf_rec] at h ⊢
                  have hRawField :
                      smtx_type_field_wf_rec raw native_reflist_nil :=
                    smtx_type_field_wf_rec_of_type_wf_rec
                      (smtx_type_wf_rec_of_type_wf (by
                        simpa [raw] using
                          eo_to_smt_type_tuple_ne_reglan (__eo_to_smt_type y)
                            (__eo_to_smt_type x))
                        (by
                          intro A B
                          simpa [raw] using
                            eo_to_smt_type_tuple_ne_fun (__eo_to_smt_type y)
                              (__eo_to_smt_type x) A B)
                        (by
                          intro A B
                          simpa [raw] using
                            eo_to_smt_type_tuple_ne_ifun (__eo_to_smt_type y)
                              (__eo_to_smt_type x) A B)
                        hWf)
                  have hParts : eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x := by
                    cases hXTrans : __eo_to_smt_type x with
                    | Datatype s d =>
                        by_cases hs : s = (native_string_lit "@Tuple")
                        · subst s
                          cases d with
                          | null =>
                              exfalso
                              simp [raw, __eo_to_smt_type_tuple, hXTrans,
                                __smtx_type_wf, __smtx_type_wf_component,
                                __smtx_type_wf_rec, native_and] at hWf
                          | sum c dTail =>
                              cases dTail with
                              | null =>
                                  have hRawField' :
                                      smtx_type_field_wf_rec
                                        (SmtType.Datatype (native_string_lit "@Tuple")
                                          (SmtDatatype.sum
                                            (SmtDatatypeCons.cons (__eo_to_smt_type y) c)
                                            SmtDatatype.null))
                                        native_reflist_nil := by
                                    by_cases hHeadComp :
                                        native_inhabited_type (__eo_to_smt_type y) = true ∧
                                          __smtx_type_wf_rec (__eo_to_smt_type y)
                                            native_reflist_nil = true
                                    · have hCompTrue :
                                          __smtx_type_wf_component (__eo_to_smt_type y) =
                                            true := by
                                        simp [__smtx_type_wf_component, native_and,
                                          hHeadComp.1, hHeadComp.2]
                                      simpa [raw, __eo_to_smt_type_tuple, hXTrans,
                                        hCompTrue, smtx_type_field_wf_rec,
                                        __smtx_type_wf_rec, native_ite,
                                        native_reflist_nil, native_reflist_contains] using hRawField
                                    · exfalso
                                      simp [raw, __eo_to_smt_type_tuple, hXTrans,
                                        hHeadComp, __smtx_type_wf,
                                        __smtx_type_wf_component, __smtx_type_wf_rec,
                                        native_and, native_ite] at hWf
                                  have hWFParts :=
                                    smtx_datatype_field_wf_rec_parts_local hRawField'
                                  have hConsWF :
                                      __smtx_dt_cons_wf_rec
                                          (SmtDatatypeCons.cons (__eo_to_smt_type y) c)
                                          (native_reflist_insert native_reflist_nil (native_string_lit "@Tuple")) =
                                        true := by
                                    simpa [__smtx_dt_wf_rec] using hWFParts.2
                                  have hHeadFieldWF :
                                      smtx_type_field_wf_rec (__eo_to_smt_type y)
                                        (native_reflist_insert native_reflist_nil (native_string_lit "@Tuple")) :=
                                    smtx_type_field_wf_rec_of_cons_wf hConsWF
                                  have hHeadValidInTuple :
                                      eo_type_valid_rec
                                          (native_reflist_insert native_reflist_nil (native_string_lit "@Tuple")) y :=
                                    eo_type_valid_of_smt_field_wf_rec
                                      (native_reflist_insert native_reflist_nil (native_string_lit "@Tuple"))
                                      hHeadFieldWF
                                  have hHeadValid : eo_type_valid_rec [] y := by
                                    simpa [native_reflist_nil] using
                                      (eo_type_valid_rec_refine_reserved
                                        (refs := native_reflist_insert native_reflist_nil (native_string_lit "@Tuple"))
                                        (refs' := native_reflist_nil)
                                        (r := (native_string_lit "@Tuple")) eo_reserved_datatype_name_tuple
                                        (by
                                          intro t ht
                                          right
                                          simpa [native_reflist_insert, native_reflist_nil] using ht)
                                        hHeadValidInTuple)
                                  have hTailWF :
                                      __smtx_dt_cons_wf_rec c
                                          (native_reflist_insert native_reflist_nil (native_string_lit "@Tuple")) =
                                        true :=
                                    smtx_dt_cons_wf_rec_tail_of_true hConsWF
                                  have hTailFieldWF :
                                      smtx_type_field_wf_rec (__eo_to_smt_type x)
                                        native_reflist_nil := by
                                    rw [hXTrans]
                                    simp [smtx_type_field_wf_rec, __smtx_type_wf_rec,
                                      __smtx_dt_wf_rec, hWFParts.1, hTailWF, native_ite]
                                  have hTailValid : eo_type_valid_rec [] x := by
                                    simpa [native_reflist_nil] using
                                      (eo_type_valid_of_smt_field_wf_rec native_reflist_nil
                                        hTailFieldWF)
                                  exact ⟨hHeadValid, hTailValid⟩
                              | sum cTail dTailTail =>
                                  exfalso
                                  simp [raw, __eo_to_smt_type_tuple, hXTrans,
                                    __smtx_type_wf, __smtx_type_wf_component,
                                    __smtx_type_wf_rec, native_and] at hWf
                        · exfalso
                          cases d with
                          | null =>
                              simp [raw, __eo_to_smt_type_tuple, hXTrans,
                                __smtx_type_wf, __smtx_type_wf_component,
                                __smtx_type_wf_rec, native_and] at hWf
                          | sum c dTail =>
                              cases dTail <;>
                                simp [raw, __eo_to_smt_type_tuple, hXTrans, hs,
                                  __smtx_type_wf, __smtx_type_wf_component,
                                  __smtx_type_wf_rec, native_and, native_ite] at hWf
                    | _ =>
                        exfalso
                        simp [raw, __eo_to_smt_type_tuple, hXTrans, __smtx_type_wf,
                          __smtx_type_wf_component, __smtx_type_wf_rec,
                          native_and] at hWf
                  simpa [eo_type_valid_rec, raw] using
                    (And.intro hParts.1 (And.intro hParts.2 (by simpa [raw] using hWf)))
              | _ =>
                  exfalso
                  simp [__eo_to_smt_type, smtx_type_field_wf_rec,
                    __smtx_type_wf_rec] at h
          | _ =>
              exfalso
              simp [__eo_to_smt_type, smtx_type_field_wf_rec,
                __smtx_type_wf_rec] at h
      | _ =>
          exfalso
          simp [__eo_to_smt_type, smtx_type_field_wf_rec,
            __smtx_type_wf_rec] at h
  | Term.__eo_List, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.__eo_List_nil, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.__eo_List_cons, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.Boolean b, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.Numeral n, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.Rational q, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.String s, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.Binary w n, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.Type, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.Stuck, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.FunType, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.Var name T, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.DtCons s d i, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.DtSel s d i j, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.UConst i T, h => by
      exfalso
      simp [__eo_to_smt_type, smtx_type_field_wf_rec,
        __smtx_type_wf_rec] at h
  | Term.UOp1 op x, h => by
      cases op <;> exfalso <;> simp [__eo_to_smt_type,
        smtx_type_field_wf_rec, __smtx_type_wf_rec] at h
  | Term.UOp2 op x y, h => by
      cases op <;> exfalso <;> simp [__eo_to_smt_type,
        smtx_type_field_wf_rec, __smtx_type_wf_rec] at h
  | Term.UOp3 op x y z, h => by
      cases op <;> exfalso <;> simp [__eo_to_smt_type,
        smtx_type_field_wf_rec, __smtx_type_wf_rec] at h

theorem eo_datatype_cons_valid_of_smt_wf_rec
    (refs : RefList) :
    ∀ {c : DatatypeCons},
      __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true ->
      eo_datatype_cons_valid_rec refs c
  | DatatypeCons.unit, _ => by
      simp [eo_datatype_cons_valid_rec]
  | DatatypeCons.cons T c, h => by
      have hField :
          smtx_type_field_wf_rec (__eo_to_smt_type T) refs :=
        smtx_type_field_wf_rec_of_cons_wf (by
          simpa [__eo_to_smt_datatype_cons] using h)
      have hTail :
          __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true :=
        smtx_dt_cons_wf_rec_tail_of_true (by
          simpa [__eo_to_smt_datatype_cons] using h)
      exact ⟨eo_type_valid_of_smt_field_wf_rec refs hField,
        eo_datatype_cons_valid_of_smt_wf_rec refs hTail⟩

theorem eo_datatype_valid_of_smt_wf_rec
    (refs : RefList) :
    ∀ {d : Datatype},
      __smtx_dt_wf_rec (__eo_to_smt_datatype d) refs = true ->
      eo_datatype_valid_rec refs d
  | Datatype.null, _ => by
      simp [eo_datatype_valid_rec]
  | Datatype.sum c d, h => by
      have hCons :
          __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true := by
        cases hC : __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs <;>
          cases d <;> simp [__eo_to_smt_datatype, __smtx_dt_wf_rec, native_ite, hC] at h ⊢
      cases d with
      | null =>
          exact ⟨eo_datatype_cons_valid_of_smt_wf_rec refs hCons, by
            simp [eo_datatype_valid_rec]⟩
      | sum cTail dTail =>
          have hTail :
              __smtx_dt_wf_rec (__eo_to_smt_datatype (Datatype.sum cTail dTail)) refs =
                true := by
            simpa [__eo_to_smt_datatype, __smtx_dt_wf_rec, native_ite, hCons] using h
          exact ⟨eo_datatype_cons_valid_of_smt_wf_rec refs hCons,
            eo_datatype_valid_of_smt_wf_rec refs hTail⟩

end

private theorem eo_to_smt_type_ne_reglan_of_ne_reglan_term
    {T : Term}
    (hT : T ≠ Term.UOp UserOp.RegLan) :
    __eo_to_smt_type T ≠ SmtType.RegLan := by
  intro hReg
  exact hT (eo_to_smt_type_eq_reglan hReg)

theorem eo_type_valid_of_smt_wf
    (T : Term)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    eo_type_valid T := by
  by_cases hReg : T = Term.UOp UserOp.RegLan
  · subst hReg
    simp [eo_type_valid]
  · by_cases hFun : ∃ A B, __eo_to_smt_type T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, hTy⟩
      rcases eo_to_smt_type_eq_fun hTy with ⟨T1, T2, hTerm, hT1, hT2⟩
      subst T
      have hParts := fun_type_wf_parts (by simpa [hTy] using hWf)
      simp [eo_type_valid]
      exact ⟨
        eo_type_valid_of_smt_field_wf_rec [] (smtx_type_field_wf_rec_of_type_wf_rec
          (by simpa [hT1] using hParts.2.1)),
        eo_type_valid_of_smt_field_wf_rec [] (smtx_type_field_wf_rec_of_type_wf_rec
          (by simpa [hT2] using hParts.2.2.2))⟩
    · have hRecWf :
          __smtx_type_wf_rec (__eo_to_smt_type T) (__eo_to_smt_type T) = true :=
        smtx_type_wf_rec_of_type_wf
          (eo_to_smt_type_ne_reglan_of_ne_reglan_term hReg)
          (by
            intro A B hTy
            exact hFun ⟨A, B, hTy⟩)
          (by
            intro A B hTy
            exact hFun ⟨A, B, hTy⟩)
          hWf
      have hField :
          smtx_type_field_wf_rec (__eo_to_smt_type T) native_reflist_nil :=
        smtx_type_field_wf_rec_of_type_wf_rec hRecWf
      have hValidRec : eo_type_valid_rec native_reflist_nil T :=
        eo_type_valid_of_smt_field_wf_rec native_reflist_nil hField
      cases T with
      | UOp op =>
          cases op with
          | RegLan =>
              exact False.elim (hReg rfl)
          | _ =>
              simpa [eo_type_valid] using hValidRec
      | _ =>
          simpa [eo_type_valid] using hValidRec

/-- Reduces `__eo_requires` when the compared EO types are definitionally equal. -/
theorem eo_requires_self_of_non_stuck
    (T U : Term) (h : T ≠ Term.Stuck) :
    __eo_requires T T U = U := by
  simp [__eo_requires, native_ite, native_not, native_teq, h]

/-- Computes EO self-equality for non-`Stuck` terms. -/
theorem eo_eq_self_of_non_stuck
    (T : Term) (h : T ≠ Term.Stuck) :
    __eo_eq T T = Term.Boolean true := by
  cases T <;> simp [__eo_eq, native_teq] at h ⊢

/-- Reduces `__eo_requires` after discharging an EO self-equality check. -/
theorem eo_requires_eo_eq_self_of_non_stuck
    (T U : Term) (h : T ≠ Term.Stuck) :
    __eo_requires (__eo_eq T T) (Term.Boolean true) U = U := by
  rw [eo_eq_self_of_non_stuck T h]
  simpa using eo_requires_self_of_non_stuck (Term.Boolean true) U (by simp)

/-- Reduces `__eo_requires` after discharging two EO self-equality checks. -/
theorem eo_requires_eo_and_eq_self_of_non_stuck
    (T U V : Term) (hT : T ≠ Term.Stuck) (hU : U ≠ Term.Stuck) :
    __eo_requires (__eo_and (__eo_eq T T) (__eo_eq U U)) (Term.Boolean true) V = V := by
  rw [eo_eq_self_of_non_stuck T hT, eo_eq_self_of_non_stuck U hU]
  simpa [__eo_and] using eo_requires_self_of_non_stuck (Term.Boolean true) V (by simp)

private theorem eo_to_smt_seq_empty_ne_numeral
    (T : SmtType) (n : native_Int) :
    __eo_to_smt_seq_empty T ≠ SmtTerm.Numeral n := by
  intro h
  cases T <;> simp [__eo_to_smt_seq_empty] at h

private theorem eo_to_smt_set_empty_ne_numeral
    (T : SmtType) (n : native_Int) :
    __eo_to_smt_set_empty T ≠ SmtTerm.Numeral n := by
  intro h
  cases T <;> simp [__eo_to_smt_set_empty] at h

private theorem eo_to_smt_map_diff_guard_ne_numeral
    (T : SmtType) (a b : SmtTerm) (n : native_Int) :
    native_ite (native_Teq T SmtType.None) SmtTerm.None
        (SmtTerm.map_diff a b) ≠
      SmtTerm.Numeral n := by
  intro h
  cases hT : native_Teq T SmtType.None <;>
    simp [native_ite, hT] at h

private theorem eo_to_smt_array_deq_diff_ne_numeral
    (a b : SmtTerm) (n : native_Int) :
    __eo_to_smt_array_deq_diff a (__smtx_typeof a) b (__smtx_typeof b) ≠
      SmtTerm.Numeral n := by
  intro h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_array_deq_diff, ha, hb] at h <;>
    cases h

private theorem eo_to_smt_sets_deq_diff_ne_numeral
    (a b : SmtTerm) (n : native_Int) :
    __eo_to_smt_sets_deq_diff a (__smtx_typeof a) b (__smtx_typeof b) ≠
      SmtTerm.Numeral n := by
  intro h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_sets_deq_diff, ha, hb] at h <;>
    cases h

private theorem eo_to_smt_at_bv_ne_numeral
    (a b : SmtTerm) (n : native_Int) :
    __eo_to_smt__at_bv a b ≠ SmtTerm.Numeral n := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_to_smt__at_bv] at h
  case Numeral.Numeral x w =>
    cases hw : native_zleq 0 w
    · simp [hw] at h
    · simp [hw] at h

/-- A non-`None` `_at_bv` translation comes from two SMT numerals. -/
theorem eo_to_smt_at_bv_of_non_none
    {a b : SmtTerm}
    (hNN : __smtx_typeof (__eo_to_smt__at_bv a b) ≠ SmtType.None) :
    ∃ n w : native_Int,
      a = SmtTerm.Numeral n ∧
        b = SmtTerm.Numeral w ∧
          native_zleq 0 w = true ∧
            __smtx_typeof (__eo_to_smt__at_bv a b) =
              SmtType.BitVec (native_int_to_nat w) := by
  cases a <;> cases b
  case Numeral.Numeral n w =>
    cases hw : native_zleq 0 w
    · exact False.elim (hNN (by
        simp [__eo_to_smt__at_bv, native_ite, hw, smtx_typeof_none]))
    · have hBinaryNN :
          __smtx_typeof (SmtTerm.Binary w (native_mod_total n (native_int_pow2 w))) ≠
            SmtType.None := by
        simpa [__eo_to_smt__at_bv, native_ite, hw] using hNN
      exact ⟨n, w, rfl, rfl, hw, by
        simpa [__eo_to_smt__at_bv, native_ite, hw] using
          smtx_typeof_binary_of_non_none w
            (native_mod_total n (native_int_pow2 w)) hBinaryNN⟩
  all_goals
    exact False.elim (hNN (by
      simp [__eo_to_smt__at_bv, smtx_typeof_none]))

private theorem eo_to_smt_quantifiers_skolemize_ne_numeral
    (t : SmtTerm) (k : native_Nat) (n : native_Int) :
    __eo_to_smt_quantifiers_skolemize t k ≠ SmtTerm.Numeral n := by
  intro h
  cases t <;> simp [__eo_to_smt_quantifiers_skolemize] at h

private theorem eo_to_smt_re_unfold_pos_component_ne_numeral
    (s r : SmtTerm) (k : native_Nat) (n : native_Int) :
    __eo_to_smt_re_unfold_pos_component s r k ≠ SmtTerm.Numeral n := by
  induction k generalizing s r with
  | zero =>
      intro h
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at h
  | succ k ih =>
      intro h
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at h
      case re_concat r1 r2 =>
        exact ih _ _ h

private theorem eo_to_smt_quantifier_term_ne_numeral
    (x y : Term) (n : native_Int) :
    __eo_to_smt (Term.UOp2 UserOp2._at_quantifiers_skolemize x y) ≠
      SmtTerm.Numeral n := by
  intro h
  cases x <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g vars =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change native_ite (__eo_to_smt_nat_is_valid y)
              (__eo_to_smt_quantifiers_skolemize
                (__eo_to_smt_exists vars (SmtTerm.not (__eo_to_smt body)))
                (__eo_to_smt_nat y))
              SmtTerm.None =
            SmtTerm.Numeral n at h
          cases hz : __eo_to_smt_nat_is_valid y <;>
            simp [native_ite, hz] at h
          exact False.elim (eo_to_smt_quantifiers_skolemize_ne_numeral
            (__eo_to_smt_exists vars (SmtTerm.not (__eo_to_smt body)))
            (__eo_to_smt_nat y) n h)

private theorem eo_to_smt_distinct_ne_numeral
    (xs : Term) (n : native_Int) :
    __eo_to_smt_distinct xs ≠ SmtTerm.Numeral n := by
  intro h
  cases xs <;> try cases h
  case Apply f a =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> cases h
    case Apply g x =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_tuple_select_ne_numeral
    (T : SmtType) (i t : SmtTerm) (n : native_Int) :
    __eo_to_smt_tuple_select T i t ≠ SmtTerm.Numeral n := by
  intro h
  cases T <;> cases i <;> simp [__eo_to_smt_tuple_select, native_ite] at h
  case Datatype.Numeral s d k =>
    by_cases hs : s = (native_string_lit "@Tuple")
    · subst hs
      cases hk : native_zleq 0 k <;> simp [hk] at h
    · simp [hs] at h

private theorem eo_to_smt_updater_ne_numeral
    (sel t u : SmtTerm) (n : native_Int) :
    __eo_to_smt_updater sel t u ≠ SmtTerm.Numeral n := by
  intro h
  cases sel <;> try cases h
  case DtSel s d i j =>
    cases hIdx : native_zlt (native_nat_to_int j) (native_nat_to_int (__smtx_dt_num_sels d i)) <;>
      simp [__eo_to_smt_updater, native_ite, hIdx] at h

theorem eo_to_smt_updater_dt_sel_guard_of_non_none
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) (t u : SmtTerm)
    (h :
      __smtx_typeof (__eo_to_smt_updater (SmtTerm.DtSel s d i j) t u) ≠
        SmtType.None) :
    native_zlt (native_nat_to_int j) (native_nat_to_int (__smtx_dt_num_sels d i)) =
      true := by
    cases hIdx : native_zlt (native_nat_to_int j) (native_nat_to_int (__smtx_dt_num_sels d i))
    · exfalso
      apply h
      simp [__eo_to_smt_updater, native_ite, hIdx, smtx_typeof_none]
    · simp

private theorem eo_to_smt_tuple_update_ne_numeral
    (T : SmtType) (i t u : SmtTerm) (n : native_Int) :
    __eo_to_smt_tuple_update T i t u ≠ SmtTerm.Numeral n := by
  intro h
  cases T <;> cases i <;> simp [__eo_to_smt_tuple_update, native_ite] at h
  case Datatype.Numeral s d k =>
    by_cases hs : s = (native_string_lit "@Tuple")
    · subst hs
      cases hk : native_zleq 0 k
      · simp [hk] at h
      · simp [hk] at h
        exact False.elim (eo_to_smt_updater_ne_numeral
          (SmtTerm.DtSel (native_string_lit "@Tuple") d native_nat_zero (native_int_to_nat k)) t u n h)
    · simp [hs] at h

private theorem eo_to_smt_tuple_prepend_rec_ne_numeral
    (tailD : SmtDatatype) (tail : SmtTerm) (k : native_Nat)
    (acc : SmtTerm) (n : native_Int)
    (hAcc : acc ≠ SmtTerm.Numeral n) :
    __eo_to_smt_tuple_prepend_rec tailD tail k acc ≠ SmtTerm.Numeral n := by
  intro h
  cases k with
  | zero =>
      exact hAcc h
  | succ k =>
      simp [__eo_to_smt_tuple_prepend_rec] at h

private theorem eo_to_smt_tuple_prepend_of_type_ne_numeral
    (tailTy : SmtType) (head : SmtTerm) (headTy : SmtType)
    (tail : SmtTerm) (n : native_Int) :
    __eo_to_smt_tuple_prepend_of_type tailTy head headTy tail ≠
      SmtTerm.Numeral n := by
  intro h
  cases tailTy <;> simp [__eo_to_smt_tuple_prepend_of_type] at h
  case Datatype s d =>
    by_cases hs : s = (native_string_lit "@Tuple")
    · subst s
      cases d with
      | null =>
          simp at h
      | sum c rest =>
          cases rest with
          | null =>
              cases hWf :
                  __smtx_type_wf
                    (SmtType.Datatype (native_string_lit "@Tuple")
                      (SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                        SmtDatatype.null)) <;>
                simp [hWf] at h
              exact
                eo_to_smt_tuple_prepend_rec_ne_numeral
                  (SmtDatatype.sum c SmtDatatype.null) tail
                  (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
                    native_nat_zero)
                  (SmtTerm.Apply
                    (SmtTerm.DtCons (native_string_lit "@Tuple")
                      (SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                        SmtDatatype.null) native_nat_zero)
                    head)
                  n
                  (by intro hSeed; cases hSeed)
                  h
          | sum cRest restRest =>
              simp at h
    · cases d with
      | null =>
          simp at h
      | sum c rest =>
          cases rest <;> simp [hs] at h

private theorem eo_to_smt_tuple_prepend_ne_numeral
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm) (n : native_Int) :
    __eo_to_smt_tuple_prepend head headTy tail ≠ SmtTerm.Numeral n := by
  intro h
  exact
    eo_to_smt_tuple_prepend_of_type_ne_numeral
      (__smtx_typeof tail) head headTy tail n h

private theorem eo_to_smt_set_insert_ne_numeral_of_not_typed_nil
    (xs : Term) (base : SmtTerm) (n : native_Int)
    (hxs : ∀ T, xs ≠ Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) :
    __eo_to_smt_set_insert xs base ≠ SmtTerm.Numeral n := by
  intro h
  cases xs <;> try cases h
  case Apply f a =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> try cases h
      case _at__at_TypedList_nil =>
        exact False.elim (hxs a rfl)
    case Apply g x =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_exists_ne_numeral_of_not_nil
    (xs : Term) (body : SmtTerm) (n : native_Int)
    (hxs : xs ≠ Term.__eo_List_nil) :
    __eo_to_smt_exists xs body ≠ SmtTerm.Numeral n := by
  intro h
  cases xs <;> try cases h
  case __eo_List_nil =>
    exact False.elim (hxs rfl)
  case Apply f a =>
    cases f <;> try cases h
    case Apply g x =>
      cases g <;> try cases h
      case __eo_List_cons =>
        cases x <;> try cases h
        case Var name T =>
          cases name <;> cases h

private theorem eo_to_smt_apply_set_insert_ne_numeral
    (xs x : Term) (n : native_Int) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ≠
      SmtTerm.Numeral n := by
  intro h
  cases xs <;> try cases h
  case Apply f a =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> try cases h
      case _at__at_TypedList_nil =>
        cases hTy :
            native_Teq (__smtx_typeof (__eo_to_smt x))
              (SmtType.Set (__eo_to_smt_type a))
        · change
            __eo_to_smt_set_insert
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) a)
                (__eo_to_smt x) =
              SmtTerm.Numeral n at h
          simp [__eo_to_smt_set_insert, hTy, native_ite] at h
        · change
            __eo_to_smt_set_insert
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) a)
                (__eo_to_smt x) =
              SmtTerm.Numeral n at h
          simp [__eo_to_smt_set_insert, hTy, native_ite] at h
          change __eo_to_smt x = SmtTerm.Numeral n at h
          rw [h] at hTy
          simp [__smtx_typeof, native_Teq] at hTy
    case Apply g head =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_apply_forall_ne_numeral
    (xs body : Term) (n : native_Int) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ≠
      SmtTerm.Numeral n := by
  intro h
  cases xs
  case __eo_List_nil =>
    change SmtTerm.None = SmtTerm.Numeral n at h
    cases h
  all_goals
    cases h

private theorem eo_to_smt_apply_exists_ne_numeral
    (xs body : Term) (n : native_Int) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ≠
      SmtTerm.Numeral n := by
  intro h
  cases xs
  case __eo_List_nil =>
    change SmtTerm.None = SmtTerm.Numeral n at h
    cases h
  all_goals
    exact False.elim (eo_to_smt_exists_ne_numeral_of_not_nil _ (__eo_to_smt body) n
      (by intro hnil; cases hnil) h)

private theorem eo_to_smt_apply_ne_numeral
    (f x : Term) (n : native_Int) :
    __eo_to_smt (Term.Apply f x) ≠ SmtTerm.Numeral n := by
  intro h
  cases f <;> try cases h
  case UOp op =>
    cases op <;> try cases h
    case distinct =>
      change native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct x) =
        SmtTerm.Numeral n at h
      cases ht : native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None <;>
        simp [native_ite, ht] at h
      exact False.elim (eo_to_smt_distinct_ne_numeral x n h)
    case _at_bvsize =>
      change native_ite
          (native_zleq 0 (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))))
          (SmtTerm._at_purify
            (SmtTerm.Numeral (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x)))))
          SmtTerm.None =
        SmtTerm.Numeral n at h
      cases hw : native_zleq 0 (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) <;>
        simp [native_ite, hw] at h
  case UOp1 op idx =>
    cases op <;> try cases h
    case tuple_select =>
      exact False.elim (eo_to_smt_tuple_select_ne_numeral
      (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt idx) (__eo_to_smt x) n h)
  case UOp2 op idx1 idx2 =>
    cases op <;> try cases h
  case Apply g y =>
    cases g <;> try cases h
    case UOp op =>
      cases op <;> try cases h
      case set_insert =>
        exact False.elim (eo_to_smt_apply_set_insert_ne_numeral y x n h)
      case «forall» =>
        exact False.elim (eo_to_smt_apply_forall_ne_numeral y x n h)
      case «exists» =>
        exact False.elim (eo_to_smt_apply_exists_ne_numeral y x n h)
      case tuple =>
        exact False.elim (eo_to_smt_tuple_prepend_ne_numeral
          (__eo_to_smt y) (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x) n h)
      case _at_array_deq_diff =>
        exact False.elim
          (eo_to_smt_array_deq_diff_ne_numeral
            (__eo_to_smt y) (__eo_to_smt x) n h)
      case _at_sets_deq_diff =>
        exact False.elim
          (eo_to_smt_sets_deq_diff_ne_numeral
            (__eo_to_smt y) (__eo_to_smt x) n h)
    case UOp1 op idx =>
      cases op <;> try cases h
      case update =>
        exact False.elim (eo_to_smt_updater_ne_numeral
          (__eo_to_smt idx) (__eo_to_smt y) (__eo_to_smt x) n h)
      case tuple_update =>
        exact False.elim (eo_to_smt_tuple_update_ne_numeral
          (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt idx)
          (__eo_to_smt y) (__eo_to_smt x) n h)
    case Apply g2 z =>
      cases g2 <;> try cases h
      case UOp op =>
        cases op <;> try cases h

/-- The only EO terms that translate to SMT numerals are EO numerals. -/
theorem eo_to_smt_eq_numeral
    (t : Term) (n : native_Int)
    (h : __eo_to_smt t = SmtTerm.Numeral n) :
    t = Term.Numeral n := by
  cases t with
  | Numeral m =>
      change SmtTerm.Numeral m = SmtTerm.Numeral n at h
      cases h
      rfl
  | UOp op => cases op <;> cases h
  | UOp1 op x =>
      cases op <;> try cases h
      · exact False.elim (eo_to_smt_seq_empty_ne_numeral (__eo_to_smt_type x) n h)
      · exact False.elim (eo_to_smt_set_empty_ne_numeral (__eo_to_smt_type x) n h)
  | UOp2 op x y =>
      cases op <;> try cases h
      case _at_bv =>
        exact False.elim (eo_to_smt_at_bv_ne_numeral (__eo_to_smt x) (__eo_to_smt y) n h)
      case _at_quantifiers_skolemize =>
        exact False.elim (eo_to_smt_quantifier_term_ne_numeral x y n h)
  | Var name T => cases name <;> cases h
  | DtCons s d i =>
      change native_ite (native_reserved_datatype_name s) SmtTerm.None
          (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) =
        SmtTerm.Numeral n at h
      cases hs : native_reserved_datatype_name s <;>
        simp [native_ite, hs] at h
  | DtSel s d i j =>
      change native_ite (native_reserved_datatype_name s) SmtTerm.None
          (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) =
        SmtTerm.Numeral n at h
      cases hs : native_reserved_datatype_name s <;>
        simp [native_ite, hs] at h
  | UOp3 op x y z =>
      cases op
      case _at_re_unfold_pos_component =>
        change native_ite (__eo_to_smt_nat_is_valid z)
            (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt_nat z))
            SmtTerm.None =
          SmtTerm.Numeral n at h
        cases hx : __eo_to_smt_nat_is_valid z <;>
          simp [native_ite, hx] at h
        exact False.elim (eo_to_smt_re_unfold_pos_component_ne_numeral
          (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt_nat z) n h)
      case _at_witness_string_length =>
        change native_ite
            (__eo_to_smt_nat_is_valid y)
            (native_ite
              (__eo_to_smt_nat_is_valid z)
              (SmtTerm.choice_nth (native_string_lit "@x") (__eo_to_smt_type x)
                (SmtTerm.eq
                  (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type x)))
                  (__eo_to_smt y))
                native_nat_zero)
              SmtTerm.None)
            SmtTerm.None =
          SmtTerm.Numeral n at h
        cases hy : __eo_to_smt_nat_is_valid y <;>
          simp [native_ite, hy] at h
        cases hz : __eo_to_smt_nat_is_valid z <;>
          simp [hz] at h
  | Apply f x => exact False.elim (eo_to_smt_apply_ne_numeral f x n h)
  | _ => cases h

section DeferredTypeRecovery


/-- Computes the type of the one-bit literal used by `bvite`. -/
private theorem typeof_binary_one_eq :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  have hNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    unfold __smtx_typeof
    simp [native_ite, SmtEval.native_and, native_zleq, native_zeq, native_mod_total,
      native_int_pow2]
    rfl
  simpa using smtx_typeof_binary_of_non_none 1 1 hNN

/-- Computes `__smtx_typeof_apply` for function-like apply heads. -/
private theorem smtx_typeof_apply_of_head_cases
    {F X A B : SmtType}
    (hHead : F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B)
    (hX : X = A)
    (hA : A ≠ SmtType.None) :
    __smtx_typeof_apply F X = B := by
  rcases hHead with hHead | hHead
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]

/-- Rewrites `generic_apply_type` for heads that are not datatype selectors/testers. -/
private theorem generic_apply_type_of_non_special_head
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  cases f <;> simp [__smtx_typeof]

/-- Simplifies EO-to-SMT type translation for `typeof_numeral`. -/
theorem eo_to_smt_type_typeof_numeral
    (n : native_Int) :
    __eo_to_smt_type (__eo_typeof (Term.Numeral n)) = SmtType.Int := by
  change __eo_to_smt_type (Term.UOp UserOp.Int) = SmtType.Int
  rfl

/-- Valid EO nat arguments are numerals, hence EO integers. -/
theorem eo_typeof_eq_int_of_nat_is_valid
    (t : Term)
    (h : __eo_to_smt_nat_is_valid t = true) :
    __eo_typeof t = Term.UOp UserOp.Int := by
  cases t <;> simp [__eo_to_smt_nat_is_valid] at h
  case Numeral n =>
    change __eo_lit_type_Numeral (Term.Numeral n) = Term.UOp UserOp.Int
    rfl

/-- Simplifies EO-to-SMT type translation for `typeof_rational`. -/
theorem eo_to_smt_type_typeof_rational
    (q : native_Rat) :
    __eo_to_smt_type (__eo_typeof (Term.Rational q)) = SmtType.Real := by
  change __eo_to_smt_type (Term.UOp UserOp.Real) = SmtType.Real
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_string`. -/
theorem eo_to_smt_type_typeof_string
    (s : native_String) :
    __eo_to_smt_type (__eo_typeof (Term.String s)) = SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) = SmtType.Seq SmtType.Char
  simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq]

/-- Simplifies EO-to-SMT type translation for `typeof_binary`. -/
theorem eo_to_smt_type_typeof_binary
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true) :
    __eo_to_smt_type (__eo_typeof (Term.Binary w n)) =
      SmtType.BitVec (native_int_to_nat w) := by
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) =
    SmtType.BitVec (native_int_to_nat w)
  simp [__eo_to_smt_type, native_ite, hWidth]

/-- Simplifies EO-to-SMT type translation for `typeof_var`. -/
theorem eo_to_smt_type_typeof_var
    (s : native_String) (T : Term) :
    __eo_to_smt_type (__eo_typeof (Term.Var (Term.String s) T)) = __eo_to_smt_type T := by
  change __eo_to_smt_type T = __eo_to_smt_type T
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_uconst`. -/
theorem eo_to_smt_type_typeof_uconst
    (i : native_Nat) (T : Term) :
    __eo_to_smt_type (__eo_typeof (Term.UConst i T)) = __eo_to_smt_type T := by
  change __eo_to_smt_type T = __eo_to_smt_type T
  rfl

/-- Stronger EO-side helper for successful function-like application. -/
theorem eo_to_smt_type_typeof_apply_of_fun_like
    (x f T U : Term)
    (hApply :
      __eo_typeof (Term.Apply f x) = __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hf :
      __eo_typeof f = Term.Apply (Term.Apply Term.FunType T) U ∨
        __eo_typeof f = Term.DtcAppType T U)
    (hx : __eo_typeof x = T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply f x)) = __eo_to_smt_type U := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hApply]
  rcases hf with hFun | hDtc
  · rw [hFun, hx]
    simp [__eo_typeof_apply, eo_requires_self_of_non_stuck T U hTNS]
  · rw [hDtc, hx]
    simp [__eo_typeof_apply, eo_requires_self_of_non_stuck T U hTNS]

/-- Stronger EO-side helper for `typeof_apply_var`. -/
theorem eo_to_smt_type_typeof_apply_var_of_fun_like
    (x T U V : Term) (s : native_String)
    (hT :
      T = Term.Apply (Term.Apply Term.FunType U) V ∨
        T = Term.DtcAppType U V)
    (hx : __eo_typeof x = U)
    (hU : __eo_to_smt_type U ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Var (Term.String s) T) x)) =
      __eo_to_smt_type V := by
  apply eo_to_smt_type_typeof_apply_of_fun_like
    (f := Term.Var (Term.String s) T) (T := U) (U := V)
  · change __eo_typeof (Term.Apply (Term.Var (Term.String s) T) x) =
      __eo_typeof_apply T (__eo_typeof x)
    rfl
  · change T = Term.Apply (Term.Apply Term.FunType U) V ∨ T = Term.DtcAppType U V
    exact hT
  · exact hx
  · exact hU

/-- Stronger EO-side helper for `typeof_apply_uconst`. -/
theorem eo_to_smt_type_typeof_apply_uconst_of_fun_like
    (x T U V : Term) (i : native_Nat)
    (hT :
      T = Term.Apply (Term.Apply Term.FunType U) V ∨
        T = Term.DtcAppType U V)
    (hx : __eo_typeof x = U)
    (hU : __eo_to_smt_type U ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UConst i T) x)) =
      __eo_to_smt_type V := by
  apply eo_to_smt_type_typeof_apply_of_fun_like
    (f := Term.UConst i T) (T := U) (U := V)
  · change __eo_typeof (Term.Apply (Term.UConst i T) x) =
      __eo_typeof_apply T (__eo_typeof x)
    rfl
  · change T = Term.Apply (Term.Apply Term.FunType U) V ∨ T = Term.DtcAppType U V
    exact hT
  · exact hx
  · exact hU

private def smtx_type_substitute_top (sub : native_String) (d0 : SmtDatatype) : SmtType -> SmtType
  | SmtType.Datatype s2 d2 =>
      SmtType.Datatype s2 (native_ite (native_streq sub s2) d2
        (__smtx_dt_substitute sub (__smtx_dt_lift s2 d2 d0) d2))
  | SmtType.TypeRef s2 =>
      native_ite (native_streq sub s2) (SmtType.Datatype sub d0) (SmtType.TypeRef s2)
  | T => T

private theorem smtx_type_substitute_eq_top
    (sub : native_String) (d0 : SmtDatatype) (T : SmtType) :
    __smtx_type_substitute sub d0 T = smtx_type_substitute_top sub d0 T := by
  cases T <;> rfl

mutual

private theorem smtx_type_substitute_top_of_wf_rec
    (sub : native_String) (d0 : SmtDatatype) :
    (T : SmtType) -> (refs : RefList) ->
      native_reflist_contains refs sub = false ->
      __smtx_type_wf_rec T refs = true ->
      smtx_type_substitute_top sub d0 T = T
  | SmtType.Datatype s d, refs, hNot, hWf => by
      have hDt : __smtx_dt_wf_rec d (native_reflist_insert refs s) = true := by
        cases hRefs : native_reflist_contains refs s <;>
          simp [__smtx_type_wf_rec, native_ite, hRefs] at hWf ⊢
        exact hWf
      by_cases hEq : sub = s
      · subst hEq
        simp [smtx_type_substitute_top, native_streq, native_ite]
      · have hNotRefs : sub ∉ refs := by
          simpa [native_reflist_contains] using hNot
        have hNotIns : native_reflist_contains (native_reflist_insert refs s) sub = false := by
          simp [native_reflist_insert, native_reflist_contains, hEq, hNotRefs]
        have hSub := smtx_dt_substitute_of_wf_rec sub (__smtx_dt_lift s d d0) d
          (native_reflist_insert refs s) hNotIns hDt
        simp [smtx_type_substitute_top, native_streq, native_ite, hEq, hSub]
  | SmtType.TypeRef s, refs, hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.DtcAppType A B, refs, hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.None, refs, hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Bool, refs, hNot, hWf => by simp [smtx_type_substitute_top]
  | SmtType.Int, refs, hNot, hWf => by simp [smtx_type_substitute_top]
  | SmtType.Real, refs, hNot, hWf => by simp [smtx_type_substitute_top]
  | SmtType.RegLan, refs, hNot, hWf => by simp [smtx_type_substitute_top]
  | SmtType.BitVec n, refs, hNot, hWf => by simp [smtx_type_substitute_top]
  | SmtType.Map A B, refs, hNot, hWf => by simp [smtx_type_substitute_top]
  | SmtType.Set A, refs, hNot, hWf => by simp [smtx_type_substitute_top]
  | SmtType.Seq A, refs, hNot, hWf => by simp [smtx_type_substitute_top]
  | SmtType.Char, refs, hNot, hWf => by simp [smtx_type_substitute_top]
  | SmtType.USort n, refs, hNot, hWf => by simp [smtx_type_substitute_top]
  | SmtType.FunType A B, refs, hNot, hWf => by simp [smtx_type_substitute_top]

private theorem smtx_dtc_substitute_of_wf_rec
    (sub : native_String) (d0 : SmtDatatype) :
    (c : SmtDatatypeCons) -> (refs : RefList) ->
      native_reflist_contains refs sub = false ->
      __smtx_dt_cons_wf_rec c refs = true ->
      __smtx_dtc_substitute sub d0 c = c
  | SmtDatatypeCons.unit, refs, hNot, hWf => by rfl
  | SmtDatatypeCons.cons T c, refs, hNot, hWf => by
      cases T with
      | TypeRef s =>
          by_cases hEq : sub = s
          · subst hEq
            have hContains : native_reflist_contains refs sub = true := by
              have hPair :
                  native_reflist_contains refs sub = true ∧
                    __smtx_dt_cons_wf_rec c refs = true := by
                simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
              exact hPair.1
            rw [hNot] at hContains
            cases hContains
          · have hTail : __smtx_dt_cons_wf_rec c refs = true := by
              simp [__smtx_dt_cons_wf_rec, native_ite] at hWf
              exact hWf.2
            have hTailSub := smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail
            have hT : __smtx_type_substitute sub d0 (SmtType.TypeRef s) = SmtType.TypeRef s := by
              simp [__smtx_type_substitute, native_streq, native_ite, hEq]
            simp [__smtx_dtc_substitute, hT, hTailSub]
      | Datatype s d =>
          have hPair :
              __smtx_type_wf_rec (SmtType.Datatype s d) refs = true ∧
                __smtx_dt_cons_wf_rec c refs = true := by
            simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
          have hT := smtx_type_substitute_top_of_wf_rec sub d0 (SmtType.Datatype s d) refs hNot hPair.1
          have hC := smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hPair.2
          have hT' :
              __smtx_type_substitute sub d0 (SmtType.Datatype s d) =
                SmtType.Datatype s d := by
            simpa [smtx_type_substitute_eq_top] using hT
          simp [__smtx_dtc_substitute, hT', hC]
      | None =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
      | DtcAppType A B =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
      | Bool =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true := by
            exact smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]
      | Int =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true := by
            exact smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]
      | Real =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true := by
            exact smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]
      | RegLan =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true := by
            exact smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]
      | BitVec n =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true := by
            exact smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]
      | Map A B =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true :=
            smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]
      | Set A =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true :=
            smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]
      | Seq A =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true :=
            smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]
      | Char =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true := by
            exact smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]
      | USort n =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true := by
            exact smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]
      | FunType A B =>
          have hTail : __smtx_dt_cons_wf_rec c refs = true :=
            smtx_dt_cons_wf_rec_tail_of_true hWf
          simp [__smtx_dtc_substitute, __smtx_type_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hTail]

private theorem smtx_dt_substitute_of_wf_rec
    (sub : native_String) (d0 : SmtDatatype) :
    (d : SmtDatatype) -> (refs : RefList) ->
      native_reflist_contains refs sub = false ->
      __smtx_dt_wf_rec d refs = true ->
      __smtx_dt_substitute sub d0 d = d
  | SmtDatatype.null, refs, hNot, hWf => by rfl
  | SmtDatatype.sum c d, refs, hNot, hWf => by
      have hCons : __smtx_dt_cons_wf_rec c refs = true := by
        cases hC : __smtx_dt_cons_wf_rec c refs <;>
          cases d <;> simp [__smtx_dt_wf_rec, native_ite, hC] at hWf ⊢
      cases d with
      | null =>
          simp [__smtx_dt_substitute,
            smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hCons]
      | sum cTail dTail =>
          have hTail :
              __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true := by
            simpa [__smtx_dt_wf_rec, native_ite, hCons] using hWf
          have hCSub := smtx_dtc_substitute_of_wf_rec sub d0 c refs hNot hCons
          have hDSub :=
            smtx_dt_substitute_of_wf_rec sub d0 (SmtDatatype.sum cTail dTail) refs hNot hTail
          change
            SmtDatatype.sum (__smtx_dtc_substitute sub d0 c)
                (__smtx_dt_substitute sub d0 (SmtDatatype.sum cTail dTail)) =
              SmtDatatype.sum c (SmtDatatype.sum cTail dTail)
          rw [hCSub, hDSub]

end

private theorem smtx_dtc_substitute_cons_eq
    (sub : native_String) (d0 : SmtDatatype) (T : SmtType) (c : SmtDatatypeCons) :
    __smtx_dtc_substitute sub d0 (SmtDatatypeCons.cons T c) =
      SmtDatatypeCons.cons (smtx_type_substitute_top sub d0 T)
        (__smtx_dtc_substitute sub d0 c) := by
  cases T <;> rfl

private theorem smtx_type_substitute_top_of_guard
    (sub : native_String) (d0 : SmtDatatype) (T U : SmtType)
    (hU : smtx_type_substitute_top sub d0 U = U) :
    smtx_type_substitute_top sub d0 (__smtx_typeof_guard T U) = __smtx_typeof_guard T U := by
  cases T
  · simp [__smtx_typeof_guard, smtx_type_substitute_top, native_ite, native_Teq]
  all_goals
    simpa [__smtx_typeof_guard, native_ite, native_Teq] using hU

/-- Fold-decision correspondence used by the `lift`: under SMT well-formedness of the candidate
body, the EO-level `native_teq` and SMT-level `native_Teq` equality checks agree. The forward
direction is congruence of translation; the backward direction is translation injectivity
(`eo_to_smt_datatype_injective_of_wf_rec`). -/
theorem eo_to_smt_teq_corr (s s2 : native_String) (dRef d2 : Datatype) (refs : RefList)
    (hwf : __smtx_dt_wf_rec (__eo_to_smt_datatype d2) refs = true) :
    native_teq (Term.DatatypeType s dRef) (Term.DatatypeType s2 d2)
      = native_Teq (SmtType.Datatype s (__eo_to_smt_datatype dRef))
          (SmtType.Datatype s2 (__eo_to_smt_datatype d2)) := by
  simp only [native_teq, native_Teq]
  by_cases hEO : Term.DatatypeType s dRef = Term.DatatypeType s2 d2
  · rw [decide_eq_true hEO]
    injection hEO with hs hd; subst hs; subst hd
    rw [decide_eq_true rfl]
  · rw [decide_eq_false hEO]
    have hSMTne : ¬ (SmtType.Datatype s (__eo_to_smt_datatype dRef)
        = SmtType.Datatype s2 (__eo_to_smt_datatype d2)) := by
      intro hSMT
      injection hSMT with hs hd
      subst hs
      have hde : dRef = d2 := eo_to_smt_datatype_injective_of_wf_rec hd rfl hwf
      subst hde
      exact hEO rfl
    rw [decide_eq_false hSMTne]

/-- Connector for the tuple case of the lift correspondence: a tuple that translates to a real
`Datatype` (not `None`) has a well-formed body, because `__eo_to_smt_type` gates the tuple
translation on `__smtx_type_wf` (`wf_component`, i.e. well-formed at the empty ref context). -/
theorem tuple_translate_wf {x1 x2 : Term} {s' : native_String} {body : SmtDatatype}
    (h : __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) x1) x2)
        = SmtType.Datatype s' body) :
    __smtx_type_wf_rec (SmtType.Datatype s' body) (SmtType.Datatype s' body) = true := by
  simp only [__eo_to_smt_type, native_ite] at h
  split at h
  · next hwf =>
      rw [h] at hwf
      simp only [__smtx_type_wf, __smtx_type_wf_component, native_and, Bool.and_eq_true] at hwf
      exact hwf.2
  · next => exact absurd h (by simp)

/-- Generalised tuple connector: any non-`DatatypeType` term that translates to a `Datatype`
must be a tuple, hence has a well-formed body. -/
theorem tuple_translate_wf_gen {fieldT : Term} {s' : native_String} {body : SmtDatatype}
    (hnDT : ∀ s2 d2, fieldT ≠ Term.DatatypeType s2 d2)
    (h : __eo_to_smt_type fieldT = SmtType.Datatype s' body) :
    __smtx_type_wf_rec (SmtType.Datatype s' body) (SmtType.Datatype s' body) = true := by
  cases fieldT with
  | DatatypeType s2 d2 => exact absurd rfl (hnDT s2 d2)
  | UOp op =>
      cases op with
      | UnitTuple =>
          simp only [__eo_to_smt_type] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [__smtx_type_wf_rec, __smtx_dt_wf_rec, __smtx_dt_cons_wf_rec, native_ite,
            native_reflist_contains, native_reflist_nil]
      | _ =>
          simp only [__eo_to_smt_type] at h
          repeat' split at h
          all_goals exact absurd h (by simp)
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op with
              | Tuple => exact tuple_translate_wf h
              | _ =>
                  simp only [__eo_to_smt_type, __smtx_typeof_guard, native_ite] at h
                  repeat' split at h
                  all_goals exact absurd h (by simp)
          | _ =>
              simp only [__eo_to_smt_type, __smtx_typeof_guard, native_ite] at h
              repeat' split at h
              all_goals exact absurd h (by simp)
      | UOp op =>
          cases op with
          | BitVec =>
              cases x <;>
                (simp only [__eo_to_smt_type, native_ite] at h
                 repeat' split at h
                 all_goals exact absurd h (by simp))
          | _ =>
              simp only [__eo_to_smt_type, __smtx_typeof_guard, native_ite] at h
              repeat' split at h
              all_goals exact absurd h (by simp)
      | _ =>
          simp only [__eo_to_smt_type] at h
          repeat' split at h
          all_goals exact absurd h (by simp)
  | _ =>
      simp only [__eo_to_smt_type, __smtx_typeof_guard, native_ite] at h
      repeat' split at h
      all_goals exact absurd h (by simp)

/- RESIDUAL ASSUMPTION (introduced by the `dtMutual` `__smtx_dt_lift` addition).

The `lift` re-folding commutes with the EO→SMT translation:
`translate (lift_eo s dRef d) = lift_smt s (translate dRef) (translate d)`.

This is **false in general**, due to a structural asymmetry between the two `lift`s:
* EO `__eo_type_lift` is SHALLOW on tuples — a tuple is a `Term.Apply (UOp Tuple) …`, which
  hits the catch-all `| T => T` and is left untouched.
* SMT `__smtx_type_lift` is DEEP — tuples translate to `SmtType.Datatype "@Tuple" body`
  (`__eo_to_smt_type`), and the SMT lift recurses into every `Datatype` body via
  `__smtx_dt_lift`.
So if a tuple field carries an inlined datatype equal to the re-fold target, the SMT side
folds it (→ `TypeRef`) while the EO side cannot reach it. The non-`Datatype` (`DatatypeType`)
case IS provable: only `dRef` needs SMT-wf, and `eo_to_smt_datatype_injective_of_wf_rec`
rules out a translation collision against the common image `translate dRef`.

Note the *substitute* commutation avoids this only on the valid/well-formed fragment:
substitute re-targets free `TypeRef`s, which a wf closed tuple has none of; lift re-targets
inlined `Datatype`s, which a wf tuple can contain. So SMT-wf is insufficient for a universal
lift theorem. The usable replacement below is `eo_to_smt_dt_lift_of_wf`, whose extra
free-reference premise rules out the bad tuple-folding case. -/

/-! ### Concrete refutation of `eo_to_smt_datatype_lift`

The commutation above is FALSE as stated. Witness `cexD`: a datatype whose single
constructor has one field that is a 1-tuple holding the *inlined* datatype
`DatatypeType "Foo" cexDRef`. The EO lift `__eo_dt_lift` is shallow on tuples (a tuple is a
`Term.Apply (UOp Tuple) …`, hitting the catch-all), so it leaves the inlined `Foo` in place.
The SMT lift `__smtx_dt_lift` recurses into the translated `Datatype "@Tuple" …` body and
folds `Foo` to `TypeRef "Foo"`. So the two sides differ:

* EO-lift-then-translate: `… (cons (Datatype "@Tuple" (cons (Datatype "Foo" …) …)) …)`
* translate-then-SMT-lift: `… (cons (Datatype "@Tuple" (cons (TypeRef "Foo")    …)) …)`
-/
private def cexS : native_String := native_string_lit "Foo"
private def cexDRef : Datatype := Datatype.sum DatatypeCons.unit Datatype.null
private def cexD : Datatype :=
  Datatype.sum
    (DatatypeCons.cons
      (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) (Term.DatatypeType cexS cexDRef))
        (Term.UOp UserOp.UnitTuple))
      DatatypeCons.unit)
    Datatype.null

/-- The two sides of `eo_to_smt_datatype_lift` are concretely unequal at `(cexS, cexDRef, cexD)`. -/
example :
    __eo_to_smt_datatype (__eo_dt_lift cexS cexDRef cexD) ≠
      __smtx_dt_lift cexS (__eo_to_smt_datatype cexDRef) (__eo_to_smt_datatype cexD) := by
  native_decide

/-- Therefore the universally-quantified commutation `eo_to_smt_datatype_lift` cannot hold. -/
theorem eo_to_smt_datatype_lift_not_general :
    ¬ (∀ (s : native_String) (dRef d : Datatype),
        __eo_to_smt_datatype (__eo_dt_lift s dRef d) =
          __smtx_dt_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype d)) := by
  intro h
  exact absurd (h cexS cexDRef cexD) (by native_decide)

/-! ### Concrete refutation of unconstrained substitution

The old all-inputs substitution commutation has the same root problem if the substituted
datatype is not constrained to the valid/well-formed fragment. Here the substituted-into
datatype carries a free `Sub` reference, so substitution observes the replacement. The replacement
contains `Datatype "Foo" cexSubstTarget2`, whose translation collides with the valid-looking
target `cexSubstTarget1` because both contain an invalid field that translates to `None`.
SMT lift folds the translated collision; EO lift does not, since the EO datatypes are distinct.
-/
private def cexSubstSub : native_String := native_string_lit "Sub"

private def cexSubstTarget1 : Datatype :=
  Datatype.sum
    (DatatypeCons.cons (Term.DatatypeTypeRef cexSubstSub)
      (DatatypeCons.cons Term.Stuck DatatypeCons.unit))
    Datatype.null

private def cexSubstTarget2 : Datatype :=
  Datatype.sum
    (DatatypeCons.cons (Term.DatatypeTypeRef cexSubstSub)
      (DatatypeCons.cons Term.FunType DatatypeCons.unit))
    Datatype.null

private def cexSubstReplacement : Datatype :=
  Datatype.sum
    (DatatypeCons.cons (Term.DatatypeType cexS cexSubstTarget2) DatatypeCons.unit)
    Datatype.null

private def cexSubstInto : Datatype :=
  Datatype.sum
    (DatatypeCons.cons (Term.DatatypeType cexS cexSubstTarget1) DatatypeCons.unit)
    Datatype.null

example : cexSubstTarget1 ≠ cexSubstTarget2 := by
  native_decide

example :
    __eo_to_smt_datatype cexSubstTarget1 =
      __eo_to_smt_datatype cexSubstTarget2 := by
  native_decide

example :
    __eo_to_smt_datatype
        (__eo_dt_substitute cexSubstSub
          (__eo_dt_lift cexS cexSubstTarget1 cexSubstReplacement)
          cexSubstTarget1) ≠
      __smtx_dt_substitute cexSubstSub
        (__smtx_dt_lift cexS (__eo_to_smt_datatype cexSubstTarget1)
          (__eo_to_smt_datatype cexSubstReplacement))
        (__eo_to_smt_datatype cexSubstTarget1) := by
  native_decide

example :
    __eo_to_smt_datatype
        (__eo_dt_substitute cexSubstSub cexSubstReplacement cexSubstInto) ≠
      __smtx_dt_substitute cexSubstSub
        (__eo_to_smt_datatype cexSubstReplacement)
        (__eo_to_smt_datatype cexSubstInto) := by
  native_decide

theorem eo_to_smt_datatype_substitute_not_general :
    ¬ (∀ (sub : native_String) (d0 d : Datatype),
        __eo_to_smt_datatype (__eo_dt_substitute sub d0 d) =
          __smtx_dt_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype d)) := by
  intro h
  exact
    (show
      __eo_to_smt_datatype
          (__eo_dt_substitute cexSubstSub cexSubstReplacement cexSubstInto) ≠
        __smtx_dt_substitute cexSubstSub
          (__eo_to_smt_datatype cexSubstReplacement)
          (__eo_to_smt_datatype cexSubstInto) by
      native_decide)
    (h cexSubstSub cexSubstReplacement cexSubstInto)

mutual
private theorem eo_lift_preserves_noDt_ty
    (s sub : native_String) (dRef : Datatype) :
    (T : Term) →
      noDtTy sub (__eo_to_smt_type T) = true →
      noDtTy sub (__eo_to_smt_type (__eo_type_lift s dRef T)) = true
  | Term.DatatypeType s2 d2, hNoDt => by
      by_cases hFold : native_teq (Term.DatatypeType s dRef) (Term.DatatypeType s2 d2) = true
      · have hEq : Term.DatatypeType s dRef = Term.DatatypeType s2 d2 :=
          of_decide_eq_true hFold
        injection hEq with hs hd
        subst hs
        subst hd
        by_cases hRes : __eo_reserved_datatype_name s = true <;>
          simp [__eo_type_lift, __eo_to_smt_type, native_ite, hFold, hRes, noDtTy]
      · by_cases hRes : __eo_reserved_datatype_name s2 = true
        · simp [__eo_type_lift, native_ite, hFold, hRes, noDtTy]
        · have hParts :
              native_streq s2 sub = false ∧ noDtDt sub (__eo_to_smt_datatype d2) = true := by
            simpa [__eo_to_smt_type, native_ite, hRes, noDtTy, native_and,
              native_not, Bool.and_eq_true] using hNoDt
          simp [__eo_type_lift, native_ite, hFold, hRes,
            noDtTy, native_and, native_not, Bool.and_eq_true]
          constructor
          · simpa [native_streq] using hParts.1
          · exact eo_lift_preserves_noDt_dt s sub dRef d2 hParts.2
  | Term.UOp op, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.UOp1 op x, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.UOp2 op x y, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.UOp3 op x y z, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.__eo_List, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.__eo_List_nil, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.__eo_List_cons, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.Bool, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.Boolean b, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.Numeral n, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.Rational q, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.String str, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.Binary w n, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.Type, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.Stuck, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.Apply f x, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.FunType, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.Var name T, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.DatatypeTypeRef s2, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.DtcAppType A B, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.DtCons name d i, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.DtSel name d i j, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.USort i, hNoDt => by simpa [__eo_type_lift] using hNoDt
  | Term.UConst i T, hNoDt => by simpa [__eo_type_lift] using hNoDt

private theorem eo_lift_preserves_noDt_dt
    (s sub : native_String) (dRef : Datatype) :
    (d : Datatype) →
      noDtDt sub (__eo_to_smt_datatype d) = true →
      noDtDt sub (__eo_to_smt_datatype (__eo_dt_lift s dRef d)) = true
  | Datatype.null, hNoDt => by
      simp [__eo_dt_lift, noDtDt]
  | Datatype.sum c d, hNoDt => by
      have hParts :
          noDtDtc sub (__eo_to_smt_datatype_cons c) = true ∧
            noDtDt sub (__eo_to_smt_datatype d) = true := by
        simpa [__eo_to_smt_datatype, noDtDt, native_and, Bool.and_eq_true] using hNoDt
      simp only [__eo_dt_lift, __eo_to_smt_datatype, noDtDt, native_and, Bool.and_eq_true]
      exact ⟨eo_lift_preserves_noDt_dtc s sub dRef c hParts.1,
        eo_lift_preserves_noDt_dt s sub dRef d hParts.2⟩

private theorem eo_lift_preserves_noDt_dtc
    (s sub : native_String) (dRef : Datatype) :
    (c : DatatypeCons) →
      noDtDtc sub (__eo_to_smt_datatype_cons c) = true →
      noDtDtc sub (__eo_to_smt_datatype_cons (__eo_dtc_lift s dRef c)) = true
  | DatatypeCons.unit, hNoDt => by
      simp [__eo_dtc_lift, noDtDtc]
  | DatatypeCons.cons T c, hNoDt => by
      have hParts :
          noDtTy sub (__eo_to_smt_type T) = true ∧
            noDtDtc sub (__eo_to_smt_datatype_cons c) = true := by
        simpa [__eo_to_smt_datatype_cons, noDtDtc, native_and, Bool.and_eq_true] using hNoDt
      simp only [__eo_dtc_lift, __eo_to_smt_datatype_cons, noDtDtc, native_and, Bool.and_eq_true]
      exact ⟨eo_lift_preserves_noDt_ty s sub dRef T hParts.1,
        eo_lift_preserves_noDt_dtc s sub dRef c hParts.2⟩
end

private theorem eo_to_smt_ty_lift_of_valid_noDt_non_datatype
    (s sub : native_String) (dRef : Datatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s)
      (__eo_to_smt_datatype dRef) = true)
    {T : Term}
    (hnDT : ∀ s2 d2, T ≠ Term.DatatypeType s2 d2)
    (hNoDt : noDtTy sub (__eo_to_smt_type T) = true) :
    __eo_to_smt_type (__eo_type_lift s dRef T) =
      __smtx_type_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_type T) := by
  have hLift : __eo_type_lift s dRef T = T := by
    cases T <;> try rfl
    case DatatypeType s2 d2 =>
      exact False.elim (hnDT s2 d2 rfl)
  rw [hLift]
  cases htr : __eo_to_smt_type T with
  | Datatype s' body =>
      have hWf :
          __smtx_type_wf_rec (SmtType.Datatype s' body) (SmtType.Datatype s' body) = true :=
        tuple_translate_wf_gen hnDT htr
      have hNoDt' : noDtTy sub (SmtType.Datatype s' body) = true := by
        simpa [htr] using hNoDt
      exact (lift_noop_of_wf_no_dt_ty s sub (__eo_to_smt_datatype dRef) hsne hFree
        (SmtType.Datatype s' body) native_reflist_nil
        (by simp [native_reflist_contains, native_reflist_nil]) hWf hNoDt').symm
  | Seq A => simp [__smtx_type_lift]
  | Set A => simp [__smtx_type_lift]
  | Map A B => simp [__smtx_type_lift]
  | FunType A B => simp [__smtx_type_lift]
  | DtcAppType A B => simp [__smtx_type_lift]
  | TypeRef s' => simp [__smtx_type_lift]
  | None => simp [__smtx_type_lift]
  | RegLan => simp [__smtx_type_lift]
  | Bool => simp [__smtx_type_lift]
  | Int => simp [__smtx_type_lift]
  | Real => simp [__smtx_type_lift]
  | BitVec w => simp [__smtx_type_lift]
  | Char => simp [__smtx_type_lift]
  | USort i => simp [__smtx_type_lift]

/- Substitution cannot require the replacement to stay SMT-WF after descending under a
`DatatypeType` binder: the EO replacement is lifted by that binder, and such lifts can
break SMT WF in the enlarged context. The stable proof-side invariant is EO-validity
plus absence of `Datatype sub ...` binders; it is enough for lift correspondence because
`DatatypeType` folds use valid-fragment injectivity, and tuple translations use the
`noDt` no-op lemmas from `SmtFreeRefs`. -/
mutual
private theorem eo_to_smt_ty_lift_of_valid_noDt (s sub : native_String) (dRef : Datatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s)
      (__eo_to_smt_datatype dRef) = true) :
    (T : Term) → (refs : RefList) →
      eo_datatype_valid_rec (s :: refs) dRef →
      eo_type_valid_rec refs T →
      noDtTy sub (__eo_to_smt_type T) = true →
      __eo_to_smt_type (__eo_type_lift s dRef T) =
        __smtx_type_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_type T)
  | Term.DatatypeType s2 d2, refs, hDRefValid, hValid, hNoDt => by
      rcases hValid with ⟨hRes, hD2Valid⟩
      have hParts :
          native_streq s2 sub = false ∧ noDtDt sub (__eo_to_smt_datatype d2) = true := by
        simpa [__eo_to_smt_type, native_ite, hRes, noDtTy, native_and,
          native_not, Bool.and_eq_true] using hNoDt
      have hDRefValid' :
          eo_datatype_valid_rec (s :: native_reflist_insert refs s2) dRef := by
        apply eo_datatype_valid_rec_weaken hDRefValid
        intro t ht
        simp [native_reflist_insert] at ht ⊢
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ht)
      simp only [__eo_type_lift]
      by_cases hteq : native_teq (Term.DatatypeType s dRef) (Term.DatatypeType s2 d2) = true
      · rw [native_ite, if_pos hteq]
        have hEq : Term.DatatypeType s dRef = Term.DatatypeType s2 d2 :=
          of_decide_eq_true hteq
        injection hEq with hs hd
        subst hs
        subst hd
        simp [__eo_to_smt_type, native_ite, hRes, __smtx_type_lift, native_Teq]
      · rw [native_ite, if_neg hteq]
        have hTeqF :
            ¬ native_Teq (SmtType.Datatype s (__eo_to_smt_datatype dRef))
                (SmtType.Datatype s2 (__eo_to_smt_datatype d2)) = true := by
          intro hTeq
          have hEq :
              SmtType.Datatype s (__eo_to_smt_datatype dRef) =
                SmtType.Datatype s2 (__eo_to_smt_datatype d2) :=
            of_decide_eq_true (by simpa [native_Teq] using hTeq)
          injection hEq with hs hd
          subst hs
          have hdEq : dRef = d2 :=
            eo_to_smt_datatype_unique_of_valid_rec_apply (s :: refs) hDRefValid hd
          subst hdEq
          exact hteq (by simp [native_teq])
        have hTr :
            __eo_to_smt_type (Term.DatatypeType s2 d2) =
              SmtType.Datatype s2 (__eo_to_smt_datatype d2) := by
          simp [__eo_to_smt_type, native_ite, hRes]
        rw [hTr, __smtx_type_lift, native_ite, if_neg hTeqF]
        simp [__eo_to_smt_type, native_ite, hRes]
        congr 1
        exact eo_to_smt_dt_lift_of_valid_noDt s sub dRef hsne hFree d2
          (native_reflist_insert refs s2) hDRefValid' hD2Valid hParts.2
  | Term.UOp op, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.UOp op) (by intro s2 d2 h; cases h) hNoDt
  | Term.UOp1 op x, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.UOp1 op x) (by intro s2 d2 h; cases h) hNoDt
  | Term.UOp2 op x y, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.UOp2 op x y) (by intro s2 d2 h; cases h) hNoDt
  | Term.UOp3 op x y z, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.UOp3 op x y z) (by intro s2 d2 h; cases h) hNoDt
  | Term.__eo_List, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.__eo_List) (by intro s2 d2 h; cases h) hNoDt
  | Term.__eo_List_nil, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.__eo_List_nil) (by intro s2 d2 h; cases h) hNoDt
  | Term.__eo_List_cons, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.__eo_List_cons) (by intro s2 d2 h; cases h) hNoDt
  | Term.Bool, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.Bool) (by intro s2 d2 h; cases h) hNoDt
  | Term.Boolean b, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.Boolean b) (by intro s2 d2 h; cases h) hNoDt
  | Term.Numeral n, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.Numeral n) (by intro s2 d2 h; cases h) hNoDt
  | Term.Rational q, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.Rational q) (by intro s2 d2 h; cases h) hNoDt
  | Term.String str, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.String str) (by intro s2 d2 h; cases h) hNoDt
  | Term.Binary w n, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.Binary w n) (by intro s2 d2 h; cases h) hNoDt
  | Term.Type, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.Type) (by intro s2 d2 h; cases h) hNoDt
  | Term.Stuck, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.Stuck) (by intro s2 d2 h; cases h) hNoDt
  | Term.Apply f x, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.Apply f x) (by intro s2 d2 h; cases h) hNoDt
  | Term.FunType, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.FunType) (by intro s2 d2 h; cases h) hNoDt
  | Term.Var name T, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.Var name T) (by intro s2 d2 h; cases h) hNoDt
  | Term.DatatypeTypeRef s2, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.DatatypeTypeRef s2) (by intro s2 d2 h; cases h) hNoDt
  | Term.DtcAppType A B, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.DtcAppType A B) (by intro s2 d2 h; cases h) hNoDt
  | Term.DtCons name d i, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.DtCons name d i) (by intro s2 d2 h; cases h) hNoDt
  | Term.DtSel name d i j, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.DtSel name d i j) (by intro s2 d2 h; cases h) hNoDt
  | Term.USort i, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.USort i) (by intro s2 d2 h; cases h) hNoDt
  | Term.UConst i T, refs, hDRefValid, hValid, hNoDt => by
      exact eo_to_smt_ty_lift_of_valid_noDt_non_datatype s sub dRef hsne hFree
        (T := Term.UConst i T) (by intro s2 d2 h; cases h) hNoDt

private theorem eo_to_smt_dt_lift_of_valid_noDt (s sub : native_String) (dRef : Datatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s)
      (__eo_to_smt_datatype dRef) = true) :
    (d0 : Datatype) → (refs : RefList) →
      eo_datatype_valid_rec (s :: refs) dRef →
      eo_datatype_valid_rec refs d0 →
      noDtDt sub (__eo_to_smt_datatype d0) = true →
      __eo_to_smt_datatype (__eo_dt_lift s dRef d0) =
        __smtx_dt_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype d0)
  | Datatype.null, refs, hDRefValid, hValid, hNoDt => by
      simp [__eo_dt_lift, __eo_to_smt_datatype, __smtx_dt_lift]
  | Datatype.sum c d, refs, hDRefValid, hValid, hNoDt => by
      rcases hValid with ⟨hCValid, hDValid⟩
      have hParts :
          noDtDtc sub (__eo_to_smt_datatype_cons c) = true ∧
            noDtDt sub (__eo_to_smt_datatype d) = true := by
        simpa [__eo_to_smt_datatype, noDtDt, native_and, Bool.and_eq_true] using hNoDt
      simp only [__eo_dt_lift, __eo_to_smt_datatype, __smtx_dt_lift]
      rw [eo_to_smt_dtc_lift_of_valid_noDt s sub dRef hsne hFree c refs
          hDRefValid hCValid hParts.1,
        eo_to_smt_dt_lift_of_valid_noDt s sub dRef hsne hFree d refs
          hDRefValid hDValid hParts.2]

private theorem eo_to_smt_dtc_lift_of_valid_noDt (s sub : native_String) (dRef : Datatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s)
      (__eo_to_smt_datatype dRef) = true) :
    (c : DatatypeCons) → (refs : RefList) →
      eo_datatype_valid_rec (s :: refs) dRef →
      eo_datatype_cons_valid_rec refs c →
      noDtDtc sub (__eo_to_smt_datatype_cons c) = true →
      __eo_to_smt_datatype_cons (__eo_dtc_lift s dRef c) =
        __smtx_dtc_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype_cons c)
  | DatatypeCons.unit, refs, hDRefValid, hValid, hNoDt => by
      simp [__eo_dtc_lift, __eo_to_smt_datatype_cons, __smtx_dtc_lift]
  | DatatypeCons.cons T c, refs, hDRefValid, hValid, hNoDt => by
      rcases hValid with ⟨hTValid, hCValid⟩
      have hParts :
          noDtTy sub (__eo_to_smt_type T) = true ∧
            noDtDtc sub (__eo_to_smt_datatype_cons c) = true := by
        simpa [__eo_to_smt_datatype_cons, noDtDtc, native_and, Bool.and_eq_true] using hNoDt
      simp only [__eo_dtc_lift, __eo_to_smt_datatype_cons, __smtx_dtc_lift]
      rw [eo_to_smt_ty_lift_of_valid_noDt s sub dRef hsne hFree T refs
          hDRefValid hTValid hParts.1,
        eo_to_smt_dtc_lift_of_valid_noDt s sub dRef hsne hFree c refs
          hDRefValid hCValid hParts.2]
end

/- Lift correspondence (the SOUND replacement for `eo_to_smt_datatype_lift`): translating the
EO-lifted datatype equals SMT-lifting the translated datatype, GIVEN SMT well-formedness of the
datatype and that the re-fold target `dRef` has a free reference `sub`. The `DatatypeType` field
case uses `eo_to_smt_teq_corr` (fold-decision via injectivity); the tuple field case will use
`Smtm.lift_noop_*` (tuple no-op) + `tuple_translate_wf_gen`. -/
mutual
theorem eo_to_smt_ty_lift_of_wf (s sub : native_String) (dRef : Datatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) (__eo_to_smt_datatype dRef) = true) :
    (T : Term) → (refs : RefList) →
      native_reflist_contains refs sub = true →
      __smtx_type_wf_rec (__eo_to_smt_type T) refs = true →
      __eo_to_smt_type (__eo_type_lift s dRef T) =
        __smtx_type_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_type T)
  | T, refs, hsr, hwf => by
    cases T with
    | DatatypeType s2 d2 =>
      by_cases hRes : native_reserved_datatype_name s2 = true
      · simp [__eo_to_smt_type, native_ite, hRes, __smtx_type_wf_rec] at hwf
      have hRes' : native_reserved_datatype_name s2 = false := by
        simpa using hRes
      have htrwf : __smtx_type_wf_rec (SmtType.Datatype s2 (__eo_to_smt_datatype d2)) refs = true := by
        simpa only [__eo_to_smt_type, native_ite, hRes'] using hwf
      have hns2 : native_reflist_contains refs s2 = false := by
        cases hc : native_reflist_contains refs s2 <;>
          simp [__smtx_type_wf_rec, native_ite, hc] at htrwf ⊢
      have hd2wf : __smtx_dt_wf_rec (__eo_to_smt_datatype d2) (native_reflist_insert refs s2) = true := by
        simp [__smtx_type_wf_rec, native_ite, hns2] at htrwf; exact htrwf
      have hsr2 : native_reflist_contains (native_reflist_insert refs s2) sub = true := by
        simp [native_reflist_contains, native_reflist_insert, List.mem_cons]
        right; simpa [native_reflist_contains] using hsr
      have htrDT : __eo_to_smt_type (Term.DatatypeType s2 d2)
          = SmtType.Datatype s2 (__eo_to_smt_datatype d2) := by
        simp [__eo_to_smt_type, native_ite, hRes']
      simp only [__eo_type_lift]
      have hcorr := eo_to_smt_teq_corr s s2 dRef d2 (native_reflist_insert refs s2) hd2wf
      by_cases hteq : native_teq (Term.DatatypeType s dRef) (Term.DatatypeType s2 d2) = true
      · rw [native_ite, if_pos hteq]
        have hEq : Term.DatatypeType s dRef = Term.DatatypeType s2 d2 := of_decide_eq_true hteq
        injection hEq with hs hd
        subst hs; subst hd
        have hLHS : __eo_to_smt_type (Term.DatatypeTypeRef s) = SmtType.TypeRef s := by
          simp [__eo_to_smt_type, native_ite, hRes']
        rw [hLHS, htrDT, __smtx_type_lift, native_ite, if_pos (by simp [native_Teq])]
      · rw [native_ite, if_neg hteq]
        have hTeqF : ¬ (native_Teq (SmtType.Datatype s (__eo_to_smt_datatype dRef))
            (SmtType.Datatype s2 (__eo_to_smt_datatype d2)) = true) := by
          rw [← hcorr]; exact hteq
        have hLHS : __eo_to_smt_type (Term.DatatypeType s2 (__eo_dt_lift s dRef d2))
            = SmtType.Datatype s2 (__eo_to_smt_datatype (__eo_dt_lift s dRef d2)) := by
          simp [__eo_to_smt_type, native_ite, hRes']
        rw [hLHS, htrDT, __smtx_type_lift, native_ite, if_neg hTeqF]
        congr 1
        exact eo_to_smt_dt_lift_of_wf s sub dRef hsne hFree d2 (native_reflist_insert refs s2) hsr2 hd2wf
    | Apply f x =>
      simp only [__eo_type_lift]
      refine (lift_noop_ty s sub (__eo_to_smt_datatype dRef) hsne hFree
        (__eo_to_smt_type (Term.Apply f x)) native_reflist_nil refs
        (by simp [native_reflist_contains, native_reflist_nil]) hsr ?_ hwf).symm
      cases htr : __eo_to_smt_type (Term.Apply f x) with
      | Datatype s' body => exact tuple_translate_wf_gen (by intro s2 d2; simp) htr
      | _ => rw [htr] at hwf; exact hwf
    | UOp op =>
      simp only [__eo_type_lift]
      refine (lift_noop_ty s sub (__eo_to_smt_datatype dRef) hsne hFree
        (__eo_to_smt_type (Term.UOp op)) native_reflist_nil refs
        (by simp [native_reflist_contains, native_reflist_nil]) hsr ?_ hwf).symm
      cases htr : __eo_to_smt_type (Term.UOp op) with
      | Datatype s' body => exact tuple_translate_wf_gen (by intro s2 d2; simp) htr
      | _ => rw [htr] at hwf; exact hwf
    | DatatypeTypeRef s2 =>
      simp only [__eo_type_lift]
      refine (lift_noop_ty s sub (__eo_to_smt_datatype dRef) hsne hFree
        (__eo_to_smt_type (Term.DatatypeTypeRef s2)) native_reflist_nil refs
        (by simp [native_reflist_contains, native_reflist_nil]) hsr ?_ hwf).symm
      cases htr : __eo_to_smt_type (Term.DatatypeTypeRef s2) with
      | Datatype s' body => exact tuple_translate_wf_gen (by intro s2 d2; simp) htr
      | _ => rw [htr] at hwf; exact hwf
    | DtcAppType a b =>
      simp only [__eo_type_lift]
      refine (lift_noop_ty s sub (__eo_to_smt_datatype dRef) hsne hFree
        (__eo_to_smt_type (Term.DtcAppType a b)) native_reflist_nil refs
        (by simp [native_reflist_contains, native_reflist_nil]) hsr ?_ hwf).symm
      cases htr : __eo_to_smt_type (Term.DtcAppType a b) with
      | Datatype s' body => exact tuple_translate_wf_gen (by intro s2 d2; simp) htr
      | _ => rw [htr] at hwf; exact hwf
    | _ => simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]

theorem eo_to_smt_dt_lift_of_wf (s sub : native_String) (dRef : Datatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) (__eo_to_smt_datatype dRef) = true) :
    (d0 : Datatype) → (refs : RefList) →
      native_reflist_contains refs sub = true →
      __smtx_dt_wf_rec (__eo_to_smt_datatype d0) refs = true →
      __eo_to_smt_datatype (__eo_dt_lift s dRef d0) =
        __smtx_dt_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype d0)
  | Datatype.null, refs, hsr, hwf => by
      simp [__eo_to_smt_datatype, __smtx_dt_wf_rec] at hwf
  | Datatype.sum c Datatype.null, refs, hsr, hwf => by
      simp only [__eo_to_smt_datatype, __smtx_dt_wf_rec] at hwf
      show SmtDatatype.sum (__eo_to_smt_datatype_cons (__eo_dtc_lift s dRef c)) SmtDatatype.null
        = SmtDatatype.sum (__smtx_dtc_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype_cons c)) SmtDatatype.null
      rw [eo_to_smt_dtc_lift_of_wf s sub dRef hsne hFree c refs hsr hwf]
  | Datatype.sum c (Datatype.sum c2 d2), refs, hsr, hwf => by
      simp only [__eo_to_smt_datatype, __smtx_dt_wf_rec, native_ite] at hwf
      have hc : __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true := by
        by_cases hcc : __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true
        · exact hcc
        · rw [if_neg hcc] at hwf; exact absurd hwf (by simp)
      have hd : __smtx_dt_wf_rec (__eo_to_smt_datatype (Datatype.sum c2 d2)) refs = true := by
        rw [if_pos hc] at hwf; exact hwf
      show SmtDatatype.sum (__eo_to_smt_datatype_cons (__eo_dtc_lift s dRef c))
            (__eo_to_smt_datatype (__eo_dt_lift s dRef (Datatype.sum c2 d2)))
        = SmtDatatype.sum (__smtx_dtc_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype_cons c))
            (__smtx_dt_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype (Datatype.sum c2 d2)))
      rw [eo_to_smt_dtc_lift_of_wf s sub dRef hsne hFree c refs hsr hc,
        eo_to_smt_dt_lift_of_wf s sub dRef hsne hFree (Datatype.sum c2 d2) refs hsr hd]

theorem eo_to_smt_dtc_lift_of_wf (s sub : native_String) (dRef : Datatype)
    (hsne : sub ≠ s)
    (hFree : hasFreeDt sub (native_reflist_insert native_reflist_nil s) (__eo_to_smt_datatype dRef) = true) :
    (c : DatatypeCons) → (refs : RefList) →
      native_reflist_contains refs sub = true →
      __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true →
      __eo_to_smt_datatype_cons (__eo_dtc_lift s dRef c) =
        __smtx_dtc_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype_cons c)
  | DatatypeCons.unit, refs, hsr, hwf => by
      simp [__eo_dtc_lift, __eo_to_smt_datatype_cons, __smtx_dtc_lift]
  | DatatypeCons.cons fieldT c', refs, hsr, hwf => by
      show SmtDatatypeCons.cons (__eo_to_smt_type (__eo_type_lift s dRef fieldT))
            (__eo_to_smt_datatype_cons (__eo_dtc_lift s dRef c'))
        = SmtDatatypeCons.cons (__smtx_type_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_type fieldT))
            (__smtx_dtc_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype_cons c'))
      cases htrf : __eo_to_smt_type fieldT with
      | TypeRef s'' =>
          simp only [__eo_to_smt_datatype_cons] at hwf
          rw [htrf] at hwf
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
          have htail : __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c') refs = true := by
            split at hwf
            · exact hwf
            · exact absurd hwf (by simp)
          congr 1
          · have hlift : __eo_type_lift s dRef fieldT = fieldT := by
              cases fieldT <;> simp_all [__eo_type_lift, __eo_to_smt_type, native_ite]
            simp only [hlift, htrf, __smtx_type_lift]
          · exact eo_to_smt_dtc_lift_of_wf s sub dRef hsne hFree c' refs hsr htail
      | _ =>
          simp only [__eo_to_smt_datatype_cons] at hwf
          rw [htrf] at hwf
          simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
          have hfield : __smtx_type_wf_rec (__eo_to_smt_type fieldT) refs = true := by
            rw [htrf]
            split at hwf
            · assumption
            · exact absurd hwf (by simp)
          have htail : __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c') refs = true := by
            split at hwf
            · exact hwf
            · exact absurd hwf (by simp)
          congr 1
          · rw [← htrf]
            exact eo_to_smt_ty_lift_of_wf s sub dRef hsne hFree fieldT refs hsr hfield
          · exact eo_to_smt_dtc_lift_of_wf s sub dRef hsne hFree c' refs hsr htail
end

/- `noRefSub sub W`: the EO datatype `W` has no free `DatatypeTypeRef sub` field (a `DatatypeType sub …`
binder shadows). Then `__eo_dt_substitute sub d0 W = W` (substituting `sub` is a no-op). Branch-B glue. -/
mutual
def noRefSubDt (sub : native_String) : Datatype → Bool
  | Datatype.sum c d => native_and (noRefSubDtc sub c) (noRefSubDt sub d)
  | Datatype.null => true
def noRefSubDtc (sub : native_String) : DatatypeCons → Bool
  | DatatypeCons.cons (Term.DatatypeType s2 d2) c =>
      native_and (native_or (native_streq sub s2) (noRefSubDt sub d2)) (noRefSubDtc sub c)
  | DatatypeCons.cons T c =>
      native_and (native_not (native_teq T (Term.DatatypeTypeRef sub))) (noRefSubDtc sub c)
  | DatatypeCons.unit => true
end

mutual
private theorem noRefSubDt_of_valid_no_free (sub : native_String) :
    (W : Datatype) → (refs : RefList) →
      native_reflist_contains refs sub = false →
      eo_datatype_valid_rec refs W →
      hasFreeDt sub refs (__eo_to_smt_datatype W) = false →
      noRefSubDt sub W = true
  | Datatype.null, refs, hNot, hValid, hFree => by
      simp [noRefSubDt]
  | Datatype.sum c d, refs, hNot, hValid, hFree => by
      rcases hValid with ⟨hCValid, hDValid⟩
      simp only [__eo_to_smt_datatype, hasFreeDt, native_or, Bool.or_eq_false_iff] at hFree
      simp only [noRefSubDt, native_and, Bool.and_eq_true]
      exact ⟨noRefSubDtc_of_valid_no_free sub c refs hNot hCValid hFree.1,
        noRefSubDt_of_valid_no_free sub d refs hNot hDValid hFree.2⟩

private theorem noRefSubDtc_of_valid_no_free (sub : native_String) :
    (c : DatatypeCons) → (refs : RefList) →
      native_reflist_contains refs sub = false →
      eo_datatype_cons_valid_rec refs c →
      hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false →
      noRefSubDtc sub c = true
  | DatatypeCons.unit, refs, hNot, hValid, hFree => by
      simp [noRefSubDtc]
  | DatatypeCons.cons U c, refs, hNot, hValid, hFree => by
      rcases hValid with ⟨hUValid, hCValid⟩
      have hTailValid := hCValid
      have hTailFreeAll : hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false :=
        hasFreeDtc_tail_false_of_cons_false sub refs (__eo_to_smt_type U)
          (__eo_to_smt_datatype_cons c) (by
            simpa [__eo_to_smt_datatype_cons] using hFree)
      cases U <;> try
        (have hTailFree : hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false := by
          exact hTailFreeAll
         have hTail := noRefSubDtc_of_valid_no_free sub c refs hNot hTailValid hTailFree
         simp [noRefSubDtc, native_and, native_not, native_teq, hTail])
      case DatatypeType s2 d2 =>
          rcases hUValid with ⟨hReserved, hD2Valid⟩
          have hFree' :
              hasFreeTy sub refs (__eo_to_smt_type (Term.DatatypeType s2 d2)) = false ∧
                hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false := by
            simpa [__eo_to_smt_datatype_cons, hasFreeDtc, native_or,
              Bool.or_eq_false_iff] using hFree
          have hD2Free :
              hasFreeDt sub (native_reflist_insert refs s2) (__eo_to_smt_datatype d2) = false := by
            simpa [__eo_to_smt_type, native_ite, hReserved, hasFreeTy] using hFree'.1
          have hTail := noRefSubDtc_of_valid_no_free sub c refs hNot hTailValid hFree'.2
          by_cases hs : sub = s2
          · subst hs
            simp [native_or]
          · have hNot' :
                native_reflist_contains (native_reflist_insert refs s2) sub = false := by
              simp [native_reflist_contains, native_reflist_insert, List.mem_cons]
              constructor
              · exact hs
              · simpa [native_reflist_contains] using hNot
            have hD2NoRef :=
              noRefSubDt_of_valid_no_free sub d2 (native_reflist_insert refs s2)
                hNot' hD2Valid hD2Free
            have hst : native_streq sub s2 = false := by
              simp [native_streq, hs]
            simp [native_or, hD2NoRef]
      case DatatypeTypeRef s2 =>
          rcases hUValid with ⟨hReserved, _hMem⟩
          have hFree' :
              native_or
                  (native_and (native_streq s2 sub) (native_not (native_reflist_contains refs sub)))
                  (hasFreeDtc sub refs (__eo_to_smt_datatype_cons c)) = false := by
            simpa [__eo_to_smt_datatype_cons, __eo_to_smt_type, native_ite, hReserved,
              hasFreeDtc] using hFree
          have hFreeSplit :
              native_and (native_streq s2 sub) (native_not (native_reflist_contains refs sub)) = false ∧
                hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false := by
            simpa [native_or, Bool.or_eq_false_iff] using hFree'
          have hTailFree : hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false := hTailFreeAll
          have hsne : s2 ≠ sub := by
            intro hs
            subst hs
            simp [native_and, native_not, hNot, native_streq] at hFreeSplit
          have hTail := noRefSubDtc_of_valid_no_free sub c refs hNot hTailValid hTailFree
          simp [hsne]
end

mutual
private theorem noRefSubDt_of_valid_cons_no_free (sub : native_String) :
    (W : Datatype) → (refs : RefList) →
      native_reflist_contains refs sub = false →
      eo_datatype_valid_rec (sub :: refs) W →
      hasFreeDt sub refs (__eo_to_smt_datatype W) = false →
      noRefSubDt sub W = true
  | Datatype.null, refs, hNot, hValid, hFree => by
      simp [noRefSubDt]
  | Datatype.sum c d, refs, hNot, hValid, hFree => by
      rcases hValid with ⟨hCValid, hDValid⟩
      simp only [__eo_to_smt_datatype, hasFreeDt, native_or, Bool.or_eq_false_iff] at hFree
      simp only [noRefSubDt, native_and, Bool.and_eq_true]
      exact ⟨noRefSubDtc_of_valid_cons_no_free sub c refs hNot hCValid hFree.1,
        noRefSubDt_of_valid_cons_no_free sub d refs hNot hDValid hFree.2⟩

private theorem noRefSubDtc_of_valid_cons_no_free (sub : native_String) :
    (c : DatatypeCons) → (refs : RefList) →
      native_reflist_contains refs sub = false →
      eo_datatype_cons_valid_rec (sub :: refs) c →
      hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false →
      noRefSubDtc sub c = true
  | DatatypeCons.unit, refs, hNot, hValid, hFree => by
      simp [noRefSubDtc]
  | DatatypeCons.cons U c, refs, hNot, hValid, hFree => by
      rcases hValid with ⟨hUValid, hCValid⟩
      have hTailFreeAll : hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false :=
        hasFreeDtc_tail_false_of_cons_false sub refs (__eo_to_smt_type U)
          (__eo_to_smt_datatype_cons c) (by
            simpa [__eo_to_smt_datatype_cons] using hFree)
      cases U <;> try
        (have hTail := noRefSubDtc_of_valid_cons_no_free sub c refs hNot hCValid hTailFreeAll
         simp [noRefSubDtc, native_and, native_not, native_teq, hTail])
      case DatatypeType s2 d2 =>
          rcases hUValid with ⟨hReserved, hD2Valid⟩
          have hFree' :
              hasFreeTy sub refs (__eo_to_smt_type (Term.DatatypeType s2 d2)) = false ∧
                hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false := by
            simpa [__eo_to_smt_datatype_cons, hasFreeDtc, native_or,
              Bool.or_eq_false_iff] using hFree
          have hD2Free :
              hasFreeDt sub (native_reflist_insert refs s2) (__eo_to_smt_datatype d2) = false := by
            simpa [__eo_to_smt_type, native_ite, hReserved, hasFreeTy] using hFree'.1
          have hTail := noRefSubDtc_of_valid_cons_no_free sub c refs hNot hCValid hFree'.2
          by_cases hs : sub = s2
          · subst hs
            simp [native_or]
          · have hNot' :
                native_reflist_contains (native_reflist_insert refs s2) sub = false := by
              simp [native_reflist_contains, native_reflist_insert, List.mem_cons]
              constructor
              · exact hs
              · simpa [native_reflist_contains] using hNot
            have hD2Swap : eo_datatype_valid_rec (sub :: s2 :: refs) d2 := by
              apply eo_datatype_valid_rec_weaken hD2Valid
              intro t ht
              simp at ht ⊢
              rcases ht with rfl | rfl | ht
              · exact Or.inr (Or.inl rfl)
              · exact Or.inl rfl
              · exact Or.inr (Or.inr ht)
            have hD2NoRef :=
              noRefSubDt_of_valid_cons_no_free sub d2
                (native_reflist_insert refs s2) hNot' hD2Swap hD2Free
            have hst : native_streq sub s2 = false := by
              simp [native_streq, hs]
            simp [native_or, hD2NoRef]
      case DatatypeTypeRef s2 =>
          rcases hUValid with ⟨hReserved, _hMem⟩
          have hFree' :
              native_or
                  (native_and (native_streq s2 sub) (native_not (native_reflist_contains refs sub)))
                  (hasFreeDtc sub refs (__eo_to_smt_datatype_cons c)) = false := by
            simpa [__eo_to_smt_datatype_cons, __eo_to_smt_type, native_ite, hReserved,
              hasFreeDtc] using hFree
          have hFreeSplit :
              native_and (native_streq s2 sub) (native_not (native_reflist_contains refs sub)) = false ∧
                hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false := by
            simpa [native_or, Bool.or_eq_false_iff] using hFree'
          have hsne : s2 ≠ sub := by
            intro hs
            subst hs
            simp [native_and, native_not, hNot, native_streq] at hFreeSplit
          have hTail := noRefSubDtc_of_valid_cons_no_free sub c refs hNot hCValid hTailFreeAll
          simp [hsne]
end

mutual
theorem eo_dt_substitute_noop (sub : native_String) (d0 : Datatype) :
    (W : Datatype) → noRefSubDt sub W = true → __eo_dt_substitute sub d0 W = W
  | Datatype.null, _ => by simp [__eo_dt_substitute]
  | Datatype.sum c d, h => by
      simp only [noRefSubDt, native_and, Bool.and_eq_true] at h
      simp only [__eo_dt_substitute]
      rw [eo_dtc_substitute_noop sub d0 c h.1, eo_dt_substitute_noop sub d0 d h.2]

theorem eo_dtc_substitute_noop (sub : native_String) (d0 : Datatype) :
    (c : DatatypeCons) → noRefSubDtc sub c = true → __eo_dtc_substitute sub d0 c = c
  | DatatypeCons.unit, _ => by simp [__eo_dtc_substitute]
  | DatatypeCons.cons U c, h => by
      cases U
      case DatatypeType s2 d2 =>
          simp only [noRefSubDtc, native_and, native_or, Bool.and_eq_true, Bool.or_eq_true] at h
          simp only [__eo_dtc_substitute]
          rw [eo_dtc_substitute_noop sub d0 c h.2]
          congr 2
          rcases h.1 with hsh | hns
          · rw [native_ite, if_pos hsh]
          · rw [native_ite]
            split
            · rfl
            · exact eo_dt_substitute_noop sub (__eo_dt_lift s2 d2 d0) d2 hns
      all_goals (
        simp only [noRefSubDtc, native_and, native_not, Bool.and_eq_true] at h
        simp only [__eo_dtc_substitute]
        rw [eo_dtc_substitute_noop sub d0 c h.2]
        try simp_all [native_ite, native_teq])
end

private theorem eo_to_smt_datatype_substitute_no_free
    (sub : native_String) (d0 W : Datatype) (refs : RefList)
    (hNot : native_reflist_contains refs sub = false)
    (hValid : eo_datatype_valid_rec refs W)
    (hFree : hasFreeDt sub refs (__eo_to_smt_datatype W) = false) :
    __eo_to_smt_datatype (__eo_dt_substitute sub d0 W) =
      __smtx_dt_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype W) := by
  have hNoRef : noRefSubDt sub W = true :=
    noRefSubDt_of_valid_no_free sub W refs hNot hValid hFree
  rw [eo_dt_substitute_noop sub d0 W hNoRef]
  exact (subst_noop_no_free_dt sub (__eo_to_smt_datatype W) (__eo_to_smt_datatype d0)
    refs hNot hFree).symm

private theorem eo_to_smt_datatype_cons_substitute_no_free
    (sub : native_String) (d0 : Datatype) (c : DatatypeCons) (refs : RefList)
    (hNot : native_reflist_contains refs sub = false)
    (hValid : eo_datatype_cons_valid_rec refs c)
    (hFree : hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false) :
    __eo_to_smt_datatype_cons (__eo_dtc_substitute sub d0 c) =
      __smtx_dtc_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype_cons c) := by
  have hNoRef : noRefSubDtc sub c = true :=
    noRefSubDtc_of_valid_no_free sub c refs hNot hValid hFree
  rw [eo_dtc_substitute_noop sub d0 c hNoRef]
  exact (subst_noop_no_free_dtc sub (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d0)
    refs hNot hFree).symm

private theorem eo_to_smt_datatype_substitute_cons_no_free
    (sub : native_String) (d0 W : Datatype) (refs : RefList)
    (hNot : native_reflist_contains refs sub = false)
    (hValid : eo_datatype_valid_rec (sub :: refs) W)
    (hFree : hasFreeDt sub refs (__eo_to_smt_datatype W) = false) :
    __eo_to_smt_datatype (__eo_dt_substitute sub d0 W) =
      __smtx_dt_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype W) := by
  have hNoRef : noRefSubDt sub W = true :=
    noRefSubDt_of_valid_cons_no_free sub W refs hNot hValid hFree
  rw [eo_dt_substitute_noop sub d0 W hNoRef]
  exact (subst_noop_no_free_dt sub (__eo_to_smt_datatype W) (__eo_to_smt_datatype d0)
    refs hNot hFree).symm

private theorem eo_to_smt_datatype_cons_substitute_cons_no_free
    (sub : native_String) (d0 : Datatype) (c : DatatypeCons) (refs : RefList)
    (hNot : native_reflist_contains refs sub = false)
    (hValid : eo_datatype_cons_valid_rec (sub :: refs) c)
    (hFree : hasFreeDtc sub refs (__eo_to_smt_datatype_cons c) = false) :
    __eo_to_smt_datatype_cons (__eo_dtc_substitute sub d0 c) =
      __smtx_dtc_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype_cons c) := by
  have hNoRef : noRefSubDtc sub c = true :=
    noRefSubDtc_of_valid_cons_no_free sub c refs hNot hValid hFree
  rw [eo_dtc_substitute_noop sub d0 c hNoRef]
  exact (subst_noop_no_free_dtc sub (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d0)
    refs hNot hFree).symm

private def eo_type_substitute_field (sub : native_String) (d0 : Datatype) : Term -> Term
  | Term.DatatypeType s2 d2 =>
      Term.DatatypeType s2 (native_ite (native_streq sub s2) d2
        (__eo_dt_substitute sub (__eo_dt_lift s2 d2 d0) d2))
  | T => native_ite (native_teq T (Term.DatatypeTypeRef sub)) (Term.DatatypeType sub d0) T

mutual

/- Do not fix this block by simply adding replacement-WF to every recursive call:
when substitution descends under `DatatypeType s d`, the replacement is EO-lifted by `s`,
and that lifted replacement can fail SMT WF even if the original replacement was WF.
The missing invariant is narrower: the lifted EO replacement must still translate like the
corresponding SMT lift, with tuple/non-`DatatypeType` interiors discharged by no-free/no-`Datatype sub`
no-op lemmas from `SmtFreeRefs`. -/
private theorem eo_to_smt_type_substitute_field
    (sub : native_String) (d0 : Datatype) :
    (T : Term) -> (refs : RefList) ->
      eo_datatype_valid_rec refs d0 ->
      noDtDt sub (__eo_to_smt_datatype d0) = true ->
      smtx_type_field_wf_rec (__eo_to_smt_type T) refs ->
      __eo_to_smt_type (eo_type_substitute_field sub d0 T) =
        smtx_type_substitute_top sub (__eo_to_smt_datatype d0) (__eo_to_smt_type T)
  | Term.DatatypeType s d, refs, hD0Valid, hD0NoDt, hField => by
      by_cases hEq : sub = s
      · subst hEq
        by_cases hRes : __eo_reserved_datatype_name sub = true
        · simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
            native_ite, native_streq, hRes]
        · simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
            native_ite, native_streq, hRes]
      · by_cases hRes : __eo_reserved_datatype_name s = true
        · simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
            native_ite, native_streq, hEq, hRes]
        · simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
            native_ite, native_streq, hEq, hRes]
          have hTypeWf :
              __smtx_type_wf_rec (SmtType.Datatype s (__eo_to_smt_datatype d)) refs = true := by
            simpa [__eo_to_smt_type, native_ite, hRes, smtx_type_field_wf_rec] using hField
          have hDtWf :
              __smtx_dt_wf_rec (__eo_to_smt_datatype d)
                (native_reflist_insert refs s) = true :=
            (smtx_datatype_type_wf_rec_parts_local hTypeWf).2
          have hD0ValidWeak :
              eo_datatype_valid_rec (native_reflist_insert refs s) d0 := by
            apply eo_datatype_valid_rec_weaken hD0Valid
            intro t ht
            simp [native_reflist_insert]
            exact Or.inr ht
          have hD0LiftValid :
              eo_datatype_valid_rec (native_reflist_insert refs s)
                (__eo_dt_lift s d d0) := by
            have hMem : s ∈ native_reflist_insert refs s := by
              simp [native_reflist_insert]
            exact eo_datatype_lift_preserves_valid s d hMem hD0ValidWeak
          have hD0LiftNoDt :
              noDtDt sub
                  (__eo_to_smt_datatype (__eo_dt_lift s d d0)) = true :=
            eo_lift_preserves_noDt_dt s sub d d0 hD0NoDt
          rw [eo_to_smt_datatype_substitute sub (__eo_dt_lift s d d0) d
            (native_reflist_insert refs s) hD0LiftValid hD0LiftNoDt hDtWf]
          by_cases hFree :
              hasFreeDt sub (native_reflist_insert native_reflist_nil s)
                (__eo_to_smt_datatype d) = true
          · have hContains :
                native_reflist_contains (native_reflist_insert refs s) sub = true := by
              by_cases hContains :
                  native_reflist_contains (native_reflist_insert refs s) sub = true
              · exact hContains
              · have hContainsFalse :
                    native_reflist_contains (native_reflist_insert refs s) sub = false := by
                  cases h :
                      native_reflist_contains (native_reflist_insert refs s) sub <;>
                    simp [h] at hContains ⊢
                have hFreeFalseAtRefs :
                    hasFreeDt sub (native_reflist_insert refs s) (__eo_to_smt_datatype d) = false :=
                  hasFreeDt_eq_false_of_wf sub (__eo_to_smt_datatype d)
                    (native_reflist_insert refs s) hDtWf
                have hNilContains :
                    native_reflist_contains (native_reflist_insert native_reflist_nil s) sub =
                      false := by
                  simp [native_reflist_contains, native_reflist_insert,
                    native_reflist_nil, hEq]
                have hFreeAtRefs :
                    hasFreeDt sub (native_reflist_insert refs s) (__eo_to_smt_datatype d) = true := by
                  rw [hasFreeDt_refs_irrel sub (__eo_to_smt_datatype d)
                    (native_reflist_insert refs s)
                    (native_reflist_insert native_reflist_nil s)]
                  · exact hFree
                  · rw [hContainsFalse, hNilContains]
                rw [hFreeFalseAtRefs] at hFreeAtRefs
                exact False.elim (by cases hFreeAtRefs)
            have hContainsRefs : native_reflist_contains refs sub = true := by
              have hMem : sub ∈ refs := by
                simpa [native_reflist_contains, native_reflist_insert, hEq] using hContains
              simpa [native_reflist_contains] using hMem
            have hDValid :
                eo_datatype_valid_rec (s :: refs) d := by
              simpa [native_reflist_insert] using
                eo_datatype_valid_of_smt_wf_rec (native_reflist_insert refs s) hDtWf
            rw [eo_to_smt_dt_lift_of_valid_noDt s sub d hEq hFree d0 refs
              hDValid hD0Valid hD0NoDt]
          · have hFreeFalse :
                hasFreeDt sub (native_reflist_insert native_reflist_nil s)
                  (__eo_to_smt_datatype d) = false := by
              cases h :
                  hasFreeDt sub (native_reflist_insert native_reflist_nil s)
                    (__eo_to_smt_datatype d) <;>
                simp [h] at hFree ⊢
            have hNot :
                native_reflist_contains (native_reflist_insert native_reflist_nil s) sub =
                  false := by
              simp [native_reflist_contains, native_reflist_insert,
                native_reflist_nil, hEq]
            have hLeft :=
              subst_noop_no_free_dt sub (__eo_to_smt_datatype d)
                (__eo_to_smt_datatype (__eo_dt_lift s d d0))
                (native_reflist_insert native_reflist_nil s) hNot hFreeFalse
            have hRight :=
              subst_noop_no_free_dt sub (__eo_to_smt_datatype d)
                (__smtx_dt_lift s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d0))
                (native_reflist_insert native_reflist_nil s) hNot hFreeFalse
            rw [hLeft, hRight]
  | Term.DatatypeTypeRef s, refs, hD0Valid, hD0NoDt, hField => by
      by_cases hEq : s = sub
      · subst hEq
        by_cases hRes : __eo_reserved_datatype_name s = true
        · simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
            native_ite, native_teq, hRes]
        · simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
            native_ite, native_teq, native_streq, hRes]
      · have hNe : sub ≠ s := by intro hs; exact hEq hs.symm
        by_cases hRes : __eo_reserved_datatype_name s = true
        · simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
            native_ite, native_teq, hEq, hRes]
        simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
          native_ite, native_teq, native_streq, hEq, hNe, hRes]
  | Term.UOp op, refs, hD0Valid, hD0NoDt, hField => by
      cases op
      case UnitTuple =>
        let tupleTy := SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
        have hNoop : smtx_type_substitute_top sub (__eo_to_smt_datatype d0) tupleTy = tupleTy := by
          exact smtx_type_substitute_top_of_wf_rec sub (__eo_to_smt_datatype d0) tupleTy
            native_reflist_nil (by rfl)
            (by simp [tupleTy, __smtx_type_wf_rec, __smtx_dt_wf_rec,
              __smtx_dt_cons_wf_rec, native_reflist_contains, native_reflist_nil,
              native_ite])
        change tupleTy = smtx_type_substitute_top sub (__eo_to_smt_datatype d0) tupleTy
        exact hNoop.symm
      all_goals
        rfl
  | Term.Apply f x, refs, hD0Valid, hD0NoDt, hField => by
      cases f
      case UOp op =>
        cases op
        case BitVec =>
          cases x <;> simp [eo_type_substitute_field, smtx_type_substitute_top,
            __eo_to_smt_type, native_ite, native_teq]
          case Numeral n =>
            cases h : native_zleq 0 n <;>
              rfl
        case Seq =>
          change
            __smtx_typeof_guard (__eo_to_smt_type x) (SmtType.Seq (__eo_to_smt_type x)) =
              smtx_type_substitute_top sub (__eo_to_smt_datatype d0)
                (__smtx_typeof_guard (__eo_to_smt_type x) (SmtType.Seq (__eo_to_smt_type x)))
          exact (smtx_type_substitute_top_of_guard sub (__eo_to_smt_datatype d0)
            (__eo_to_smt_type x) (SmtType.Seq (__eo_to_smt_type x))
            (by simp [smtx_type_substitute_top])).symm
        case Set =>
          change
            __smtx_typeof_guard (__eo_to_smt_type x) (SmtType.Set (__eo_to_smt_type x)) =
              smtx_type_substitute_top sub (__eo_to_smt_datatype d0)
                (__smtx_typeof_guard (__eo_to_smt_type x) (SmtType.Set (__eo_to_smt_type x)))
          exact (smtx_type_substitute_top_of_guard sub (__eo_to_smt_datatype d0)
            (__eo_to_smt_type x) (SmtType.Set (__eo_to_smt_type x))
            (by simp [smtx_type_substitute_top])).symm
        all_goals
          simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
            native_ite, native_teq]
      case Apply f1 x1 =>
        cases f1
        case FunType =>
          let inner := __smtx_typeof_guard (__eo_to_smt_type x)
            (native_ite
              (__smtx_is_finite_type
                (SmtType.FunType (__eo_to_smt_type x1) (__eo_to_smt_type x)))
              (SmtType.FunType (__eo_to_smt_type x1) (__eo_to_smt_type x))
              (SmtType.FunType (__eo_to_smt_type x1) (__eo_to_smt_type x)))
          have hInner : smtx_type_substitute_top sub (__eo_to_smt_datatype d0) inner = inner := by
            exact smtx_type_substitute_top_of_guard sub (__eo_to_smt_datatype d0)
              (__eo_to_smt_type x)
              (native_ite
                (__smtx_is_finite_type
                  (SmtType.FunType (__eo_to_smt_type x1) (__eo_to_smt_type x)))
                (SmtType.FunType (__eo_to_smt_type x1) (__eo_to_smt_type x))
                (SmtType.FunType (__eo_to_smt_type x1) (__eo_to_smt_type x)))
              (by
                cases hFin :
                    __smtx_is_finite_type
                      (SmtType.FunType (__eo_to_smt_type x1) (__eo_to_smt_type x)) <;>
                  simp [smtx_type_substitute_top, native_ite])
          change
            __smtx_typeof_guard (__eo_to_smt_type x1) inner =
              smtx_type_substitute_top sub (__eo_to_smt_datatype d0)
                (__smtx_typeof_guard (__eo_to_smt_type x1) inner)
          exact (smtx_type_substitute_top_of_guard sub (__eo_to_smt_datatype d0)
            (__eo_to_smt_type x1) inner hInner).symm
        case UOp op =>
          cases op
          case Array =>
            let inner := __smtx_typeof_guard (__eo_to_smt_type x)
              (SmtType.Map (__eo_to_smt_type x1) (__eo_to_smt_type x))
            have hInner : smtx_type_substitute_top sub (__eo_to_smt_datatype d0) inner = inner := by
              exact smtx_type_substitute_top_of_guard sub (__eo_to_smt_datatype d0)
                (__eo_to_smt_type x) (SmtType.Map (__eo_to_smt_type x1) (__eo_to_smt_type x))
                (by simp [smtx_type_substitute_top])
            change
              __smtx_typeof_guard (__eo_to_smt_type x1) inner =
                smtx_type_substitute_top sub (__eo_to_smt_datatype d0)
                  (__smtx_typeof_guard (__eo_to_smt_type x1) inner)
            exact (smtx_type_substitute_top_of_guard sub (__eo_to_smt_datatype d0)
              (__eo_to_smt_type x1) inner hInner).symm
          case Tuple =>
            let raw := __eo_to_smt_type_tuple (__eo_to_smt_type x1) (__eo_to_smt_type x)
            cases hWf : __smtx_type_wf raw with
            | false =>
                simp [raw, eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
                  native_ite, native_teq, hWf]
            | true =>
                simp [raw, eo_type_substitute_field, __eo_to_smt_type,
                  native_ite, native_teq, hWf]
                exact (smtx_type_substitute_top_of_wf_rec sub (__eo_to_smt_datatype d0) raw
                  native_reflist_nil (by rfl)
                  (smtx_type_wf_rec_of_type_wf
                    (eo_to_smt_type_tuple_ne_reglan (__eo_to_smt_type x1) (__eo_to_smt_type x))
                    (by
                      intro A B
                      exact eo_to_smt_type_tuple_ne_fun (__eo_to_smt_type x1) (__eo_to_smt_type x) A B)
                    (by
                      intro A B
                      exact eo_to_smt_type_tuple_ne_ifun (__eo_to_smt_type x1) (__eo_to_smt_type x) A B)
                    hWf)).symm
          all_goals
            simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
              native_ite, native_teq]
        all_goals
          simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
            native_ite, native_teq]
      all_goals
        simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type,
          native_ite, native_teq]
  | Term.DtcAppType A B, refs, hD0Valid, hD0NoDt, hField => by
      let inner := __smtx_typeof_guard (__eo_to_smt_type B)
        (SmtType.DtcAppType (__eo_to_smt_type A) (__eo_to_smt_type B))
      have hInner : smtx_type_substitute_top sub (__eo_to_smt_datatype d0) inner = inner := by
        exact smtx_type_substitute_top_of_guard sub (__eo_to_smt_datatype d0)
          (__eo_to_smt_type B) (SmtType.DtcAppType (__eo_to_smt_type A) (__eo_to_smt_type B))
          (by simp [smtx_type_substitute_top])
      change
        __smtx_typeof_guard (__eo_to_smt_type A) inner =
          smtx_type_substitute_top sub (__eo_to_smt_datatype d0)
            (__smtx_typeof_guard (__eo_to_smt_type A) inner)
      exact (smtx_type_substitute_top_of_guard sub (__eo_to_smt_datatype d0)
        (__eo_to_smt_type A) inner hInner).symm
  | Term.__eo_List, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.__eo_List_nil, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.__eo_List_cons, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.Bool, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.Boolean b, refs, hD0Valid, hD0NoDt, hField => by cases b <;> simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.Numeral n, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.Rational q, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.String s, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.Binary w n, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.Type, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.Stuck, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.FunType, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.Var name T, refs, hD0Valid, hD0NoDt, hField => by cases name <;> simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.DtCons s d i, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.DtSel s d i j, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.USort i, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UConst i T, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.repeat x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.zero_extend x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.sign_extend x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.rotate_left x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.rotate_right x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1._at_bit x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.re_exp x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.is x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.update x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.tuple_select x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.tuple_update x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.int_to_bv x, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp2 UserOp2.extract x y, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp2 UserOp2._at_bv x y, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp2 UserOp2.re_loop x y, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.seq_empty T, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp1 UserOp1.set_empty T, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp2 UserOp2._at_quantifiers_skolemize x y, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp2 UserOp2._at_const x y, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp3 UserOp3._at_re_unfold_pos_component x y z, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]
  | Term.UOp3 UserOp3._at_witness_string_length x y z, refs, hD0Valid, hD0NoDt, hField => by simp [eo_type_substitute_field, smtx_type_substitute_top, __eo_to_smt_type, native_ite, native_teq]

private theorem eo_to_smt_datatype_cons_substitute
    (sub : native_String) (d0 : Datatype) :
    (c : DatatypeCons) -> (refs : RefList) ->
      eo_datatype_valid_rec refs d0 ->
      noDtDt sub (__eo_to_smt_datatype d0) = true ->
      __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true ->
      __eo_to_smt_datatype_cons (__eo_dtc_substitute sub d0 c) =
        __smtx_dtc_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype_cons c)
  | DatatypeCons.unit, refs, hD0Valid, hD0NoDt, hWf => by rfl
  | DatatypeCons.cons U c, refs, hD0Valid, hD0NoDt, hWf => by
      have hField :
          smtx_type_field_wf_rec (__eo_to_smt_type U) refs :=
        smtx_type_field_wf_rec_of_cons_wf (by
          simpa [__eo_to_smt_datatype_cons] using hWf)
      have hTail :
          __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true :=
        smtx_dt_cons_wf_rec_tail_of_true (by
          simpa [__eo_to_smt_datatype_cons] using hWf)
      rw [show __eo_dtc_substitute sub d0 (DatatypeCons.cons U c) =
          DatatypeCons.cons (eo_type_substitute_field sub d0 U) (__eo_dtc_substitute sub d0 c) by
        cases U <;> rfl]
      simp [__eo_to_smt_datatype_cons,
        eo_to_smt_datatype_cons_substitute sub d0 c refs hD0Valid hD0NoDt hTail,
        smtx_dtc_substitute_cons_eq,
        eo_to_smt_type_substitute_field sub d0 U refs hD0Valid hD0NoDt hField]

theorem eo_to_smt_datatype_substitute
    (sub : native_String) (d0 : Datatype) :
    (d : Datatype) -> (refs : RefList) ->
      eo_datatype_valid_rec refs d0 ->
      noDtDt sub (__eo_to_smt_datatype d0) = true ->
      __smtx_dt_wf_rec (__eo_to_smt_datatype d) refs = true ->
      __eo_to_smt_datatype (__eo_dt_substitute sub d0 d) =
        __smtx_dt_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype d)
  | Datatype.null, refs, hD0Valid, hD0NoDt, hWf => by rfl
  | Datatype.sum c d, refs, hD0Valid, hD0NoDt, hWf => by
      have hCons :
          __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true :=
        by
          cases hC : __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs <;>
            cases d <;>
              simp [__eo_to_smt_datatype, __smtx_dt_wf_rec, native_ite, hC] at hWf ⊢
      cases d with
      | null =>
          simp [__eo_dt_substitute, __eo_to_smt_datatype, __smtx_dt_substitute,
            eo_to_smt_datatype_cons_substitute sub d0 c refs hD0Valid hD0NoDt hCons]
      | sum cTail dTail =>
          have hTail :
              __smtx_dt_wf_rec (__eo_to_smt_datatype (Datatype.sum cTail dTail)) refs = true := by
            have hCons' :
                __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true := hCons
            simpa [__eo_to_smt_datatype, __smtx_dt_wf_rec, native_ite, hCons'] using hWf
          have hConsSub :=
            eo_to_smt_datatype_cons_substitute sub d0 c refs hD0Valid hD0NoDt hCons
          have hTailSub :=
            eo_to_smt_datatype_substitute sub d0 (Datatype.sum cTail dTail) refs
              hD0Valid hD0NoDt hTail
          change
            SmtDatatype.sum
                (__eo_to_smt_datatype_cons (__eo_dtc_substitute sub d0 c))
                (__eo_to_smt_datatype
                  (__eo_dt_substitute sub d0 (Datatype.sum cTail dTail))) =
              SmtDatatype.sum
                (__smtx_dtc_substitute sub (__eo_to_smt_datatype d0)
                  (__eo_to_smt_datatype_cons c))
                (__smtx_dt_substitute sub (__eo_to_smt_datatype d0)
                  (__eo_to_smt_datatype (Datatype.sum cTail dTail)))
          rw [hConsSub, hTailSub]

end

/-- Selector return translation after expanding the datatype's recursive self-reference. -/
theorem eo_to_smt_typeof_dt_sel_return_substitute_self
    (s : native_String) (d : Datatype) (i j : native_Nat)
    (hWf :
      __smtx_dt_wf_rec (__eo_to_smt_datatype d)
        (native_reflist_insert native_reflist_nil s) = true) :
    __eo_to_smt_type (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  rw [eo_to_smt_typeof_dt_sel_return]
  have hDValid :
      eo_datatype_valid_rec (native_reflist_insert native_reflist_nil s) d :=
    eo_datatype_valid_of_smt_wf_rec (native_reflist_insert native_reflist_nil s) hWf
  have hDNoDt :
      noDtDt s (__eo_to_smt_datatype d) = true :=
    noDt_of_wf_dt s (__eo_to_smt_datatype d)
      (native_reflist_insert native_reflist_nil s) hWf
      (by simp [native_reflist_contains, native_reflist_insert, native_reflist_nil])
  rw [eo_to_smt_datatype_substitute s d d (native_reflist_insert native_reflist_nil s)
    hDValid hDNoDt hWf]
  rfl

theorem eo_to_smt_type_typeof_dt_cons_of_valid
    (s : native_String) (d : Datatype) (i : native_Nat)
    (hReserved : __eo_reserved_datatype_name s = false)
    (hValid : eo_datatype_valid_rec [s] d)
    (hNN : __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) ∧
    eo_type_valid_rec [] (__eo_typeof (Term.DtCons s d i)) := by
  let D : SmtType := SmtType.Datatype s (__eo_to_smt_datatype d)
  let inner : SmtType :=
    __smtx_typeof_dt_cons_rec D
      (__smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d)) i
  have hGuardNN : __smtx_typeof_guard_wf D inner ≠ SmtType.None := by
    simpa [D, inner, Smtm.typeof_dt_cons_eq] using hNN
  have hInnerEq :
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) = inner := by
    have hGuard : __smtx_typeof_guard_wf D inner = inner :=
      smtx_typeof_guard_wf_of_non_none D inner hGuardNN
    simpa [D, inner, Smtm.typeof_dt_cons_eq] using hGuard
  have hInnerNN : inner ≠ SmtType.None := by
    rw [← hInnerEq]
    exact hNN
  have hTyValid : eo_type_valid_rec [] (Term.DatatypeType s d) :=
    ⟨hReserved, hValid⟩
  have hSubValid : eo_datatype_valid_rec [] (__eo_dt_substitute s d d) :=
    eo_datatype_valid_rec_substitute s d [] hValid hValid
  have hSubEq :
      __eo_to_smt_datatype (__eo_dt_substitute s d d) =
        __smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d) :=
    by
      have hBaseTypeWf : __smtx_type_wf D = true :=
        Smtm.smtx_typeof_guard_wf_wf_of_non_none D inner hGuardNN
      have hBaseDtWf :
          __smtx_dt_wf_rec (__eo_to_smt_datatype d)
            (native_reflist_insert native_reflist_nil s) = true :=
        datatype_wf_rec_of_type_wf hBaseTypeWf
      have hBaseNoDt :
          noDtDt s (__eo_to_smt_datatype d) = true :=
        noDt_of_wf_dt s (__eo_to_smt_datatype d)
          (native_reflist_insert native_reflist_nil s) hBaseDtWf
          (by simp [native_reflist_contains, native_reflist_insert, native_reflist_nil])
      exact eo_to_smt_datatype_substitute s d d
        (native_reflist_insert native_reflist_nil s) hValid hBaseNoDt hBaseDtWf
  have hRec :=
    eo_to_smt_type_typeof_dt_cons_rec_of_valid (T := Term.DatatypeType s d) hTyValid
      hSubValid
      (by
        simpa [D, inner, __eo_to_smt_type, hReserved, native_ite, hSubEq] using hInnerNN)
  refine ⟨?_, ?_⟩
  · have hRec' :
        __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = inner := by
      change
        __eo_to_smt_type
            (__eo_typeof_dt_cons_rec (Term.DatatypeType s d) (__eo_dt_substitute s d d) i) =
          inner
      have hRhs :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type (Term.DatatypeType s d))
              (__eo_to_smt_datatype (__eo_dt_substitute s d d)) i =
            inner := by
        simp [D, inner, __eo_to_smt_type, hReserved, native_ite, hSubEq]
      exact hRec.1.trans hRhs
    exact hRec'.trans hInnerEq.symm
  · change
      eo_type_valid_rec []
        (__eo_typeof_dt_cons_rec (Term.DatatypeType s d) (__eo_dt_substitute s d d) i)
    exact hRec.2

private theorem eo_typeof_dt_cons_rec_null (T : Term) (i : native_Nat) :
    __eo_typeof_dt_cons_rec T Datatype.null i = Term.Stuck := by
  rw [__eo_typeof_dt_cons_rec.eq_def]
  cases T <;> cases i <;> simp

private theorem eo_typeof_dt_cons_rec_unit (T : Term) (d : Datatype) (hT : T ≠ Term.Stuck) :
    __eo_typeof_dt_cons_rec T (Datatype.sum DatatypeCons.unit d) native_nat_zero = T := by
  rw [__eo_typeof_dt_cons_rec.eq_def]
  cases T <;> simp at hT ⊢

private theorem eo_typeof_dt_cons_rec_cons (T U : Term) (c : DatatypeCons) (d : Datatype) (hT : T ≠ Term.Stuck) :
    __eo_typeof_dt_cons_rec T (Datatype.sum (DatatypeCons.cons U c) d) native_nat_zero =
      Term.DtcAppType U (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero) := by
  rw [__eo_typeof_dt_cons_rec.eq_def]
  cases T <;> simp at hT ⊢

private theorem eo_typeof_dt_cons_rec_succ (T : Term) (c : DatatypeCons) (d : Datatype) (n : native_Nat) (hT : T ≠ Term.Stuck) :
    __eo_typeof_dt_cons_rec T (Datatype.sum c d) (native_nat_succ n) =
      __eo_typeof_dt_cons_rec T d n := by
  rw [__eo_typeof_dt_cons_rec.eq_def]
  cases T <;> simp at hT ⊢

private theorem smtx_typeof_dt_cons_rec_null (T : SmtType) (i : native_Nat) :
    __smtx_typeof_dt_cons_rec T SmtDatatype.null i = SmtType.None := by
  rw [__smtx_typeof_dt_cons_rec.eq_def]

private theorem smtx_typeof_dt_cons_rec_unit (T : SmtType) (d : SmtDatatype) :
    __smtx_typeof_dt_cons_rec T (SmtDatatype.sum SmtDatatypeCons.unit d) native_nat_zero = T := by
  rw [__smtx_typeof_dt_cons_rec.eq_1]

private theorem smtx_typeof_dt_cons_rec_cons (T U : SmtType) (c : SmtDatatypeCons) (d : SmtDatatype) :
    __smtx_typeof_dt_cons_rec T (SmtDatatype.sum (SmtDatatypeCons.cons U c) d) native_nat_zero =
      SmtType.DtcAppType U (__smtx_typeof_dt_cons_rec T (SmtDatatype.sum c d) native_nat_zero) := by
  rw [__smtx_typeof_dt_cons_rec.eq_2]

private theorem smtx_typeof_dt_cons_rec_succ (T : SmtType) (c : SmtDatatypeCons) (d : SmtDatatype) (n : native_Nat) :
    __smtx_typeof_dt_cons_rec T (SmtDatatype.sum c d) (native_nat_succ n) =
      __smtx_typeof_dt_cons_rec T d n := by
  rw [__smtx_typeof_dt_cons_rec.eq_3]

private theorem smtx_dt_wf_tail_of_sum_wf
    (c : SmtDatatypeCons) (d : SmtDatatype) (refs : RefList)
    (hTail : d ≠ SmtDatatype.null)
    (hWf : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_wf_rec d refs = true := by
  cases d with
  | null =>
      exact False.elim (hTail rfl)
  | sum cTail dTail =>
      have hCons : __smtx_dt_cons_wf_rec c refs = true := by
        cases hC : __smtx_dt_cons_wf_rec c refs <;>
          simp [__smtx_dt_wf_rec, native_ite, hC] at hWf ⊢
      simpa [__smtx_dt_wf_rec, native_ite, hCons] using hWf

private theorem smtx_dt_cons_wf_of_sum_wf
    (c : SmtDatatypeCons) (d : SmtDatatype) (refs : RefList)
    (hWf : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases hC : __smtx_dt_cons_wf_rec c refs <;>
    cases d <;> simp [__smtx_dt_wf_rec, native_ite, hC] at hWf ⊢

private theorem smtx_dt_cons_tail_wf_of_wf_rec
    (U : SmtType) (c : SmtDatatypeCons) (refs : RefList)
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons U c) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  exact smtx_dt_cons_wf_rec_tail_of_true hWf

private theorem smtx_type_substitute_top_ne_none_of_cons_wf
    (sub : native_String) (d0 : SmtDatatype) (U : SmtType) (c : SmtDatatypeCons) (refs : RefList)
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons U c) refs = true) :
    smtx_type_substitute_top sub d0 U ≠ SmtType.None := by
  cases U <;> simp [smtx_type_substitute_top, __smtx_dt_cons_wf_rec,
    __smtx_type_wf_rec, native_ite] at hWf ⊢
  case TypeRef s =>
    by_cases hEq : sub = s <;>
      simp [hEq]

private theorem smtx_typeof_dt_cons_rec_zero_subst_ne_none
    (sub : native_String) (d0 : SmtDatatype) (T : SmtType) (hT : T ≠ SmtType.None) :
    (c : SmtDatatypeCons) -> (d : SmtDatatype) ->
      __smtx_typeof_dt_cons_rec T
          (SmtDatatype.sum (__smtx_dtc_substitute sub d0 c) (__smtx_dt_substitute sub d0 d))
          native_nat_zero ≠ SmtType.None
  | SmtDatatypeCons.unit, d => by
      simp [__smtx_dtc_substitute, smtx_typeof_dt_cons_rec_unit, hT]
  | SmtDatatypeCons.cons U c, d => by
      rw [smtx_dtc_substitute_cons_eq, smtx_typeof_dt_cons_rec_cons]
      simp

private theorem eo_to_smt_typeof_dt_cons_rec_substitute_of_wf
    (sub : native_String) (d0 : Datatype) (T : Term) (hT : __eo_to_smt_type T ≠ SmtType.None) :
    (d : Datatype) -> (i : native_Nat) -> (refs : RefList) ->
      native_reflist_contains refs sub = true ->
      __smtx_dt_wf_rec (__eo_to_smt_datatype d0) refs = true ->
      __smtx_dt_wf_rec (__eo_to_smt_datatype d) refs = true ->
      __eo_to_smt_type (__eo_typeof_dt_cons_rec T (__eo_dt_substitute sub d0 d) i) =
        __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
          (__smtx_dt_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype d)) i
  | Datatype.null, i, refs, hContains, hD0Wf, hWf => by
      rw [__eo_dt_substitute, __smtx_dt_substitute.eq_def, eo_typeof_dt_cons_rec_null]
      change SmtType.None = __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) SmtDatatype.null i
      rw [smtx_typeof_dt_cons_rec_null]
  | Datatype.sum DatatypeCons.unit d, native_nat_zero, refs, hContains, hD0Wf, hWf => by
      have hTTerm : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
      rw [__eo_dt_substitute, __smtx_dt_substitute.eq_def, __eo_dtc_substitute,
        eo_typeof_dt_cons_rec_unit T (__eo_dt_substitute sub d0 d) hTTerm]
      change __eo_to_smt_type T =
        __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
          (SmtDatatype.sum SmtDatatypeCons.unit
            (__smtx_dt_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype d))) native_nat_zero
      rw [smtx_typeof_dt_cons_rec_unit]
  | Datatype.sum (DatatypeCons.cons U c) d, native_nat_zero, refs, hContains, hD0Wf, hWf => by
      have hTTerm : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
      rw [__eo_dt_substitute, __smtx_dt_substitute.eq_def]
      rw [show __eo_dtc_substitute sub d0 (DatatypeCons.cons U c) =
          DatatypeCons.cons (eo_type_substitute_field sub d0 U) (__eo_dtc_substitute sub d0 c) by
        cases U <;> rfl]
      rw [eo_typeof_dt_cons_rec_cons T (eo_type_substitute_field sub d0 U)
        (__eo_dtc_substitute sub d0 c) (__eo_dt_substitute sub d0 d) hTTerm]
      change __eo_to_smt_type
          (Term.DtcAppType (eo_type_substitute_field sub d0 U)
            (__eo_typeof_dt_cons_rec T (Datatype.sum (__eo_dtc_substitute sub d0 c)
              (__eo_dt_substitute sub d0 d)) native_nat_zero)) =
        __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
          (SmtDatatype.sum
            (__smtx_dtc_substitute sub (__eo_to_smt_datatype d0)
              (SmtDatatypeCons.cons (__eo_to_smt_type U) (__eo_to_smt_datatype_cons c)))
            (__smtx_dt_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype d)))
          native_nat_zero
      rw [smtx_dtc_substitute_cons_eq, smtx_typeof_dt_cons_rec_cons]
      let cSmt := __eo_to_smt_datatype_cons c
      let dSmt := __eo_to_smt_datatype d
      let d0Smt := __eo_to_smt_datatype d0
      have hCons : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons (__eo_to_smt_type U) cSmt) refs = true := by
        exact smtx_dt_cons_wf_of_sum_wf _ _ refs (by simpa [cSmt, dSmt] using hWf)
      have hFieldNN : smtx_type_substitute_top sub d0Smt (__eo_to_smt_type U) ≠ SmtType.None :=
        smtx_type_substitute_top_ne_none_of_cons_wf sub d0Smt (__eo_to_smt_type U) cSmt refs hCons
      have hTailCons : __smtx_dt_cons_wf_rec cSmt refs = true :=
        smtx_dt_cons_tail_wf_of_wf_rec (__eo_to_smt_type U) cSmt refs hCons
      have hTailWf : __smtx_dt_wf_rec (__eo_to_smt_datatype (Datatype.sum c d)) refs = true := by
        by_cases hDnull : dSmt = SmtDatatype.null
        · simp [__eo_to_smt_datatype, __smtx_dt_wf_rec, cSmt, dSmt, hDnull,
            hTailCons]
        · have hDtTail : __smtx_dt_wf_rec dSmt refs = true :=
            smtx_dt_wf_tail_of_sum_wf _ _ refs hDnull (by simpa [cSmt, dSmt] using hWf)
          simp [__eo_to_smt_datatype, __smtx_dt_wf_rec, cSmt, dSmt, hTailCons,
            hDtTail, native_ite]
      have hRec := eo_to_smt_typeof_dt_cons_rec_substitute_of_wf sub d0 T hT
        (Datatype.sum c d) native_nat_zero refs hContains hD0Wf hTailWf
      have hRestNN :
          __eo_to_smt_type
              (__eo_typeof_dt_cons_rec T (__eo_dt_substitute sub d0 (Datatype.sum c d)) native_nat_zero) ≠
            SmtType.None := by
        rw [hRec]
        exact smtx_typeof_dt_cons_rec_zero_subst_ne_none sub d0Smt (__eo_to_smt_type T) hT cSmt dSmt
      rw [eo_to_smt_type_dtc_app]
      have hD0Valid : eo_datatype_valid_rec refs d0 :=
        eo_datatype_valid_of_smt_wf_rec refs hD0Wf
      have hD0NoDt : noDtDt sub (__eo_to_smt_datatype d0) = true :=
        noDt_of_wf_dt sub (__eo_to_smt_datatype d0) refs hD0Wf hContains
      rw [eo_to_smt_type_substitute_field sub d0 U refs hD0Valid hD0NoDt
        (smtx_type_field_wf_rec_of_cons_wf hCons)]
      change
        __smtx_typeof_guard (smtx_type_substitute_top sub d0Smt (__eo_to_smt_type U))
          (__smtx_typeof_guard
            (__eo_to_smt_type (__eo_typeof_dt_cons_rec T (__eo_dt_substitute sub d0 (Datatype.sum c d)) native_nat_zero))
            (SmtType.DtcAppType (smtx_type_substitute_top sub d0Smt (__eo_to_smt_type U))
              (__eo_to_smt_type (__eo_typeof_dt_cons_rec T (__eo_dt_substitute sub d0 (Datatype.sum c d)) native_nat_zero)))) =
          SmtType.DtcAppType (smtx_type_substitute_top sub d0Smt (__eo_to_smt_type U))
            (__smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
              (SmtDatatype.sum (__smtx_dtc_substitute sub d0Smt cSmt) (__smtx_dt_substitute sub d0Smt dSmt)) native_nat_zero)
      rw [smtx_typeof_guard_of_non_none _ _ hFieldNN,
        smtx_typeof_guard_of_non_none _ _ hRestNN, hRec]
      rfl
  | Datatype.sum c d, native_nat_succ n, refs, hContains, hD0Wf, hWf => by
      have hTTerm : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
      rw [__eo_dt_substitute, __smtx_dt_substitute.eq_def]
      rw [eo_typeof_dt_cons_rec_succ T (__eo_dtc_substitute sub d0 c)
        (__eo_dt_substitute sub d0 d) n hTTerm]
      change __eo_to_smt_type (__eo_typeof_dt_cons_rec T (__eo_dt_substitute sub d0 d) n) =
        __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
          (SmtDatatype.sum (__smtx_dtc_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype_cons c))
            (__smtx_dt_substitute sub (__eo_to_smt_datatype d0) (__eo_to_smt_datatype d))) (native_nat_succ n)
      rw [smtx_typeof_dt_cons_rec_succ]
      cases d with
      | null =>
          simp [__eo_dt_substitute, __smtx_dt_substitute, eo_typeof_dt_cons_rec_null,
            smtx_typeof_dt_cons_rec_null, __eo_to_smt_type]
      | sum cTail dTail =>
          have hDtTail :
              __smtx_dt_wf_rec (__eo_to_smt_datatype (Datatype.sum cTail dTail)) refs = true := by
            exact smtx_dt_wf_tail_of_sum_wf _ _ refs (by simp [__eo_to_smt_datatype])
              (by simpa [__eo_to_smt_datatype] using hWf)
          exact eo_to_smt_typeof_dt_cons_rec_substitute_of_wf sub d0 T hT
            (Datatype.sum cTail dTail) n refs hContains hD0Wf hDtTail

theorem eo_to_smt_type_typeof_dt_cons
    (s : native_String) (d : Datatype) (i : native_Nat)
    (hReserved : __eo_reserved_datatype_name s = false)
    (hNN : __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) := by
  let dSmt := __eo_to_smt_datatype d
  let raw := __smtx_typeof_dt_cons_rec (SmtType.Datatype s dSmt)
    (__smtx_dt_substitute s dSmt dSmt) i
  have hGuardNN : __smtx_typeof_guard_wf (SmtType.Datatype s dSmt) raw ≠ SmtType.None := by
    simpa [dSmt, raw, Smtm.typeof_dt_cons_eq] using hNN
  have hTypeofEq : __smtx_typeof (SmtTerm.DtCons s dSmt i) = raw := by
    rw [Smtm.typeof_dt_cons_eq]
    exact smtx_typeof_guard_wf_of_non_none (SmtType.Datatype s dSmt) raw hGuardNN
  have hBaseWf : __smtx_dt_wf_rec dSmt (native_reflist_insert native_reflist_nil s) = true := by
    have hWf := Smtm.smtx_typeof_guard_wf_wf_of_non_none (SmtType.Datatype s dSmt) raw hGuardNN
    exact datatype_wf_rec_of_type_wf hWf
  have hBaseNN : __eo_to_smt_type (Term.DatatypeType s d) ≠ SmtType.None := by
    simp [__eo_to_smt_type, native_ite, hReserved]
  have hRec := eo_to_smt_typeof_dt_cons_rec_substitute_of_wf s d (Term.DatatypeType s d)
    hBaseNN d i (native_reflist_insert native_reflist_nil s)
    (by simp [native_reflist_contains, native_reflist_insert, native_reflist_nil])
    hBaseWf hBaseWf
  change __eo_to_smt_type (__eo_typeof_dt_cons_rec (Term.DatatypeType s d) (__eo_dt_substitute s d d) i) =
    __smtx_typeof (SmtTerm.DtCons s dSmt i)
  rw [hRec]
  simpa [__eo_to_smt_type, native_ite, hReserved, dSmt] using hTypeofEq.symm

/-- Stronger EO-side helper for `typeof_apply_dt_cons`. -/
theorem eo_to_smt_type_typeof_apply_dt_cons_of_fun_like
    (x U V : Term) (s : native_String) (d : Datatype) (i : native_Nat)
    (hHead :
      __eo_typeof (Term.DtCons s d i) = Term.Apply (Term.Apply Term.FunType U) V ∨
        __eo_typeof (Term.DtCons s d i) = Term.DtcAppType U V)
    (hx : __eo_typeof x = U)
    (hU : __eo_to_smt_type U ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtCons s d i) x)) =
      __eo_to_smt_type V := by
  apply eo_to_smt_type_typeof_apply_of_fun_like
    (f := Term.DtCons s d i) (T := U) (U := V)
  · change __eo_typeof (Term.Apply (Term.DtCons s d i) x) =
      __eo_typeof_apply (__eo_typeof (Term.DtCons s d i)) (__eo_typeof x)
    rfl
  · exact hHead
  · exact hx
  · exact hU

/-- Stronger EO-side helper for `typeof_apply_dt_sel`. -/
theorem eo_to_smt_type_typeof_apply_dt_sel_of_datatype_type
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (hx : __eo_typeof x = Term.DatatypeType s d) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __eo_to_smt_type (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) := by
  have hDt : Term.DatatypeType s d ≠ Term.Stuck := by
    intro hStuck
    cases hStuck
  have hReq :
      __eo_requires (Term.DatatypeType s d) (Term.DatatypeType s d)
        (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) =
      __eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j :=
    eo_requires_self_of_non_stuck (Term.DatatypeType s d)
      (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) hDt
  change
    __eo_to_smt_type
        (__eo_typeof_apply (__eo_typeof (Term.DtSel s d i j)) (__eo_typeof x)) =
      __eo_to_smt_type (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j)
  rw [hx]
  simpa [__eo_typeof_apply, hDt] using congrArg __eo_to_smt_type hReq

/-- Stronger selector helper phrased directly with the SMT selector return type. -/
theorem eo_to_smt_type_typeof_apply_dt_sel_of_datatype_type_smt_ret
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (hx : __eo_typeof x = Term.DatatypeType s d)
    (hWf :
      __smtx_dt_wf_rec (__eo_to_smt_datatype d)
        (native_reflist_insert native_reflist_nil s) = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  exact
    (eo_to_smt_type_typeof_apply_dt_sel_of_datatype_type x s d i j hx).trans
      (eo_to_smt_typeof_dt_sel_return_substitute_self s d i j hWf)

/-- Stronger EO-side helper for `typeof_apply_apply_select`. -/
theorem eo_to_smt_type_typeof_apply_apply_select_of_array
    (x y U T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T)
    (hx : __eo_typeof x = U)
    (hU : __eo_to_smt_type U ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) =
      __eo_to_smt_type T := by
  have hUNS : U ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none U hU
  have hReq : __eo_requires (__eo_eq U U) (Term.Boolean true) T = T :=
    eo_requires_eo_eq_self_of_non_stuck U T hUNS
  change __eo_to_smt_type (__eo_typeof_select (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type T
  rw [hy, hx]
  simpa [__eo_typeof_select, hUNS] using congrArg __eo_to_smt_type hReq

/-- Stronger EO-side helper for `typeof_apply_apply_apply_store`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_store_of_array
    (x y z U T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T)
    (hy : __eo_typeof y = U)
    (hx : __eo_typeof x = T)
    (hU : __eo_to_smt_type U ≠ SmtType.None)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) =
      SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T) := by
  have hUNS : U ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none U hU
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  have hReq :
      __eo_requires (__eo_and (__eo_eq U U) (__eo_eq T T)) (Term.Boolean true)
        (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T) =
      Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T :=
    eo_requires_eo_and_eq_self_of_non_stuck U T
      (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T) hUNS hTNS
  have hArrayTy :
      __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T) =
        SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T) := by
    change
      __smtx_typeof_guard (__eo_to_smt_type U)
          (__smtx_typeof_guard (__eo_to_smt_type T)
            (SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T))) =
        SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T)
    rw [smtx_typeof_guard_of_non_none _ _ hU, smtx_typeof_guard_of_non_none _ _ hT]
  change
    __eo_to_smt_type (__eo_typeof_store (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T)
  rw [hz, hy, hx]
  simpa [__eo_typeof_store, hUNS, hTNS, hReq] using hArrayTy

/-- Private EO-side helper for `is`. -/
private theorem eo_typeof_is_of_non_stuck
    (C D : Term)
    (hC : C ≠ Term.Stuck)
    (hD : D ≠ Term.Stuck) :
    __eo_typeof_is C D = Term.Bool := by
  cases C <;> cases D <;> simp [__eo_typeof_is] at hC hD ⊢

/-- Private EO-side helper for `update`. -/
private theorem eo_typeof_update_of_non_stuck
    (S D T : Term)
    (hS : S ≠ Term.Stuck)
    (hT : T ≠ Term.Stuck) :
    __eo_typeof_update S D T = D := by
  cases S <;> cases D <;> cases T <;> simp [__eo_typeof_update] at hS hT ⊢

/-- Private EO-side helper for `tuple_select`. -/
private theorem eo_typeof_tuple_select_of_non_stuck
    (i T : Term)
    (hi : i ≠ Term.Stuck)
    (hT : T ≠ Term.Stuck) :
    __eo_typeof_tuple_select (Term.UOp UserOp.Int) i T =
      __eo_list_nth (Term.UOp UserOp.Tuple) T i := by
  cases i <;> cases T <;> simp [__eo_typeof_tuple_select] at hi hT ⊢

/-- Private EO-side helper for `tuple_update`. -/
private theorem eo_typeof_tuple_update_of_non_stuck
    (i T U : Term)
    (hi : i ≠ Term.Stuck)
    (hT : T ≠ Term.Stuck)
    (hU : U ≠ Term.Stuck) :
    __eo_typeof_tuple_update (Term.UOp UserOp.Int) i T U =
      __eo_requires U (__eo_list_nth (Term.UOp UserOp.Tuple) T i) T := by
  cases i <;> cases T <;> cases U <;>
    simp [__eo_typeof_tuple_update] at hi hT hU ⊢

/-- Private EO-side helper for `_at_witness_string_length`. -/
private theorem eo_typeof_at_witness_string_length_of_non_stuck
    (T : Term)
    (hT : T ≠ Term.Stuck) :
    __eo_typeof__at_witness_string_length Term.Type T (Term.UOp UserOp.Int) (Term.UOp UserOp.Int) = T := by
  cases T <;> simp [__eo_typeof__at_witness_string_length] at hT ⊢

/-- Stronger EO-side helper for `typeof_apply_apply_is`. -/
theorem eo_to_smt_type_typeof_apply_apply_is_of_non_stuck
    (x y : Term)
    (hy : __eo_typeof y ≠ Term.Stuck)
    (hx : __eo_typeof x ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.is y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_is (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_is_of_non_stuck (__eo_typeof y) (__eo_typeof x) hy hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_update`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_update_of_middle_type
    (x y z D : Term)
    (hz : __eo_typeof z ≠ Term.Stuck)
    (hy : __eo_typeof y = D)
    (hx : __eo_typeof x ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update z) y) x)) =
      __eo_to_smt_type D := by
  change __eo_to_smt_type (__eo_typeof_update (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type D
  rw [hy]
  rw [eo_typeof_update_of_non_stuck (__eo_typeof z) D (__eo_typeof x) hz hx]

/-- Stronger EO-side helper for `typeof_apply_apply_tuple_select`. -/
theorem eo_to_smt_type_typeof_apply_apply_tuple_select_of_int
    (x y T : Term)
    (hx : __eo_typeof x = Term.UOp UserOp.Int)
    (hy : __eo_typeof y = T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.tuple_select x) y)) =
      __eo_to_smt_type (__eo_list_nth (Term.UOp UserOp.Tuple) T x) := by
  have hXNS : x ≠ Term.Stuck := by
    intro hX
    subst x
    have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
      rfl
    rw [hStuckTy] at hx
    cases hx
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  change __eo_to_smt_type (__eo_typeof_tuple_select (__eo_typeof x) x (__eo_typeof y)) =
    __eo_to_smt_type (__eo_list_nth (Term.UOp UserOp.Tuple) T x)
  rw [hx, hy]
  rw [eo_typeof_tuple_select_of_non_stuck x T hXNS hTNS]

/-- Stronger EO-side helper for `typeof_apply_apply_apply_tuple_update`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_tuple_update_of_int_list_nth_type
    (x y z T : Term)
    (hz : __eo_typeof z = Term.UOp UserOp.Int)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = __eo_list_nth (Term.UOp UserOp.Tuple) T z)
    (hT : __eo_to_smt_type T ≠ SmtType.None)
    (hNth : __eo_to_smt_type (__eo_list_nth (Term.UOp UserOp.Tuple) T z) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update z) y) x)) =
      __eo_to_smt_type T := by
  have hZNS : z ≠ Term.Stuck := by
    intro hZ
    subst z
    have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
      rfl
    rw [hStuckTy] at hz
    cases hz
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  have hNthNS : __eo_list_nth (Term.UOp UserOp.Tuple) T z ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none
      (__eo_list_nth (Term.UOp UserOp.Tuple) T z) hNth
  change
    __eo_to_smt_type (__eo_typeof_tuple_update (__eo_typeof z) z (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type T
  rw [hz, hy, hx]
  rw [eo_typeof_tuple_update_of_non_stuck z T (__eo_list_nth (Term.UOp UserOp.Tuple) T z) hZNS hTNS hNthNS]
  simpa using
    congrArg __eo_to_smt_type
      (eo_requires_self_of_non_stuck (__eo_list_nth (Term.UOp UserOp.Tuple) T z) T hNthNS)

/-- Stronger EO-side helper for `typeof_seq_empty`. -/
theorem eo_to_smt_type_typeof_seq_empty_of_seq_type
    (T : Term)
    (hType : __eo_typeof T = Term.Type)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T))) =
      SmtType.Seq (__eo_to_smt_type T) := by
  have hSeqType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.Seq) T) = Term.Type := by
    change __eo_typeof_Seq (__eo_typeof T) = Term.Type
    rw [hType]
    rfl
  change
    __eo_to_smt_type
        (__eo_typeof_seq_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.Seq) T))
          (Term.Apply (Term.UOp UserOp.Seq) T)) =
      SmtType.Seq (__eo_to_smt_type T)
  rw [hSeqType]
  change __eo_to_smt_type (__eo_disamb_type_seq_empty (Term.Apply (Term.UOp UserOp.Seq) T)) =
    SmtType.Seq (__eo_to_smt_type T)
  simp [__eo_disamb_type_seq_empty]
  exact smtx_typeof_guard_of_non_none _ _ hT

/-- Bridge-free direct form for `seq_empty` in the main translation proof. -/
theorem eo_to_smt_typeof_matches_translation_seq_empty
    (T : Term)
    (h : __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) =
      __eo_to_smt_type (__eo_typeof (Term.UOp1 UserOp1.seq_empty T)) := by
  cases hTy : __eo_to_smt_type T <;> rw [hTy] at h <;>
    simp [__eo_to_smt_seq_empty] at h
  case Seq A =>
    have hSmt : __smtx_typeof (SmtTerm.seq_empty A) = SmtType.Seq A :=
      smtx_typeof_seq_empty_of_non_none A h
    have hSeqWF : __smtx_type_wf (SmtType.Seq A) = true :=
      Smtm.smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq A) (SmtType.Seq A) (by
        simpa [__smtx_typeof] using h)
    have hWF : __smtx_type_wf A = true :=
      Smtm.seq_type_wf_component_of_wf hSeqWF
    rcases eo_to_smt_type_eq_seq hTy with ⟨U, hTEq, hU⟩
    subst T
    have hUWF : __smtx_type_wf (__eo_to_smt_type U) = true := by
      rw [hU]
      exact hWF
    have hUType := eo_typeof_type_of_smt_type_wf U hUWF
    have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
      Smtm.type_wf_non_none hUWF
    have hEo := eo_to_smt_type_typeof_seq_empty_of_seq_type U hUType hUNN
    change __smtx_typeof (SmtTerm.seq_empty A) =
      __eo_to_smt_type (__eo_typeof (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)))
    rw [hSmt]
    change SmtType.Seq A =
      __eo_to_smt_type (__eo_typeof (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)))
    rw [hEo, hU]

/-- Stronger EO-side helper for `typeof_set_empty`. -/
theorem eo_to_smt_type_typeof_set_empty_of_set_type
    (T : Term)
    (hType : __eo_typeof T = Term.Type)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) T))) =
      SmtType.Set (__eo_to_smt_type T) := by
  have hSetType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.Set) T) = Term.Type := by
    change __eo_typeof_Seq (__eo_typeof T) = Term.Type
    rw [hType]
    rfl
  change
    __eo_to_smt_type
        (__eo_typeof_set_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.Set) T))
          (Term.Apply (Term.UOp UserOp.Set) T)) =
      SmtType.Set (__eo_to_smt_type T)
  rw [hSetType]
  change __eo_to_smt_type (__eo_disamb_type_set_empty (Term.Apply (Term.UOp UserOp.Set) T)) =
    SmtType.Set (__eo_to_smt_type T)
  simp [__eo_disamb_type_set_empty]
  exact smtx_typeof_guard_of_non_none _ _ hT

/-- Bridge-free direct form for `set_empty` in the main translation proof. -/
theorem eo_to_smt_typeof_matches_translation_set_empty
    (T : Term)
    (h : __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) =
      __eo_to_smt_type (__eo_typeof (Term.UOp1 UserOp1.set_empty T)) := by
  cases hTy : __eo_to_smt_type T <;> rw [hTy] at h <;>
    simp [__eo_to_smt_set_empty] at h
  case Set A =>
    have hSmt : __smtx_typeof (SmtTerm.set_empty A) = SmtType.Set A :=
      smtx_typeof_set_empty_of_non_none A h
    have hSetWF : __smtx_type_wf (SmtType.Set A) = true :=
      Smtm.smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set A) (SmtType.Set A) (by
        simpa [__smtx_typeof] using h)
    have hWF : __smtx_type_wf A = true :=
      Smtm.set_type_wf_component_of_wf hSetWF
    rcases eo_to_smt_type_eq_set hTy with ⟨U, hTEq, hU⟩
    subst T
    have hUWF : __smtx_type_wf (__eo_to_smt_type U) = true := by
      rw [hU]
      exact hWF
    have hUType := eo_typeof_type_of_smt_type_wf U hUWF
    have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
      Smtm.type_wf_non_none hUWF
    have hEo := eo_to_smt_type_typeof_set_empty_of_set_type U hUType hUNN
    change __smtx_typeof (SmtTerm.set_empty A) =
      __eo_to_smt_type (__eo_typeof (Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) U)))
    rw [hSmt]
    change SmtType.Set A =
      __eo_to_smt_type (__eo_typeof (Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) U)))
    rw [hEo, hU]

/-- Simplifies EO-to-SMT type translation for `typeof_purify`. -/
theorem eo_to_smt_type_typeof_purify
    (x : Term) :
    __eo_to_smt_type (__eo_typeof (Term._at_purify x)) =
      __eo_to_smt_type (__eo_typeof x) := by
  change __eo_to_smt_type (__eo_typeof__at_purify (__eo_typeof x)) =
      __eo_to_smt_type (__eo_typeof x)
  cases h : __eo_typeof x <;> rfl

/-- Stronger EO-side helper for `typeof_apply_at_bvsize`. -/
theorem eo_to_smt_type_typeof_apply_at_bvsize_of_bitvec_type
    (x w : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_bvsize) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_bvsize (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_not_of_bool`. -/
theorem eo_to_smt_type_typeof_apply_not_of_bool
    (x : Term)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.not) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_not (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_abs_of_int`. -/
theorem eo_to_smt_type_typeof_apply_abs_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.abs) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_abs (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_len_of_seq`. -/
theorem eo_to_smt_type_typeof_apply_str_len_of_seq
    (x V : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) V) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_len) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_len (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_rev_of_seq`. -/
theorem eo_to_smt_type_typeof_apply_str_rev_of_seq
    (x V : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) V)
    (hV : __eo_to_smt_type V ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_rev) x)) =
      SmtType.Seq (__eo_to_smt_type V) := by
  change __eo_to_smt_type (__eo_typeof_str_rev (__eo_typeof x)) =
    SmtType.Seq (__eo_to_smt_type V)
  rw [hx]
  exact smtx_typeof_guard_of_non_none _ _ hV

/-- Simplifies EO-to-SMT type translation for `typeof_apply_seq_unit_of_non_none`. -/
theorem eo_to_smt_type_typeof_apply_seq_unit_of_non_none
    (x : Term)
    (hx : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) x)) =
      SmtType.Seq (__eo_to_smt_type (__eo_typeof x)) := by
  change __eo_to_smt_type (__eo_typeof_seq_unit (__eo_typeof x)) =
    SmtType.Seq (__eo_to_smt_type (__eo_typeof x))
  cases hTy : __eo_typeof x <;> simp [__eo_typeof_seq_unit, __eo_to_smt_type, hTy] at hx ⊢
  case UOp a =>
    exact smtx_typeof_guard_of_non_none _ _ hx
  case Apply =>
    exact smtx_typeof_guard_of_non_none _ _ hx
  case DatatypeType =>
    apply smtx_typeof_guard_of_non_none
    simp [hx]
  case DatatypeTypeRef =>
    apply smtx_typeof_guard_of_non_none
    simp [hx]
  case DtcAppType a b =>
    cases hA : __eo_to_smt_type a <;> cases hB : __eo_to_smt_type b <;>
      simp [__smtx_typeof_guard, native_ite, native_Teq, hA, hB] at hx ⊢
  all_goals simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_set_singleton_of_non_none`. -/
theorem eo_to_smt_type_typeof_apply_set_singleton_of_non_none
    (x : Term)
    (hx : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.set_singleton) x)) =
      SmtType.Set (__eo_to_smt_type (__eo_typeof x)) := by
  change __eo_to_smt_type (__eo_typeof_set_singleton (__eo_typeof x)) =
    SmtType.Set (__eo_to_smt_type (__eo_typeof x))
  cases hTy : __eo_typeof x <;> simp [__eo_typeof_set_singleton, __eo_to_smt_type, hTy] at hx ⊢
  case UOp a =>
    exact smtx_typeof_guard_of_non_none _ _ hx
  case Apply =>
    exact smtx_typeof_guard_of_non_none _ _ hx
  case DatatypeType =>
    apply smtx_typeof_guard_of_non_none
    simp [hx]
  case DatatypeTypeRef =>
    apply smtx_typeof_guard_of_non_none
    simp [hx]
  case DtcAppType a b =>
    cases hA : __eo_to_smt_type a <;> cases hB : __eo_to_smt_type b <;>
      simp [__smtx_typeof_guard, native_ite, native_Teq, hA, hB] at hx ⊢
  all_goals simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- Stronger EO-side helper for `typeof_apply_at_bvsize`. -/
theorem eo_to_smt_type_typeof_apply_at_bvsize_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_bvsize) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_bvsize (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_set_choose`. -/
theorem eo_to_smt_type_typeof_apply_set_choose_of_set
    (x T : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) x)) = __eo_to_smt_type T := by
  change __eo_to_smt_type (__eo_typeof_set_choose (__eo_typeof x)) = __eo_to_smt_type T
  rw [hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_set_is_singleton`. -/
theorem eo_to_smt_type_typeof_apply_set_is_singleton_of_set
    (x T : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.set_is_singleton) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_set_is_empty (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_set_is_empty`. -/
theorem eo_to_smt_type_typeof_apply_set_is_empty_of_set
    (x T : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.set_is_empty) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_set_is_empty (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_to_real_of_int`. -/
theorem eo_to_smt_type_typeof_apply_to_real_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.to_real) x)) = SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof_to_real (__eo_typeof x)) = SmtType.Real
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_to_real_of_real`. -/
theorem eo_to_smt_type_typeof_apply_to_real_of_real
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Real)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.to_real) x)) = SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof_to_real (__eo_typeof x)) = SmtType.Real
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_to_int_of_real`. -/
theorem eo_to_smt_type_typeof_apply_to_int_of_real
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Real)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.to_int) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_to_int (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_int_pow2_of_int`. -/
theorem eo_to_smt_type_typeof_apply_int_pow2_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.int_pow2) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_int_log2_of_int`. -/
theorem eo_to_smt_type_typeof_apply_int_log2_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.int_log2) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_int_ispow2_of_int`. -/
theorem eo_to_smt_type_typeof_apply_int_ispow2_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.int_ispow2) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_int_ispow2 (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_int_div_by_zero_of_int`. -/
theorem eo_to_smt_type_typeof_apply_at_int_div_by_zero_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_mod_by_zero_of_int`. -/
theorem eo_to_smt_type_typeof_apply_at_mod_by_zero_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_div_by_zero_of_real`. -/
theorem eo_to_smt_type_typeof_apply_at_div_by_zero_of_real
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Real)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_div_by_zero) x)) = SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof__at_div_by_zero (__eo_typeof x)) = SmtType.Real
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_is_int_of_real`. -/
theorem eo_to_smt_type_typeof_apply_is_int_of_real
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Real)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.is_int) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_is_int (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_lower_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_lower_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_lower) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_to_lower (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_upper_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_upper_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_upper) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_to_lower (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_code_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_code_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_code) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_to_code (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_from_code_of_int`. -/
theorem eo_to_smt_type_typeof_apply_str_from_code_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_from_code) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_from_code (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_is_digit_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_is_digit_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_is_digit) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_is_digit (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_int_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_int_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_int) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_to_code (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_from_int_of_int`. -/
theorem eo_to_smt_type_typeof_apply_str_from_int_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_from_int) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_from_code (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_strings_stoi_non_digit_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_at_strings_stoi_non_digit_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term._at_strings_stoi_non_digit x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_to_code (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

end DeferredTypeRecovery

/-- Stronger EO-side helper for `typeof_apply_apply_or`. -/
theorem eo_to_smt_type_typeof_apply_apply_or_of_bool
    (x y : Term)
    (hy : __eo_typeof y = Term.Bool)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_and`. -/
theorem eo_to_smt_type_typeof_apply_apply_and_of_bool
    (x y : Term)
    (hy : __eo_typeof y = Term.Bool)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_imp`. -/
theorem eo_to_smt_type_typeof_apply_apply_imp_of_bool
    (x y : Term)
    (hy : __eo_typeof y = Term.Bool)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.imp) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_xor`. -/
theorem eo_to_smt_type_typeof_apply_apply_xor_of_bool
    (x y : Term)
    (hy : __eo_typeof y = Term.Bool)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.xor) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_eq`. -/
theorem eo_to_smt_type_typeof_apply_apply_eq_of_same_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) =
      SmtType.Bool := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  change __eo_to_smt_type (__eo_typeof_eq (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  simpa [__eo_typeof_eq] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck T Term.Bool hTNS)

/-- Stronger EO-side helper for `typeof_apply_apply_plus`. -/
theorem eo_to_smt_type_typeof_apply_apply_plus_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.plus) y) x)) =
      __eo_to_smt_type T := by
  change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = __eo_to_smt_type T
  rw [hy, hx]
  rcases hT with rfl | rfl <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_neg`. -/
theorem eo_to_smt_type_typeof_apply_apply_neg_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y) x)) =
      __eo_to_smt_type T := by
  change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = __eo_to_smt_type T
  rw [hy, hx]
  rcases hT with rfl | rfl <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_mult`. -/
theorem eo_to_smt_type_typeof_apply_apply_mult_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) x)) =
      __eo_to_smt_type T := by
  change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = __eo_to_smt_type T
  rw [hy, hx]
  rcases hT with rfl | rfl <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_lt`. -/
theorem eo_to_smt_type_typeof_apply_apply_lt_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rcases hT with rfl | rfl <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_leq`. -/
theorem eo_to_smt_type_typeof_apply_apply_leq_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rcases hT with rfl | rfl <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_gt`. -/
theorem eo_to_smt_type_typeof_apply_apply_gt_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rcases hT with rfl | rfl <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_geq`. -/
theorem eo_to_smt_type_typeof_apply_apply_geq_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rcases hT with rfl | rfl <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_div`. -/
theorem eo_to_smt_type_typeof_apply_apply_div_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.div) y) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_mod`. -/
theorem eo_to_smt_type_typeof_apply_apply_mod_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mod) y) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_multmult`. -/
theorem eo_to_smt_type_typeof_apply_apply_multmult_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_divisible`. -/
theorem eo_to_smt_type_typeof_apply_apply_divisible_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_divisible (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_div_total`. -/
theorem eo_to_smt_type_typeof_apply_apply_div_total_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_mod_total`. -/
theorem eo_to_smt_type_typeof_apply_apply_mod_total_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_multmult_total`. -/
theorem eo_to_smt_type_typeof_apply_apply_multmult_total_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_qdiv`. -/
theorem eo_to_smt_type_typeof_apply_apply_qdiv_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) x)) =
      SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
  rw [hy, hx]
  rcases hT with rfl | rfl <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_qdiv_total`. -/
theorem eo_to_smt_type_typeof_apply_apply_qdiv_total_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) x)) =
      SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
  rw [hy, hx]
  rcases hT with rfl | rfl <;> rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_re_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_re_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_re) x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_str_to_re (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_mult_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_mult_of_reglan
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.RegLan)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.re_mult) x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_plus_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_plus_of_reglan
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.RegLan)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.re_plus) x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_opt_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_opt_of_reglan
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.RegLan)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.re_opt) x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_comp_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_comp_of_reglan
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.RegLan)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.re_comp) x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvnot_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvnot_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)) = SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvnot (__eo_typeof x)) = SmtType.BitVec w
  rw [hx]
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) =
    SmtType.BitVec w
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq,
    native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvneg_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvneg_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) x)) = SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvnot (__eo_typeof x)) = SmtType.BitVec w
  rw [hx]
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) =
    SmtType.BitVec w
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq,
    native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvnego_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvnego_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnego) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvnego (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvredand_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvredand_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvredand) x)) = SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvredand (__eo_typeof x)) = SmtType.BitVec 1
  rw [hx]
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) = SmtType.BitVec 1
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq, native_int_to_nat,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvredor_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvredor_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvredor) x)) = SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvredand (__eo_typeof x)) = SmtType.BitVec 1
  rw [hx]
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) = SmtType.BitVec 1
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq, native_int_to_nat,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_ubv_to_int_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_ubv_to_int_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.ubv_to_int) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_bvsize (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_sbv_to_int_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_sbv_to_int_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.sbv_to_int) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_bvsize (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `_at_strings_stoi_result`. -/
theorem eo_to_smt_type_typeof_apply_apply_at_strings_stoi_result_of_seq_char_int
    (x y : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_strings_stoi_result y) x)) =
      SmtType.Int := by
  change
    __eo_to_smt_type
        (__eo_typeof__at_strings_stoi_result (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_ite`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_ite_of_bool_same_type
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Bool)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) =
      __eo_to_smt_type T := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  change __eo_to_smt_type (__eo_typeof_ite (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type T
  rw [hz, hy, hx]
  simpa [__eo_typeof_ite] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck T T hTNS)

/-- Private EO-side helper for sequence binops with a same-element-type check. -/
private theorem eo_to_smt_type_typeof_seq_same_elem_ret_bool
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_str_contains (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hy, hx]
  simpa [__eo_typeof_str_contains] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck T Term.Bool hTNS)

/-- Private EO-side helper for sequence binops returning the same sequence type. -/
private theorem eo_to_smt_type_typeof_seq_same_elem_ret_seq
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_str_concat (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hy, hx]
  simpa [__eo_typeof_str_concat] using
    congrArg __eo_to_smt_type
      (eo_requires_eo_eq_self_of_non_stuck T (Term.Apply (Term.UOp UserOp.Seq) T) hTNS)

/-- Private EO-side helper for ternary string ops with two same-element-type checks. -/
private theorem eo_to_smt_type_typeof_seq_same_elem_same_elem_ret_seq
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_str_replace (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hz, hy, hx]
  simpa [__eo_typeof_str_replace] using
    congrArg __eo_to_smt_type
      (eo_requires_eo_and_eq_self_of_non_stuck T T (Term.Apply (Term.UOp UserOp.Seq) T) hTNS hTNS)

/-- Private EO-side helper for string `indexof`-style typing. -/
private theorem eo_to_smt_type_typeof_seq_same_elem_int_ret_int
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.UOp UserOp.Int)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_str_indexof (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Int := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hz, hy, hx]
  simpa [__eo_typeof_str_indexof] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck T (Term.UOp UserOp.Int) hTNS)

/-- Private EO-side helper for string `update`-style typing. -/
private theorem eo_to_smt_type_typeof_seq_int_same_elem_ret_seq
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_str_update (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hz, hy, hx]
  simpa [__eo_typeof_str_update] using
    congrArg __eo_to_smt_type
      (eo_requires_eo_eq_self_of_non_stuck T (Term.Apply (Term.UOp UserOp.Seq) T) hTNS)

/-- Stronger EO-side helper for `typeof_apply_apply_str_contains`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_contains_of_seq
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_contains (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_seq_same_elem_ret_bool x y T hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_str_prefixof`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_prefixof_of_seq
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_contains (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_seq_same_elem_ret_bool x y T hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_str_suffixof`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_suffixof_of_seq
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_contains (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_seq_same_elem_ret_bool x y T hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_str_lt`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_lt_of_seq_char
    (x y : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_str_leq`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_leq_of_seq_char
    (x y : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_re_range`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_range_of_seq_char
    (x y : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_range (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_re_concat`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_concat_of_reglan
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_re_inter`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_inter_of_reglan
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_re_union`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_union_of_reglan
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_re_diff`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_diff_of_reglan
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_str_in_re`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_in_re_of_seq_char_reglan
    (x y : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_in_re (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_seq_nth`. -/
theorem eo_to_smt_type_typeof_apply_apply_seq_nth_of_seq_int
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) y) x)) =
      __eo_to_smt_type T := by
  change __eo_to_smt_type (__eo_typeof_seq_nth (__eo_typeof y) (__eo_typeof x)) = __eo_to_smt_type T
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_str_concat`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_concat_of_seq
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_concat (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  exact eo_to_smt_type_typeof_seq_same_elem_ret_seq x y T hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_str_at`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_at_of_seq_int
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_at (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_substr`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_substr_of_seq_int_int
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_substr (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  rw [hz, hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_indexof`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_indexof_of_seq_seq_int
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.UOp UserOp.Int)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_indexof (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Int
  exact eo_to_smt_type_typeof_seq_same_elem_int_ret_int x y z T hz hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_update`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_update_of_seq_int_seq
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_update (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  exact eo_to_smt_type_typeof_seq_int_same_elem_ret_seq x y z T hz hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_replace`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_of_seq
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) z) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_replace (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  exact eo_to_smt_type_typeof_seq_same_elem_same_elem_ret_seq x y z T hz hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_replace_all`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_all_of_seq
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) z) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_replace (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  exact eo_to_smt_type_typeof_seq_same_elem_same_elem_ret_seq x y z T hz hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_replace_re`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_of_seq_char_reglan
    (x y z : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) z) y) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_replace_re (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Seq SmtType.Char
  rw [hz, hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_replace_re_all`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_all_of_seq_char_reglan
    (x y z : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) z) y) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_replace_re (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Seq SmtType.Char
  rw [hz, hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_indexof_re`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_indexof_re_of_seq_char_reglan
    (x y z : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_indexof_re (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Int
  rw [hz, hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_at_re_unfold_pos_component`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_re_unfold_pos_component_of_seq_char_reglan_int
    (x y z : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type
        (__eo_typeof
          (Term._at_re_unfold_pos_component z y x)) =
      SmtType.Seq SmtType.Char := by
  change
    __eo_to_smt_type
        (__eo_typeof__at_re_unfold_pos_component (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Seq SmtType.Char
  rw [hx, hz, hy]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_re_loop`. -/
theorem native_zlt_neg_one_of_zleq_zero {n : native_Int}
    (hn : native_zleq 0 n = true) :
    native_zlt (-1 : native_Int) n = true := by
  have hn' : (0 : Int) <= n := by
    simpa [native_zleq] using hn
  have hlt : (-1 : Int) < n := by
    omega
  simpa [native_zlt] using hlt

theorem eo_to_smt_type_typeof_apply_apply_apply_re_loop_of_int_int_reglan
    (x : Term) (n1 n2 : Int)
    (hn1 : native_zleq 0 n1 = true)
    (hn2 : native_zleq 0 n2 = true)
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type
        (__eo_typeof
          (Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral n1) (Term.Numeral n2)) x)) =
      SmtType.RegLan := by
  change
    __eo_to_smt_type
        (__eo_typeof_re_loop (__eo_typeof (Term.Numeral n1)) (Term.Numeral n1)
          (__eo_typeof (Term.Numeral n2)) (Term.Numeral n2) (__eo_typeof x)) =
      SmtType.RegLan
  have hn1Gt : native_zlt (-1 : native_Int) n1 = true :=
    native_zlt_neg_one_of_zleq_zero hn1
  have hn2Gt : native_zlt (-1 : native_Int) n2 = true :=
    native_zlt_neg_one_of_zleq_zero hn2
  rw [hx]
  change
    __eo_to_smt_type
        (__eo_typeof_re_loop (Term.UOp UserOp.Int) (Term.Numeral n1)
          (Term.UOp UserOp.Int) (Term.Numeral n2) (Term.UOp UserOp.RegLan)) =
      SmtType.RegLan
  simp [__eo_typeof_re_loop, __eo_gt, __eo_requires, native_teq, native_not,
    hn1Gt, hn2Gt]

/-- Stronger EO-side helper for `typeof_apply_apply_apply_at_witness_string_length`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_at_witness_string_length_of_type_int_int
    (x y z : Term)
    (hz : __eo_typeof z = Term.Type)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type
        (__eo_typeof (Term.UOp3 UserOp3._at_witness_string_length z y x)) =
      __eo_to_smt_type z := by
  change
    __eo_to_smt_type
        (__eo_typeof__at_witness_string_length (__eo_typeof z) z (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type z
  have hZNS : z ≠ Term.Stuck := by
    intro hZ
    subst z
    have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
      rfl
    rw [hStuckTy] at hz
    cases hz
  rw [hz, hy, hx]
  rw [eo_typeof_at_witness_string_length_of_non_stuck z hZNS]

/-- Private EO-side helper for same-width bitvector operators returning a bitvector. -/
private theorem eo_to_smt_type_typeof_bv_same_width_ret_bitvec
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  rw [hy, hx]
  simpa [__eo_typeof_bvand] using
    congrArg __eo_to_smt_type
      (eo_requires_eo_eq_self_of_non_stuck w (Term.Apply (Term.UOp UserOp.BitVec) w) hW)

/-- Private EO-side helper for same-width bitvector comparisons. -/
private theorem eo_to_smt_type_typeof_bv_same_width_ret_bool
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool := by
  rw [hy, hx]
  simpa [__eo_typeof_bvult] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck w Term.Bool hW)

/-- Private EO-side helper for same-width bitvector comparison-to-bv1 operators. -/
private theorem eo_to_smt_type_typeof_bv_same_width_ret_bv1
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof_bvcomp (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec 1 := by
  rw [hy, hx]
  simpa [__eo_typeof_bvcomp, __eo_to_smt_type, native_ite, native_zleq] using
    congrArg __eo_to_smt_type
      (eo_requires_eo_eq_self_of_non_stuck w (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) hW)

/-- Stronger EO-side helper for `typeof_apply_apply_concat`. -/
theorem eo_to_smt_type_typeof_apply_apply_concat_of_bitvec_types
    (x y w1 w2 : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w1)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w2) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) =
      __eo_to_smt_type (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add w1 w2)) := by
  change __eo_to_smt_type (__eo_typeof_concat (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add w1 w2))
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for same-width bitvector binops returning a bitvector. -/
theorem eo_to_smt_type_typeof_apply_apply_bvand_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvor`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvor_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvxor`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvxor_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvadd`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvadd_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvult`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvult_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvcomp`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvcomp_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) y) x)) =
      SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvcomp (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec 1
  exact eo_to_smt_type_typeof_bv_same_width_ret_bv1 x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvnand`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvnand_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvnand) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvnor`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvnor_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvnor) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvxnor`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvxnor_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvmul`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvmul_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvudiv`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvudiv_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvurem`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvurem_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsub`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsub_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsdiv`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsdiv_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdiv) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsrem`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsrem_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsrem) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsmod`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsmod_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmod) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvule`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvule_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvugt`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvugt_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvuge`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvuge_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvslt`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvslt_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsle`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsle_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsgt`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsgt_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsge`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsge_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvshl`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvshl_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvlshr`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvlshr_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvashr`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvashr_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvuaddo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvuaddo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvuaddo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsaddo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsaddo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsaddo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvumulo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvumulo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsmulo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsmulo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvusubo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvusubo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvusubo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvssubo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvssubo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvssubo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsdivo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsdivo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvultbv`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvultbv_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) y) x)) =
      SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvcomp (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec 1
  exact eo_to_smt_type_typeof_bv_same_width_ret_bv1 x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsltbv`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsltbv_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : w ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) y) x)) =
      SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvcomp (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec 1
  exact eo_to_smt_type_typeof_bv_same_width_ret_bv1 x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_repeat`. -/
theorem eo_to_smt_type_typeof_apply_apply_repeat_of_int_bitvec_type
    (x y n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.repeat y) x)) =
      __eo_to_smt_type
        (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
          (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_mul y n))) := by
  change __eo_to_smt_type (__eo_typeof_repeat (__eo_typeof y) y (__eo_typeof x)) =
    __eo_to_smt_type
      (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
        (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_mul y n)))
  rw [hy, hx]
  apply congrArg __eo_to_smt_type
  cases y with
  | _ =>
      rfl

/-- Stronger EO-side helper for `typeof_apply_apply_zero_extend`. -/
theorem eo_to_smt_type_typeof_apply_apply_zero_extend_of_int_bitvec_type
    (x y n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.zero_extend y) x)) =
      __eo_to_smt_type
        (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
          (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add n y))) := by
  change __eo_to_smt_type (__eo_typeof_zero_extend (__eo_typeof y) y (__eo_typeof x)) =
    __eo_to_smt_type
      (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
        (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add n y)))
  rw [hy, hx]
  apply congrArg __eo_to_smt_type
  cases y <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_sign_extend`. -/
theorem eo_to_smt_type_typeof_apply_apply_sign_extend_of_int_bitvec_type
    (x y n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend y) x)) =
      __eo_to_smt_type
        (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
          (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add n y))) := by
  change __eo_to_smt_type (__eo_typeof_zero_extend (__eo_typeof y) y (__eo_typeof x)) =
    __eo_to_smt_type
      (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
        (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add n y)))
  rw [hy, hx]
  apply congrArg __eo_to_smt_type
  cases y <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_rotate_left`. -/
theorem eo_to_smt_type_typeof_apply_apply_rotate_left_of_int_bitvec_type
    (x y n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.rotate_left y) x)) =
      __eo_to_smt_type
        (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) n)) := by
  change __eo_to_smt_type (__eo_typeof_rotate_left (__eo_typeof y) y (__eo_typeof x)) =
    __eo_to_smt_type
      (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
        (Term.Apply (Term.UOp UserOp.BitVec) n))
  rw [hy, hx]
  apply congrArg __eo_to_smt_type
  cases y <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_rotate_right`. -/
theorem eo_to_smt_type_typeof_apply_apply_rotate_right_of_int_bitvec_type
    (x y n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.rotate_right y) x)) =
      __eo_to_smt_type
        (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) n)) := by
  change __eo_to_smt_type (__eo_typeof_rotate_left (__eo_typeof y) y (__eo_typeof x)) =
    __eo_to_smt_type
      (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
        (Term.Apply (Term.UOp UserOp.BitVec) n))
  rw [hy, hx]
  apply congrArg __eo_to_smt_type
  cases y <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_int_to_bv`. -/
theorem eo_to_smt_type_typeof_apply_apply_int_to_bv_of_int_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv y) x)) =
      __eo_to_smt_type
        (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) y)) := by
  change __eo_to_smt_type (__eo_typeof_int_to_bv (__eo_typeof y) y (__eo_typeof x)) =
    __eo_to_smt_type
      (__eo_requires (__eo_gt y (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
        (Term.Apply (Term.UOp UserOp.BitVec) y))
  rw [hy, hx]
  apply congrArg __eo_to_smt_type
  cases y <;> rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_extract`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_extract_of_int_int_bitvec_type
    (x y z n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hz : __eo_typeof z = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract y z) x)) =
      __eo_to_smt_type
        (__eo_mk_apply
          (Term.UOp UserOp.BitVec)
          (__eo_requires (__eo_gt z (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
            (__eo_requires (__eo_gt n y) (Term.Boolean true)
              (__eo_requires
                (__eo_gt (__eo_add (__eo_add y (__eo_neg z)) (Term.Numeral 1))
                  (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
                (__eo_add (__eo_add y (__eo_neg z)) (Term.Numeral 1)))))) := by
  change __eo_to_smt_type (__eo_typeof_extract (__eo_typeof y) y (__eo_typeof z) z (__eo_typeof x)) =
    __eo_to_smt_type
      (__eo_mk_apply
        (Term.UOp UserOp.BitVec)
        (__eo_requires (__eo_gt z (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
          (__eo_requires (__eo_gt n y) (Term.Boolean true)
            (__eo_requires
              (__eo_gt (__eo_add (__eo_add y (__eo_neg z)) (Term.Numeral 1))
                (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
              (__eo_add (__eo_add y (__eo_neg z)) (Term.Numeral 1))))))
  rw [hy, hz, hx]
  apply congrArg __eo_to_smt_type
  cases y with
  | Stuck =>
      have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
        rfl
      rw [hStuckTy] at hy
      cases hy
  | _ =>
      cases z with
      | _ =>
          rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_bvite`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_bvite_of_bitvec1_same_type
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
      __eo_to_smt_type T := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  change __eo_to_smt_type (__eo_typeof_bvite (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type T
  rw [hz, hy, hx]
  simpa [__eo_typeof_bvite] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck T T hTNS)

end TranslationProofs
