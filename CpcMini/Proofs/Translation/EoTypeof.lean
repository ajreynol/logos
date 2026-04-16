import CpcMini.Proofs.Translation.Datatypes

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Computes `__smtx_typeof_guard` under a non-`None` premise. -/
theorem smtx_typeof_guard_of_non_none
    (T U : SmtType) (h : T ≠ SmtType.None) :
    __smtx_typeof_guard T U = U := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq] at h ⊢

/-- A translated sequence type is never an SMT type reference. -/
theorem smtx_typeof_guard_seq_ne_typeref
    (T : SmtType) (s : native_String) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.TypeRef s := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated sequence type is never an SMT datatype. -/
theorem smtx_typeof_guard_seq_ne_datatype
    (T : SmtType) (s : native_String) (d : SmtDatatype) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.Datatype s d := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT type reference. -/
theorem smtx_typeof_guard_fun_ne_typeref
    (T U : SmtType) (s : native_String) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠
      SmtType.TypeRef s := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT datatype. -/
theorem smtx_typeof_guard_fun_ne_datatype
    (T U : SmtType) (s : native_String) (d : SmtDatatype) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠
      SmtType.Datatype s d := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT type reference. -/
theorem smtx_typeof_guard_dtc_app_ne_typeref
    (T U : SmtType) (s : native_String) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠
      SmtType.TypeRef s := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT datatype. -/
theorem smtx_typeof_guard_dtc_app_ne_datatype
    (T U : SmtType) (s : native_String) (d : SmtDatatype) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠
      SmtType.Datatype s d := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- An EO application never translates to an SMT type reference. -/
theorem eo_to_smt_type_apply_ne_typeref
    (f x : Term) (s : native_String) :
    __eo_to_smt_type (Term.Apply f x) ≠ SmtType.TypeRef s := by
  cases f with
  | BitVec =>
      cases x with
      | Numeral n =>
          by_cases hz : native_zleq 0 n = true
          · simp [__eo_to_smt_type, native_ite, hz]
          · simp [__eo_to_smt_type, native_ite, hz]
      | _ =>
          simp [__eo_to_smt_type]
  | Seq =>
      simpa [__eo_to_smt_type] using
        smtx_typeof_guard_seq_ne_typeref (__eo_to_smt_type x) s
  | Apply f1 x1 =>
      cases f1 <;>
        simp [__eo_to_smt_type, smtx_typeof_guard_fun_ne_typeref]
  | _ =>
      simp [__eo_to_smt_type]

/-- An EO application never translates to an SMT datatype. -/
theorem eo_to_smt_type_apply_ne_datatype
    (f x : Term) (s : native_String) (d : SmtDatatype) :
    __eo_to_smt_type (Term.Apply f x) ≠ SmtType.Datatype s d := by
  cases f with
  | BitVec =>
      cases x with
      | Numeral n =>
          by_cases hz : native_zleq 0 n = true
          · simp [__eo_to_smt_type, native_ite, hz]
          · simp [__eo_to_smt_type, native_ite, hz]
      | _ =>
          simp [__eo_to_smt_type]
  | Seq =>
      simpa [__eo_to_smt_type] using
        smtx_typeof_guard_seq_ne_datatype (__eo_to_smt_type x) s d
  | Apply f1 x1 =>
      cases f1 <;>
        simp [__eo_to_smt_type, smtx_typeof_guard_fun_ne_datatype]
  | _ =>
      simp [__eo_to_smt_type]

/-- A translated EO datatype-constructor application type is never an SMT datatype. -/
theorem eo_to_smt_type_dtc_app_ne_datatype
    (T U : Term) (s : native_String) (d : SmtDatatype) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Datatype s d := by
  simpa [__eo_to_smt_type] using
    smtx_typeof_guard_dtc_app_ne_datatype (__eo_to_smt_type T) (__eo_to_smt_type U) s d

/-- Translating EO type-reference substitution matches the corresponding SMT substitution step. -/
theorem eo_to_smt_type_substitute_typeref
    (s : native_String) (d : Datatype) :
    ∀ T : Term,
      __eo_to_smt_type
          (native_ite (native_teq T (Term.DatatypeTypeRef s))
            (Term.DatatypeType s d) T) =
        native_ite (native_Teq (__eo_to_smt_type T) (SmtType.TypeRef s))
          (SmtType.Datatype s (__eo_to_smt_datatype d))
          (__eo_to_smt_type T)
  | Term.__eo_pf t => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Int => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Real => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.BitVec => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Char => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Seq => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List_nil => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List_cons => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Bool => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Boolean b => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Numeral n => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Rational q => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.String str => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Binary w n => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Type => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Stuck => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Apply f x => by
      have hneq : __eo_to_smt_type (Term.Apply f x) ≠ SmtType.TypeRef s :=
        eo_to_smt_type_apply_ne_typeref f x s
      simp [native_ite, native_teq, native_Teq, hneq]
  | Term.FunType => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Var name ty => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DatatypeType s2 d2 => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DatatypeTypeRef s2 => by
      by_cases hs : s2 = s
      · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, hs]
      · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, hs]
  | Term.DtcAppType T U => by
      let V :=
        __smtx_typeof_guard (__eo_to_smt_type T)
          (__smtx_typeof_guard (__eo_to_smt_type U)
            (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U)))
      have hneq : V ≠ SmtType.TypeRef s := by
        dsimp [V]
        exact smtx_typeof_guard_dtc_app_ne_typeref (__eo_to_smt_type T) (__eo_to_smt_type U) s
      by_cases hV : V = SmtType.TypeRef s
      · exact False.elim (hneq hV)
      · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, V, hV]
  | Term.DtCons s2 d2 i => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DtSel s2 d2 i j => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.USort u => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.UConst i T => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.not => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.or => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.and => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.imp => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.eq => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]

/-- Constructor congruence for SMT datatype constructors. -/
private theorem smt_datatype_cons_congr
    {T1 T2 : SmtType} {c1 c2 : SmtDatatypeCons}
    (hT : T1 = T2) (hc : c1 = c2) :
    SmtDatatypeCons.cons T1 c1 = SmtDatatypeCons.cons T2 c2 := by
  cases hT
  cases hc
  rfl

/-- `__smtx_dtc_substitute` takes its generic branch when the head type is not a datatype. -/
private theorem smtx_dtc_substitute_non_datatype
    (s : native_String) (d : SmtDatatype) (T : SmtType) (c : SmtDatatypeCons)
    (hT : ∀ s2 d2, T ≠ SmtType.Datatype s2 d2) :
    __smtx_dtc_substitute s d (SmtDatatypeCons.cons T c) =
      SmtDatatypeCons.cons
        (native_ite (native_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T)
        (__smtx_dtc_substitute s d c) := by
  cases T <;> simp [__smtx_dtc_substitute, native_ite, native_Teq] at hT ⊢

/-- Recursive calls from a datatype-constructor tail decrease the `Sum` measure. -/
private theorem sum_size_inl_lt_cons (T : Term) (c : DatatypeCons) :
    Sum.elim sizeOf sizeOf ((Sum.inl c : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf (Sum.inl (DatatypeCons.cons T c) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.DatatypeCons.cons.sizeOf_spec]
  omega

/-- Recursive calls into a datatype-valued field decrease the `Sum` measure. -/
private theorem sum_size_inr_lt_datatype_cons
    (s : native_String) (d : Datatype) (c : DatatypeCons) :
    Sum.elim sizeOf sizeOf ((Sum.inr d : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf
        (Sum.inl (DatatypeCons.cons (Term.DatatypeType s d) c) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.DatatypeCons.cons.sizeOf_spec, Eo.Term.DatatypeType.sizeOf_spec]
  omega

/-- Recursive calls from the constructor part of a datatype sum decrease the `Sum` measure. -/
private theorem sum_size_inl_lt_sum (c : DatatypeCons) (d : Datatype) :
    Sum.elim sizeOf sizeOf ((Sum.inl c : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf (Sum.inr (Datatype.sum c d) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.Datatype.sum.sizeOf_spec]
  omega

/-- Recursive calls from the tail part of a datatype sum decrease the `Sum` measure. -/
private theorem sum_size_inr_lt_sum (c : DatatypeCons) (d : Datatype) :
    Sum.elim sizeOf sizeOf ((Sum.inr d : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf (Sum.inr (Datatype.sum c d) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.Datatype.sum.sizeOf_spec]
  omega

/--
Auxiliary commutation theorem for EO/SMT datatype substitution, indexed over the
sum of datatype constructors and datatypes so the recursion can descend into
nested datatype fields.
-/
private theorem eo_to_smt_substitute_aux
    (s : native_String) (d : Datatype) :
    ∀ x : Sum DatatypeCons Datatype,
      Sum.elim
        (fun c =>
          __eo_to_smt_datatype_cons (__eo_dtc_substitute s d c) =
            __smtx_dtc_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype_cons c))
        (fun d0 =>
          __eo_to_smt_datatype (__eo_dt_substitute s d d0) =
            __smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d0))
        x
  | .inl DatatypeCons.unit => by
      simp [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute]
  | .inl (DatatypeCons.cons T c) => by
      cases T
      case DatatypeType s2 d2 =>
        by_cases hst : native_streq s s2 = true
        · have hc := eo_to_smt_substitute_aux s d (.inl c)
          simpa [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute,
            native_ite, hst] using hc
        · have hd2 := eo_to_smt_substitute_aux s d (.inr d2)
          have hc := eo_to_smt_substitute_aux s d (.inl c)
          simpa [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute,
            native_ite, hst] using And.intro hd2 hc
      case Apply f x =>
        have hc := eo_to_smt_substitute_aux s d (.inl c)
        dsimp [Sum.elim, __eo_dtc_substitute, __eo_to_smt_datatype_cons]
        rw [smtx_dtc_substitute_non_datatype s (__eo_to_smt_datatype d)
          (__eo_to_smt_type (Term.Apply f x)) (__eo_to_smt_datatype_cons c)]
        · exact smt_datatype_cons_congr
            (eo_to_smt_type_substitute_typeref s d (Term.Apply f x))
            (by simpa using hc)
        · intro s2 d2
          exact eo_to_smt_type_apply_ne_datatype f x s2 d2
      case DtcAppType T1 T2 =>
        have hc := eo_to_smt_substitute_aux s d (.inl c)
        dsimp [Sum.elim, __eo_dtc_substitute, __eo_to_smt_datatype_cons]
        rw [smtx_dtc_substitute_non_datatype s (__eo_to_smt_datatype d)
          (__eo_to_smt_type (Term.DtcAppType T1 T2)) (__eo_to_smt_datatype_cons c)]
        · exact smt_datatype_cons_congr
            (eo_to_smt_type_substitute_typeref s d (Term.DtcAppType T1 T2))
            (by simpa using hc)
        · intro s2 d2
          exact eo_to_smt_type_dtc_app_ne_datatype T1 T2 s2 d2
      all_goals
        have hc := eo_to_smt_substitute_aux s d (.inl c)
        dsimp [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute]
        exact smt_datatype_cons_congr
          (eo_to_smt_type_substitute_typeref s d _)
          (by simpa using hc)
  | .inr Datatype.null => by
      simp [__eo_dt_substitute, __eo_to_smt_datatype, __smtx_dt_substitute]
  | .inr (Datatype.sum c d0) => by
      have hc := eo_to_smt_substitute_aux s d (.inl c)
      have hd0 := eo_to_smt_substitute_aux s d (.inr d0)
      simpa [__eo_dt_substitute, __eo_to_smt_datatype, __smtx_dt_substitute] using
        And.intro hc hd0
termination_by x => Sum.elim sizeOf sizeOf x
decreasing_by
  all_goals
    first
    | exact sum_size_inl_lt_cons _ _
    | exact sum_size_inr_lt_datatype_cons _ _ _
    | exact sum_size_inl_lt_sum _ _
    | exact sum_size_inr_lt_sum _ _

/-- EO datatype-constructor substitution commutes with type translation. -/
theorem eo_to_smt_datatype_cons_substitute
    (s : native_String) (d : Datatype) (c : DatatypeCons) :
    __eo_to_smt_datatype_cons (__eo_dtc_substitute s d c) =
      __smtx_dtc_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype_cons c) := by
  simpa using eo_to_smt_substitute_aux s d (.inl c)

/-- EO datatype substitution commutes with type translation. -/
theorem eo_to_smt_datatype_substitute
    (s : native_String) (d : Datatype) (d0 : Datatype) :
    __eo_to_smt_datatype (__eo_dt_substitute s d d0) =
      __smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d0) := by
  simpa using eo_to_smt_substitute_aux s d (.inr d0)

/-- Selector return typing commutes with EO-to-SMT type translation. -/
theorem eo_to_smt_type_typeof_dt_sel_return :
    ∀ d : Datatype, ∀ i j : native_Nat,
      __eo_to_smt_type (__eo_typeof_dt_sel_return d i j) =
        __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype d) i j
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_zero => by
      simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons]
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_succ j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons] using
        eo_to_smt_type_typeof_dt_sel_return (Datatype.sum c d) native_nat_zero j
  | Datatype.sum c d, native_nat_succ i, j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons] using
        eo_to_smt_type_typeof_dt_sel_return d i j
  | Datatype.null, i, j => by
      simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_type]
  | Datatype.sum DatatypeCons.unit d, native_nat_zero, j => by
      cases j <;> simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
        __eo_to_smt_datatype, __eo_to_smt_datatype_cons, __eo_to_smt_type]
termination_by d i j => sizeOf d + i + j

/-- Selector return typing commutes with EO-to-SMT type translation on the EO-side substituted datatype. -/
theorem eo_to_smt_type_typeof_dt_sel_return_on_substituted_datatype
    (s : native_String) (d : Datatype) (i j : native_Nat) :
    __eo_to_smt_type (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  simp [__smtx_ret_typeof_sel, eo_to_smt_datatype_substitute,
    eo_to_smt_type_typeof_dt_sel_return]

/--
If the EO argument already has the exact datatype expected by a selector, the
translated EO result type matches the SMT selector return type.
-/
theorem eo_to_smt_type_typeof_apply_dt_sel_of_exact_eo_datatype
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (hx : __eo_typeof x = Term.DatatypeType s d) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  simp [__eo_typeof, __eo_typeof_apply, __eo_requires, hx,
    eo_to_smt_type_typeof_dt_sel_return_on_substituted_datatype,
    native_ite, native_teq, native_not]

end TranslationProofs
