import CpcMini.Proofs.TypePreservation.Datatypes

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace Smtm

private theorem value_dt_substitute_canonical
    (s : native_String)
    (d : SmtDatatype) :
    (v : SmtValue) ->
      __smtx_value_canonical v ->
        __smtx_value_canonical (__smtx_value_dt_substitute s d v)
  | SmtValue.NotValue, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Boolean b, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Numeral n, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Rational q, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Binary w n, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Map m, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Fun m, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Set m, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Seq ss, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Char c, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.UValue i e, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.RegLan r, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.DtCons s' d' i, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Apply f a, h => by
      simp [__smtx_value_canonical, __smtx_value_canonical_bool, native_and] at h
      have hf := value_dt_substitute_canonical s d f h.1
      have ha := value_dt_substitute_canonical s d a h.2
      simp [__smtx_value_dt_substitute, __smtx_value_canonical,
        __smtx_value_canonical_bool, native_and] at hf ha ⊢
      exact ⟨hf, ha⟩

private theorem value_dt_substitute_eq_notValue
    (s : native_String)
    (d : SmtDatatype) :
    (v : SmtValue) ->
      __smtx_value_dt_substitute s d v = SmtValue.NotValue ↔
        v = SmtValue.NotValue
  | SmtValue.NotValue => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Boolean b => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Numeral n => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Rational q => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Binary w n => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Map m => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Fun m => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Set m => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Seq ss => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Char c => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.UValue i e => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.RegLan r => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.DtCons s' d' i => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Apply f a => by
      simp [__smtx_value_dt_substitute]

private theorem value_dt_substitute_ne_notValue
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    __smtx_value_dt_substitute s d v ≠ SmtValue.NotValue := by
  intro hSub
  exact h ((value_dt_substitute_eq_notValue s d v).1 hSub)

private theorem value_ne_notValue_of_type_ne_none
    {v : SmtValue}
    {T : SmtType}
    (hTy : __smtx_typeof_value v = T)
    (hT : T ≠ SmtType.None) :
    v ≠ SmtValue.NotValue := by
  intro hEq
  subst hEq
  simp [__smtx_typeof_value] at hTy
  exact hT hTy.symm

private theorem native_veq_notValue_false_of_ne
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    native_veq v SmtValue.NotValue = false := by
  simpa [native_veq] using h

private theorem ne_notValue_of_native_veq_notValue_false
    {v : SmtValue}
    (h : native_veq v SmtValue.NotValue = false) :
    v ≠ SmtValue.NotValue := by
  intro hEq
  subst hEq
  simp [native_veq] at h

private theorem native_veq_value_dt_substitute_notValue_false
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    native_veq (__smtx_value_dt_substitute s d v) SmtValue.NotValue = false := by
  have hSub := value_dt_substitute_ne_notValue s d h
  exact native_veq_notValue_false_of_ne hSub

private theorem value_dt_substitute_type_default_eq_of_not_datatype
    (s : native_String)
    (d : SmtDatatype)
    (T : SmtType)
    (hDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d') :
    __smtx_value_dt_substitute s d (__smtx_type_default T) =
      __smtx_type_default T := by
  cases T <;> simp [__smtx_type_default, __smtx_value_dt_substitute]
  case Datatype s' d' =>
    exact False.elim (hDatatype s' d' rfl)

private theorem value_dt_substitute_type_default_ne_notValue_of_not_datatype_wf_rec
    (s : native_String)
    (d : SmtDatatype)
    (T : SmtType)
    (refs : RefList)
    (hDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d')
    (hRec : __smtx_type_wf_rec T refs = true) :
    __smtx_value_dt_substitute s d (__smtx_type_default T) ≠
      SmtValue.NotValue := by
  cases T <;>
    simp [__smtx_type_default, __smtx_value_dt_substitute, __smtx_type_wf_rec] at hRec ⊢
  case Datatype s' d' =>
    exact False.elim (hDatatype s' d' rfl)

private def type_dt_substitute_head
    (s : native_String)
    (d : SmtDatatype) : SmtType -> SmtType
  | SmtType.Datatype s' d' => SmtType.Datatype s' (__smtx_dt_substitute s d d')
  | T => native_ite (native_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T

private theorem ret_typeof_sel_rec_dt_substitute
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i j,
      __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d0 d) i j =
        type_dt_substitute_head s d0 (__smtx_ret_typeof_sel_rec d i j)
  | SmtDatatype.null, i, j => by
      cases i <;> cases j <;>
        simp [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec,
          type_dt_substitute_head, native_ite, native_Teq]
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) d, native_nat_zero, native_nat_zero => by
      cases T <;>
        simp [__smtx_dt_substitute, __smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
          type_dt_substitute_head, native_ite, native_Teq]
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) d, native_nat_zero, native_nat_succ j => by
      cases T <;>
        simpa [__smtx_dt_substitute, __smtx_dtc_substitute, __smtx_ret_typeof_sel_rec] using
          ret_typeof_sel_rec_dt_substitute s d0 (SmtDatatype.sum c d) native_nat_zero j
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, j => by
      cases j <;>
        simp [__smtx_dt_substitute, __smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
          type_dt_substitute_head, native_ite, native_Teq]
  | SmtDatatype.sum c d, native_nat_succ i, j => by
      simpa [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec] using
        ret_typeof_sel_rec_dt_substitute s d0 d i j

private theorem type_dt_substitute_head_typeref_eq_self
    (s : native_String)
    (d : SmtDatatype)
    {s' : native_String}
    (h : s' ≠ s) :
    type_dt_substitute_head s d (SmtType.TypeRef s') = SmtType.TypeRef s' := by
  have hType : SmtType.TypeRef s' ≠ SmtType.TypeRef s := by
    intro hEq
    injection hEq with hName
    exact h hName
  simp [type_dt_substitute_head, native_ite, native_Teq, hType]

private theorem type_dt_substitute_head_typeref_eq_current
    (s : native_String)
    (d : SmtDatatype) :
    type_dt_substitute_head s d (SmtType.TypeRef s) = SmtType.Datatype s d := by
  simp [type_dt_substitute_head, native_ite, native_Teq]

private theorem value_dt_substitute_type_default_typeref
    (s : native_String)
    (d : SmtDatatype)
    (s' : native_String) :
    __smtx_value_dt_substitute s d (__smtx_type_default (SmtType.TypeRef s')) =
      SmtValue.NotValue := by
  simp [__smtx_type_default, __smtx_value_dt_substitute]

private theorem ret_typeof_sel_rec_substitute_type_ref_current
    (s : native_String)
    (d0 d : SmtDatatype)
    (i j : native_Nat)
    (h : __smtx_ret_typeof_sel_rec d i j = SmtType.TypeRef s) :
    __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d0 d) i j =
      SmtType.Datatype s d0 := by
  calc
    __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d0 d) i j =
        type_dt_substitute_head s d0 (__smtx_ret_typeof_sel_rec d i j) :=
      ret_typeof_sel_rec_dt_substitute s d0 d i j
    _ = SmtType.Datatype s d0 := by
      simp [h, type_dt_substitute_head_typeref_eq_current]

private theorem datatype_wf_rec_of_type_wf_rec_nil
    {s : native_String}
    {d : SmtDatatype}
    (h : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
    __smtx_dt_wf_rec d (native_reflist_insert native_reflist_nil s) = true := by
  simpa [__smtx_type_wf_rec, native_ite, native_reflist_contains,
    native_reflist_nil, native_reflist_insert] using h

private theorem type_ref_eq_of_contains_singleton
    {s r : native_String}
    (h : native_reflist_contains (native_reflist_insert native_reflist_nil s) r = true) :
    r = s := by
  simpa [native_reflist_contains, native_reflist_insert, native_reflist_nil] using h

private def datatype_cons_default_productive
    (s : native_String)
    (d : SmtDatatype) :
    SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons T c =>
      __smtx_value_dt_substitute s d (__smtx_type_default T) ≠
        SmtValue.NotValue ∧
      datatype_cons_default_productive s d c

private def datatype_cons_default_productive_prefix
    (s : native_String)
    (d : SmtDatatype) :
    SmtDatatypeCons -> native_Nat -> Prop
  | _c, native_nat_zero => True
  | SmtDatatypeCons.unit, native_nat_succ _n => False
  | SmtDatatypeCons.cons T c, native_nat_succ n =>
      __smtx_value_dt_substitute s d (__smtx_type_default T) ≠
        SmtValue.NotValue ∧
      datatype_cons_default_productive_prefix s d c n

private def datatype_default_productive_from
    (s : native_String)
    (d0 : SmtDatatype) :
    SmtDatatype -> Prop
  | SmtDatatype.null => False
  | SmtDatatype.sum c d =>
      datatype_cons_default_productive s d0 c ∨
      datatype_default_productive_from s d0 d

private def datatype_default_productive_prefix_at
    (s : native_String)
    (d0 : SmtDatatype) :
    SmtDatatype -> native_Nat -> native_Nat -> Prop
  | SmtDatatype.null, _i, _n => False
  | SmtDatatype.sum c _d, native_nat_zero, n =>
      datatype_cons_default_productive_prefix s d0 c n
  | SmtDatatype.sum _c d, native_nat_succ i, n =>
      datatype_default_productive_prefix_at s d0 d i n

private theorem datatype_cons_default_productive_of_prefix_full
    (s : native_String)
    (d : SmtDatatype) :
    (c : SmtDatatypeCons) ->
      datatype_cons_default_productive_prefix s d c (__smtx_dtc_num_sels c) ->
        datatype_cons_default_productive s d c
  | SmtDatatypeCons.unit, h => by
      simp [datatype_cons_default_productive]
  | SmtDatatypeCons.cons T c, h => by
      simp [datatype_cons_default_productive_prefix, __smtx_dtc_num_sels] at h
      exact ⟨h.1, datatype_cons_default_productive_of_prefix_full s d c h.2⟩

private theorem datatype_default_productive_from_of_prefix_full_at
    (s : native_String)
    (d0 : SmtDatatype) :
    (d : SmtDatatype) ->
      (i : native_Nat) ->
        datatype_default_productive_prefix_at s d0 d i (__smtx_dt_num_sels d i) ->
          datatype_default_productive_from s d0 d
  | SmtDatatype.null, i, h => by
      cases i <;> simp [datatype_default_productive_prefix_at] at h
  | SmtDatatype.sum c d, native_nat_zero, h => by
      exact Or.inl
        (datatype_cons_default_productive_of_prefix_full s d0 c
          (by simpa [datatype_default_productive_prefix_at, __smtx_dt_num_sels] using h))
  | SmtDatatype.sum c d, native_nat_succ i, h => by
      exact Or.inr
        (datatype_default_productive_from_of_prefix_full_at s d0 d i
          (by simpa [datatype_default_productive_prefix_at, __smtx_dt_num_sels] using h))

private theorem dt_cons_wf_rec_tail_of_cons_true
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases T <;>
    simp [__smtx_dt_cons_wf_rec, native_ite] at h ⊢
  case TypeRef s =>
    cases hRef : native_reflist_contains refs s <;>
      simp [__smtx_dt_cons_wf_rec, native_ite, hRef] at h
    exact h
  all_goals
    exact h.2.2

private theorem dt_cons_wf_rec_parts_of_cons_not_typeref_true
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (hTypeRef : ∀ s, T ≠ SmtType.TypeRef s)
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true) :
    native_inhabited_type T = true ∧
      __smtx_type_wf_rec T refs = true ∧
        __smtx_dt_cons_wf_rec c refs = true := by
  cases T <;>
    simp [__smtx_dt_cons_wf_rec, native_ite, __smtx_type_wf_rec] at h ⊢
  case TypeRef s =>
    exact False.elim (hTypeRef s rfl)
  all_goals
    exact h

private theorem dt_wf_rec_head_of_sum_true
    {c : SmtDatatypeCons}
    {d : SmtDatatype}
    {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases d with
  | null =>
      simpa [__smtx_dt_wf_rec] using h
  | sum c' d' =>
      cases hCons : __smtx_dt_cons_wf_rec c refs <;>
        simp [__smtx_dt_wf_rec, native_ite, hCons] at h
      rfl

private theorem dt_wf_rec_tail_of_sum_sum_true
    {c c' : SmtDatatypeCons}
    {d : SmtDatatype}
    {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c (SmtDatatype.sum c' d)) refs = true) :
    __smtx_dt_wf_rec (SmtDatatype.sum c' d) refs = true := by
  cases hCons : __smtx_dt_cons_wf_rec c refs <;>
    simp [__smtx_dt_wf_rec, native_ite, hCons] at h
  exact h

private theorem datatype_cons_default_ne_notValue_of_productive
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (hv : v ≠ SmtValue.NotValue) :
    (c : SmtDatatypeCons) ->
      datatype_cons_default_productive s d c ->
        __smtx_datatype_cons_default s d v c ≠ SmtValue.NotValue
  | SmtDatatypeCons.unit, _hProd => by
      simpa [__smtx_datatype_cons_default] using hv
  | SmtDatatypeCons.cons T c, hProd => by
      have hArg :
          __smtx_value_dt_substitute s d (__smtx_type_default T) ≠
            SmtValue.NotValue := hProd.1
      have hArgVeq :
          native_veq
              (__smtx_value_dt_substitute s d (__smtx_type_default T))
              SmtValue.NotValue = false :=
        native_veq_notValue_false_of_ne hArg
      have hApply :
          SmtValue.Apply v
              (__smtx_value_dt_substitute s d (__smtx_type_default T)) ≠
            SmtValue.NotValue := by
        intro hEq
        cases hEq
      simpa [__smtx_datatype_cons_default, hArgVeq, native_ite] using
        datatype_cons_default_ne_notValue_of_productive s d hApply c hProd.2

private theorem datatype_default_ne_notValue_of_productive_from
    (s : native_String)
    (d0 : SmtDatatype) :
    (d : SmtDatatype) ->
      (n : native_Nat) ->
        datatype_default_productive_from s d0 d ->
          __smtx_datatype_default s d0 d n ≠ SmtValue.NotValue
  | SmtDatatype.null, n, hProd => by
      simp [datatype_default_productive_from] at hProd
  | SmtDatatype.sum c d, n, hProd => by
      cases hProd with
      | inl hCons =>
          have hConsNV :
              __smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c ≠
                SmtValue.NotValue :=
            datatype_cons_default_ne_notValue_of_productive s d0 (by intro h; cases h) c hCons
          have hConsVeq :
              native_veq
                  (__smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c)
                  SmtValue.NotValue = false :=
            native_veq_notValue_false_of_ne hConsNV
          simpa [__smtx_datatype_default, hConsVeq, native_not, native_ite] using hConsNV
      | inr hTail =>
          cases hConsVeq :
              native_veq
                (__smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c)
                SmtValue.NotValue
          · have hConsNV :
                __smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c ≠
                  SmtValue.NotValue :=
              ne_notValue_of_native_veq_notValue_false hConsVeq
            simpa [__smtx_datatype_default, hConsVeq, native_not, native_ite] using hConsNV
          · simpa [__smtx_datatype_default, hConsVeq, native_not, native_ite] using
              datatype_default_ne_notValue_of_productive_from s d0 d
                (native_nat_succ n) hTail

private theorem value_head_dt_cons_of_chain_type :
    (v : SmtValue) ->
      (T : SmtType) ->
        dt_cons_chain_result T ->
          T ≠ SmtType.None ->
            __smtx_typeof_value v = T ->
              ∃ s d i, __vsm_apply_head v = SmtValue.DtCons s d i
  | SmtValue.NotValue, T, hChain, hNN, hTy => by
      simp [__smtx_typeof_value] at hTy
      exact False.elim (hNN hTy.symm)
  | SmtValue.Boolean b, T, hChain, hNN, hTy => by
      subst T
      simp [__smtx_typeof_value, dt_cons_chain_result] at hChain
  | SmtValue.Numeral n, T, hChain, hNN, hTy => by
      subst T
      simp [__smtx_typeof_value, dt_cons_chain_result] at hChain
  | SmtValue.Rational q, T, hChain, hNN, hTy => by
      subst T
      simp [__smtx_typeof_value, dt_cons_chain_result] at hChain
  | SmtValue.Binary w n, T, hChain, hNN, hTy => by
      cases hBin :
          native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [__smtx_typeof_value, hBin] at hTy
      · exact False.elim (hNN hTy.symm)
      · cases T <;> simp [native_ite, dt_cons_chain_result] at hChain hTy
  | SmtValue.Map m, T, hChain, hNN, hTy => by
      cases typeof_map_value_shape m with
      | inl h =>
          rcases h with ⟨A, B, hMap⟩
          cases T <;> simp [__smtx_typeof_value, hMap, dt_cons_chain_result] at hChain hTy
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hTy
          exact False.elim (hNN hTy.symm)
  | SmtValue.Fun m, T, hChain, hNN, hTy => by
      cases typeof_map_value_shape m with
      | inl h =>
          rcases h with ⟨A, B, hMap⟩
          cases T <;>
            simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap,
              dt_cons_chain_result] at hChain hTy
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at hTy
          exact False.elim (hNN hTy.symm)
  | SmtValue.Set m, T, hChain, hNN, hTy => by
      cases typeof_map_value_shape m with
      | inl h =>
          rcases h with ⟨A, B, hMap⟩
          cases B <;> cases T <;>
            simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap,
              dt_cons_chain_result] at hChain hTy
          all_goals first | contradiction | exact False.elim (hNN rfl)
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at hTy
          exact False.elim (hNN hTy.symm)
  | SmtValue.Seq ss, T, hChain, hNN, hTy => by
      cases typeof_seq_value_shape ss with
      | inl h =>
          rcases h with ⟨A, hSeq⟩
          cases T <;> simp [__smtx_typeof_value, hSeq, dt_cons_chain_result] at hChain hTy
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hTy
          exact False.elim (hNN hTy.symm)
  | SmtValue.Char c, T, hChain, hNN, hTy => by
      subst T
      simp [__smtx_typeof_value, dt_cons_chain_result] at hChain
  | SmtValue.UValue i e, T, hChain, hNN, hTy => by
      subst T
      simp [__smtx_typeof_value, dt_cons_chain_result] at hChain
  | SmtValue.RegLan r, T, hChain, hNN, hTy => by
      subst T
      simp [__smtx_typeof_value, dt_cons_chain_result] at hChain
  | SmtValue.DtCons s d i, T, hChain, hNN, hTy => by
      exact ⟨s, d, i, by simp [__vsm_apply_head]⟩
  | SmtValue.Apply f a, T, hChain, hNN, hTy => by
      have hApplyNN :
          __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value a) ≠
            SmtType.None := by
        intro hNone
        apply hNN
        simpa [__smtx_typeof_value, hNone] using hTy.symm
      rcases typeof_apply_value_non_none_cases hApplyNN with
        ⟨A, B, hF, hA, hANone, hBNone⟩
      have hBT : B = T := by
        have hApply :
            __smtx_typeof_apply_value (SmtType.DtcAppType A B) A = T := by
          simpa [__smtx_typeof_value, hF, hA] using hTy
        simpa [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite,
          native_Teq, hANone] using hApply
      have hChainF : dt_cons_chain_result (SmtType.DtcAppType A B) := by
        simp [dt_cons_chain_result, hBT, hChain]
      have hHead :=
        value_head_dt_cons_of_chain_type f (SmtType.DtcAppType A B) hChainF
          (by simp) hF
      rcases hHead with ⟨s, d, i, hHead⟩
      exact ⟨s, d, i, by simpa [__vsm_apply_head] using hHead⟩

private theorem typeof_dt_cons_value_rec_datatype_components
    {s0 s : native_String}
    {d0 dTarget : SmtDatatype} :
    ∀ d i,
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s0 d0) d i =
        SmtType.Datatype s dTarget ->
          s0 = s ∧ d0 = dTarget
  | SmtDatatype.null, i, h => by
      cases i <;> simp [__smtx_typeof_dt_cons_value_rec] at h
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, h => by
      simp [__smtx_typeof_dt_cons_value_rec] at h
      exact h
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero, h => by
      simp [__smtx_typeof_dt_cons_value_rec] at h
  | SmtDatatype.sum c d, native_nat_succ i, h => by
      simpa [__smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_datatype_components d i
          (by simpa [__smtx_typeof_dt_cons_value_rec] using h)

private theorem dt_cons_applied_type_rec_datatype_components
    {s0 s : native_String}
    {d0 dTarget : SmtDatatype} :
    ∀ d i n,
      dt_cons_applied_type_rec s0 d0 d i n = SmtType.Datatype s dTarget ->
        s0 = s ∧ d0 = dTarget
  | d, i, 0, h => by
      exact typeof_dt_cons_value_rec_datatype_components d i
        (by simpa [dt_cons_applied_type_rec] using h)
  | SmtDatatype.null, i, Nat.succ n, h => by
      cases i <;> simp [dt_cons_applied_type_rec] at h
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, Nat.succ n, h => by
      simp [dt_cons_applied_type_rec] at h
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n, h => by
      exact dt_cons_applied_type_rec_datatype_components
        (d := SmtDatatype.sum c d) (i := 0) (n := n)
        (by simpa [dt_cons_applied_type_rec] using h)
  | SmtDatatype.sum c d, Nat.succ i, Nat.succ n, h => by
      exact dt_cons_applied_type_rec_datatype_components
        (d := d) (i := i) (n := Nat.succ n)
        (by simpa [dt_cons_applied_type_rec] using h)

private theorem value_head_dt_cons_components_of_datatype_type
    {v : SmtValue}
    {s s' : native_String}
    {d d' : SmtDatatype}
    {i : native_Nat}
    (hHead : __vsm_apply_head v = SmtValue.DtCons s' d' i)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    s' = s ∧ d' = d := by
  have hChain := dt_cons_chain_type_of_non_none hHead (by simp [hTy])
  have hEq :
      dt_cons_applied_type_rec s' d' (__smtx_dt_substitute s' d' d') i
          (vsm_num_apply_args v) =
        SmtType.Datatype s d := by
    simpa [hTy] using hChain.symm
  exact dt_cons_applied_type_rec_datatype_components
    (d := __smtx_dt_substitute s' d' d') (i := i) (n := vsm_num_apply_args v) hEq

private theorem vsm_apply_arg_nth_size_lt :
    (v : SmtValue) ->
      {j : native_Nat} ->
        j < vsm_num_apply_args v ->
          sizeOf (__vsm_apply_arg_nth v j (vsm_num_apply_args v)) < sizeOf v
  | SmtValue.Apply f a, j, hj => by
      by_cases hLast : j = vsm_num_apply_args f
      · subst hLast
        have hcond :
            SmtEval.native_nateq (vsm_num_apply_args f) (vsm_num_apply_args f) = true := by
          simp [SmtEval.native_nateq]
        simp [__vsm_apply_arg_nth, vsm_num_apply_args, hcond, native_ite]
        omega
      · have hj' : j < vsm_num_apply_args f := by
          have hjSucc : j < Nat.succ (vsm_num_apply_args f) := by
            simpa [vsm_num_apply_args] using hj
          have hle : j ≤ vsm_num_apply_args f := Nat.lt_succ_iff.mp hjSucc
          cases Nat.eq_or_lt_of_le hle with
          | inl hEq => exact False.elim (hLast hEq)
          | inr hLt => exact hLt
        have hcond :
            SmtEval.native_nateq j (vsm_num_apply_args f) = false := by
          simp [SmtEval.native_nateq, hLast]
        have hlt := vsm_apply_arg_nth_size_lt f hj'
        simp [__vsm_apply_arg_nth, vsm_num_apply_args, hcond, native_ite]
        omega
  | SmtValue.NotValue, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Boolean b, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Numeral n, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Rational q, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Binary w n, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Map m, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Fun m, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Set m, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Seq ss, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Char c, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.UValue i e, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.RegLan r, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.DtCons s d i, j, hj => by
      simp [vsm_num_apply_args] at hj

private theorem datatype_type_default_typed_canonical_of_typed_value
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList)
    (v : SmtValue)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype s d) refs = true) :
      __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  have hHead :
      ∃ i, __vsm_apply_head v = SmtValue.DtCons s d i := by
    rcases value_head_dt_cons_of_chain_type v (SmtType.Datatype s d)
        (by simp [dt_cons_chain_result])
        (by simp)
        hTy with ⟨s', d', i, hHead'⟩
    have hComponents :=
      value_head_dt_cons_components_of_datatype_type hHead' hTy
    rcases hComponents with ⟨rfl, rfl⟩
    exact ⟨i, hHead'⟩
  rcases hHead with ⟨i, hHead⟩
  have hArgCount :
      vsm_num_apply_args v = __smtx_dt_num_sels (__smtx_dt_substitute s d d) i :=
    vsm_num_apply_args_eq_dt_num_sels_of_datatype hHead hTy
  have hArgCountOrig :
      vsm_num_apply_args v = __smtx_dt_num_sels d i := by
    simpa [dt_num_sels_substitute] using hArgCount
  have hDtWf :
      __smtx_dt_wf_rec d (native_reflist_insert refs s) = true := by
    cases hContains : native_reflist_contains refs s <;>
      simp [__smtx_type_wf_rec, native_ite, hContains] at hRec
    exact hRec
  -- The proof should now follow the constructor path exposed by `hHead`,
  -- using recursive arguments as evidence that some later constructor is
  -- productive, and non-recursive arguments to justify their default values.
  sorry

/--
If a datatype is semantically inhabited and recursively well-formed, the
generated constructor-search default is a canonical value of that datatype.
-/
theorem cpcmini_datatype_type_default_typed_canonical_assumption
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
      __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  classical
  have hInh :
      ∃ v : SmtValue, __smtx_typeof_value v = SmtType.Datatype s d := by
    simpa [native_inhabited_type] using _hInh
  rcases hInh with ⟨v, hTy⟩
  exact datatype_type_default_typed_canonical_of_typed_value s d native_reflist_nil v hTy _hRec

private theorem datatype_type_default_typed_canonical_of_wf_rec
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
      __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  exact cpcmini_datatype_type_default_typed_canonical_assumption s d _hInh _hRec

private theorem type_default_typed_canonical_of_wf_rec :
    (T : SmtType) ->
      native_inhabited_type T = true ->
        __smtx_type_wf_rec T native_reflist_nil = true ->
          __smtx_typeof_value (__smtx_type_default T) = T ∧
            __smtx_value_canonical (__smtx_type_default T)
  | SmtType.None, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.Bool, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Int, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Real, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.RegLan, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.BitVec w, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, native_ite, native_and,
          native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total,
          native_nat_to_int, native_int_to_nat]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, native_ite, native_zleq, native_zeq,
          native_mod_total, native_int_pow2, native_zexp_total, native_nat_to_int]
  | SmtType.Map A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hB := type_default_typed_canonical_of_wf_rec B hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.Set A, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq, __smtx_typeof_value, __smtx_type_default]
  | SmtType.Seq A, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_seq_value,
        __smtx_value_canonical, __smtx_value_canonical_bool, __smtx_seq_canonical]
  | SmtType.Char, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Datatype s d, hInh, hRec => by
      exact datatype_type_default_typed_canonical_of_wf_rec s d hInh hRec
  | SmtType.TypeRef s, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.USort i, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.FunType A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hB := type_default_typed_canonical_of_wf_rec B hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_fun_type, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.DtcAppType A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
termination_by T _ _ => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals omega

private theorem type_default_ne_notValue_of_wf_rec
    (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T native_reflist_nil = true) :
    __smtx_type_default T ≠ SmtValue.NotValue := by
  have hDef := type_default_typed_canonical_of_wf_rec T hInh hRec
  have hT : T ≠ SmtType.None := by
    intro hNone
    cases T <;> simp [__smtx_type_wf_rec] at hRec hNone
  exact value_ne_notValue_of_type_ne_none hDef.1 hT

/-- Every well-formed Mini SMT type has a canonical inhabitant. -/
theorem canonical_type_inhabited_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl, by
      simp [__smtx_value_canonical, __smtx_value_canonical_bool]⟩
  · have hParts :
        native_inhabited_type T = true ∧
          __smtx_type_wf_rec T native_reflist_nil = true := by
      cases T <;> simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hWF hReg ⊢ <;>
        exact hWF
    have hDef :=
      type_default_typed_canonical_of_wf_rec T hParts.1 hParts.2
    exact ⟨__smtx_type_default T, hDef.1, hDef.2⟩

end Smtm
