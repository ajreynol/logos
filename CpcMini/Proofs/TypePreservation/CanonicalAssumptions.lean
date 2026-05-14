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

private def datatype_cons_default_productive
    (s : native_String)
    (d : SmtDatatype) :
    SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons T c =>
      __smtx_value_dt_substitute s d (__smtx_type_default T) ≠
        SmtValue.NotValue ∧
      datatype_cons_default_productive s d c

private def datatype_default_productive_from
    (s : native_String)
    (d0 : SmtDatatype) :
    SmtDatatype -> Prop
  | SmtDatatype.null => False
  | SmtDatatype.sum c d =>
      datatype_cons_default_productive s d0 c ∨
      datatype_default_productive_from s d0 d

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

private theorem datatype_type_default_typed_canonical_of_typed_value
    (s : native_String)
    (d : SmtDatatype)
    (v : SmtValue)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
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
  exact datatype_type_default_typed_canonical_of_typed_value s d v hTy _hRec

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
