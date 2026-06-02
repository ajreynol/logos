import Cpc.Proofs.RuleSupport.SetsMemberSupport
import Cpc.Proofs.RuleSupport.ArraySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace SetsEvalOpSupport

open SetsMemberSupport

/--
`listLookup M L v` is the membership characteristic value of `v` in the model
interpretation of a cons-shaped element list `L` (a `@@TypedList` produced by
`__set_union_to_list` / `__eval_sets_op`, or a raw `__eo_List` produced by
`__eo_get_elements_rec`). It returns `Boolean true` iff the model value `v` equals
the model evaluation of some element term of `L`, mirroring the SMT model lookups
of a union-of-singletons set value.
-/
noncomputable def listLookup (M : SmtModel) : Term -> SmtValue -> SmtValue
  | Term.Apply (Term.Apply _ x) y, v =>
      native_ite (native_veq (__smtx_model_eval M (__eo_to_smt x)) v)
        (SmtValue.Boolean true) (listLookup M y v)
  | _, v => SmtValue.Boolean false

theorem listLookup_cons (M : SmtModel) (f x y : Term) (v : SmtValue) :
    listLookup M (Term.Apply (Term.Apply f x) y) v =
      native_ite (native_veq (__smtx_model_eval M (__eo_to_smt x)) v)
        (SmtValue.Boolean true) (listLookup M y v) := by
  rfl

/-! ### Foundational set-value lemmas -/

/-- The default leaf of a canonical, Bool-valued, default-false set map is
`SmtMap.default A (Boolean false)`. -/
theorem set_default_leaf :
    ∀ {m : SmtMap} {A : SmtType},
      __smtx_map_canonical m = true ->
      __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool ->
      __smtx_msm_get_default m = SmtValue.Boolean false ->
      smt_map_default_leaf m = SmtMap.default A (SmtValue.Boolean false)
  | SmtMap.default T e, A, _hCan, hTy, hDef => by
      have hT : T = A := by
        have := hTy
        simp [__smtx_typeof_map_value] at this
        exact this.1
      have he : e = SmtValue.Boolean false := by
        simpa [__smtx_msm_get_default] using hDef
      subst hT; subst he
      rfl
  | SmtMap.cons k v m, A, hCan, hTy, hDef => by
      have hTailTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool :=
        map_cons_tail_type hTy
      have hTailCan : __smtx_map_canonical m = true :=
        map_cons_tail_canonical hCan
      have hTailDef : __smtx_msm_get_default m = SmtValue.Boolean false := by
        simpa [__smtx_msm_get_default] using hDef
      have hRec := set_default_leaf hTailCan hTailTy hTailDef
      simpa [smt_map_default_leaf] using hRec

/-- Lookup of a union of two canonical, Bool-valued, default-false set maps. -/
theorem set_union_lookup
    (m1 m2 : SmtMap) (A : SmtType) (v : SmtValue)
    (h1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool)
    (h2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool)
    (h1Can : __smtx_map_canonical m1 = true)
    (h2Can : __smtx_map_canonical m2 = true)
    (h1Def : __smtx_msm_get_default m1 = SmtValue.Boolean false) :
    __smtx_msm_lookup
        (__smtx_mss_op_internal false m1
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false)) m2) v =
      native_ite
        (native_veq (__smtx_msm_lookup m1 v) (SmtValue.Boolean true))
        (SmtValue.Boolean true)
        (__smtx_msm_lookup m2 v) := by
  have hEmptyTy :
      __smtx_typeof_map_value
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false)) = SmtType.Map A SmtType.Bool := by
    rw [h1Ty]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value, __smtx_typeof_value]
  have hRec :=
    mss_op_lookup_acc false (m1 := m1)
      (m2 := SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
        (SmtValue.Boolean false))
      (acc := m2) (A := A) (i := v) h1Ty hEmptyTy h2Ty h1Can h2Can h1Def
  rw [hRec]
  simp [__smtx_msm_lookup, native_veq, native_iff, SmtEval.native_and, native_ite]

/-- The model value of a set-typed translated term is a canonical, Bool-valued,
default-false set map. -/
theorem set_value_facts
    (M : SmtModel) (hM : model_total_typed M) (t : Term) (A : SmtType)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTyA : __smtx_typeof (__eo_to_smt t) = SmtType.Set A) :
    ∃ m : SmtMap,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Set m ∧
        __smtx_map_canonical m = true ∧
          __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool ∧
            __smtx_msm_get_default m = SmtValue.Boolean false := by
  have hCanEval : __smtx_value_canonical (__smtx_model_eval M (__eo_to_smt t)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM t hTrans
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Set A := by
    simpa [hTyA] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by
          simpa [term_has_non_none_type, RuleProofs.eo_has_smt_translation]
            using hTrans)
  rcases set_value_canonical hEvalTy with ⟨m, hm⟩
  have hCanSet : __smtx_value_canonical (SmtValue.Set m) := by
    simpa [hm] using hCanEval
  have hmCan : __smtx_map_canonical m = true := by
    have hParts := hCanSet
    simp [__smtx_value_canonical, __smtx_value_canonical_bool, SmtEval.native_and]
      at hParts
    exact hParts.1
  have hmDef : __smtx_msm_get_default m = SmtValue.Boolean false := by
    have hParts := hCanSet
    simp [__smtx_value_canonical, __smtx_value_canonical_bool, SmtEval.native_and]
      at hParts
    exact eq_of_native_veq_true hParts.2
  have hmTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool :=
    set_map_value_typed (by simpa [hm] using hEvalTy)
  exact ⟨m, hm, hmCan, hmTy, hmDef⟩

/-! ### Element-list predicate and list-level lemmas -/

/-- A cons-shaped element list: a chain of `Apply (Apply _ _)` cells terminating in
a non-`Stuck`, non-cons terminator (e.g. a `@@TypedList_nil`/`__eo_List_nil`). -/
def IsElemList : Term -> Prop
  | Term.Apply (Term.Apply f x) y => f ≠ Term.Stuck ∧ x ≠ Term.Stuck ∧ IsElemList y
  | Term.Stuck => False
  | _ => True

theorem isElemList_ne_stuck {L : Term} (h : IsElemList L) : L ≠ Term.Stuck := by
  intro hStuck; rw [hStuck] at h; exact h

theorem mk_apply_of_ne_stuck {a w : Term} (ha : a ≠ Term.Stuck) (hw : w ≠ Term.Stuck) :
    __eo_mk_apply a w = Term.Apply a w := by
  cases a <;> cases w <;> simp_all [__eo_mk_apply]

/-- Reduction of `__eo_list_concat_rec` on a cons cell with non-`Stuck` second list. -/
theorem concat_rec_cons (f x y z : Term) (hz : z ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) y) z =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec y z) := by
  cases z <;> first | (exact absurd rfl hz) | rfl

/-- `__eo_list_concat_rec` of a proper list onto a non-`Stuck` list is non-`Stuck`. -/
theorem concat_rec_ne_stuck :
    ∀ L1 L2 : Term, IsElemList L1 -> L2 ≠ Term.Stuck ->
      __eo_list_concat_rec L1 L2 ≠ Term.Stuck := by
  intro L1 L2
  induction L1, L2 using __eo_list_concat_rec.induct with
  | case1 z => intro hL1 _; exact absurd hL1 (by simp [IsElemList])
  | case2 t ht => intro _ hL2; exact absurd rfl hL2
  | case3 f x y z hz ih =>
      intro hL1 hL2
      have hb : IsElemList y := hL1.2.2
      have hTail : __eo_list_concat_rec y z ≠ Term.Stuck := ih hb hL2
      rw [concat_rec_cons f x y z hL2, mk_apply_of_ne_stuck (by simp) hTail]
      simp
  | case4 nil z hns hzs hncons =>
      intro hL1 hL2
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      rw [hEq]; exact hL2

/-- `listLookup` distributes over `__eo_list_concat_rec` for a proper left list. -/
theorem listLookup_concat
    (M : SmtModel) (v : SmtValue) :
    ∀ L1 L2 : Term,
      IsElemList L1 -> L2 ≠ Term.Stuck ->
      listLookup M (__eo_list_concat_rec L1 L2) v =
        native_ite (native_veq (listLookup M L1 v) (SmtValue.Boolean true))
          (SmtValue.Boolean true) (listLookup M L2 v) := by
  intro L1 L2
  induction L1, L2 using __eo_list_concat_rec.induct with
  | case1 z => intro hL1 _; exact absurd hL1 (by simp [IsElemList])
  | case2 t ht => intro _ hL2; exact absurd rfl hL2
  | case3 f x y z hz ih =>
      intro hL1 hL2
      have hb : IsElemList y := hL1.2.2
      have hTail : __eo_list_concat_rec y z ≠ Term.Stuck :=
        concat_rec_ne_stuck y z hb hL2
      rw [concat_rec_cons f x y z hL2, mk_apply_of_ne_stuck (by simp) hTail,
        listLookup_cons, ih hb hL2, listLookup_cons]
      cases h : native_veq (__smtx_model_eval M (__eo_to_smt x)) v <;>
        simp [native_ite, native_veq, h]
  | case4 nil z hns hzs hncons =>
      intro hL1 hL2
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      have hLnil : listLookup M nil v = SmtValue.Boolean false := by
        unfold listLookup
        split <;> simp_all
      rw [hEq, hLnil]
      simp [native_ite, native_veq]

/-! ### Normal-form lookup equals listLookup -/

/-- For a union-of-singletons normal form `nf` (one on which `__set_union_to_list`
succeeds), the model lookup of `nf`'s set value at `v` equals `listLookup` of the
element list of `nf`. -/
theorem set_nf_lookup
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ (nf : Term) (m : SmtMap) (v : SmtValue),
      __set_union_to_list nf ≠ Term.Stuck ->
      RuleProofs.eo_has_smt_translation nf ->
      __smtx_model_eval M (__eo_to_smt nf) = SmtValue.Set m ->
      __smtx_msm_lookup m v = listLookup M (__set_union_to_list nf) v := by
  sorry

/-! ### setof preserves membership, meq implies membership equality -/

/-- `__eo_eq` of two non-`Stuck` terms is the Boolean of their decidable equality. -/
theorem eo_eq_val (a b : Term) (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __eo_eq a b = Term.Boolean (native_teq b a) := by
  unfold __eo_eq; split <;> simp_all

theorem prepend_if_keep (f x res : Term)
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) (hres : res ≠ Term.Stuck) :
    __eo_prepend_if (Term.Boolean true) f x res = Term.Apply (Term.Apply f x) res := by
  unfold __eo_prepend_if; split <;> simp_all

theorem prepend_if_drop (f x res : Term)
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) (hres : res ≠ Term.Stuck) :
    __eo_prepend_if (Term.Boolean false) f x res = res := by
  unfold __eo_prepend_if; split <;> simp_all

theorem erase_all_rec_cons (f x y z : Term) (hz : z ≠ Term.Stuck) :
    __eo_list_erase_all_rec (Term.Apply (Term.Apply f x) y) z =
      __eo_prepend_if (__eo_not (__eo_eq z x)) f x (__eo_list_erase_all_rec y z) := by
  cases z <;> first | (exact absurd rfl hz) | rfl

/-- `__eo_list_erase_all_rec` preserves the element-list invariant. -/
theorem erase_all_isElemList :
    ∀ L z : Term, IsElemList L -> z ≠ Term.Stuck ->
      IsElemList (__eo_list_erase_all_rec L z) := by
  intro L z
  induction L, z using __eo_list_erase_all_rec.induct with
  | case1 z => intro hL _; exact absurd hL (by simp [IsElemList])
  | case2 t ht => intro _ hz; exact absurd rfl hz
  | case3 f x y z hz ih =>
      intro hL hzs
      obtain ⟨hf, hx, hy⟩ := hL
      have hTail : IsElemList (__eo_list_erase_all_rec y z) := ih hy hzs
      have hTailNS := isElemList_ne_stuck hTail
      rw [erase_all_rec_cons f x y z hzs, eo_eq_val z x hzs hx]
      cases hxz : native_teq x z
      · rw [show __eo_not (Term.Boolean false) = Term.Boolean true by decide,
          prepend_if_keep f x _ hf hx hTailNS]
        exact ⟨hf, hx, hTail⟩
      · rw [show __eo_not (Term.Boolean true) = Term.Boolean false by decide,
          prepend_if_drop f x _ hf hx hTailNS]
        exact hTail
  | case4 nil z hns hzs hncons =>
      intro hL _
      have hEq : __eo_list_erase_all_rec nil z = nil := by
        unfold __eo_list_erase_all_rec; split <;> simp_all
      rw [hEq]; exact hL

/-- Erasing all syntactic copies of `z` does not change membership of `v` when `v`
is not the model value of `z`. -/
theorem erase_all_mem (M : SmtModel) (v : SmtValue) :
    ∀ L z : Term, IsElemList L -> z ≠ Term.Stuck ->
      native_veq (__smtx_model_eval M (__eo_to_smt z)) v = false ->
      listLookup M (__eo_list_erase_all_rec L z) v = listLookup M L v := by
  intro L z
  induction L, z using __eo_list_erase_all_rec.induct with
  | case1 z => intro hL _ _; exact absurd hL (by simp [IsElemList])
  | case2 t ht => intro _ hz _; exact absurd rfl hz
  | case3 f x y z hz ih =>
      intro hL hzs hveq
      obtain ⟨hf, hx, hy⟩ := hL
      have hTail : IsElemList (__eo_list_erase_all_rec y z) :=
        erase_all_isElemList y z hy hzs
      have hTailNS := isElemList_ne_stuck hTail
      have ihm := ih hy hzs hveq
      rw [erase_all_rec_cons f x y z hzs, eo_eq_val z x hzs hx]
      cases hxz : native_teq x z
      · rw [show __eo_not (Term.Boolean false) = Term.Boolean true by decide,
          prepend_if_keep f x _ hf hx hTailNS, listLookup_cons, ihm, listLookup_cons]
      · rw [show __eo_not (Term.Boolean true) = Term.Boolean false by decide,
          prepend_if_drop f x _ hf hx hTailNS, ihm, listLookup_cons]
        have hxe : x = z := of_decide_eq_true hxz
        rw [hxe, hveq]; simp [native_ite]
  | case4 nil z hns hzs hncons =>
      intro hL _ _
      have hEq : __eo_list_erase_all_rec nil z = nil := by
        unfold __eo_list_erase_all_rec; split <;> simp_all
      rw [hEq]

theorem setof_rec_cons (f x y : Term) :
    __eo_list_setof_rec (Term.Apply (Term.Apply f x) y) =
      __eo_mk_apply (Term.Apply f x)
        (__eo_list_erase_all_rec (__eo_list_setof_rec y) x) := rfl

/-- `__eo_list_setof_rec` preserves the element-list invariant. -/
theorem setof_rec_isElemList :
    ∀ L : Term, IsElemList L -> IsElemList (__eo_list_setof_rec L) := by
  intro L
  induction L using __eo_list_setof_rec.induct with
  | case1 => intro hL; exact absurd hL (by simp [IsElemList])
  | case2 f x y ih =>
      intro hL
      obtain ⟨hf, hx, hy⟩ := hL
      have hSy := ih hy
      have hEr := erase_all_isElemList (__eo_list_setof_rec y) x hSy hx
      have hErNS := isElemList_ne_stuck hEr
      rw [setof_rec_cons, mk_apply_of_ne_stuck (by simp) hErNS]
      exact ⟨hf, hx, hEr⟩
  | case3 nil hns hncons =>
      intro hL
      have hEq : __eo_list_setof_rec nil = nil := by
        unfold __eo_list_setof_rec; split <;> simp_all
      rw [hEq]; exact hL

theorem listLookup_setof
    (M : SmtModel) (v : SmtValue) :
    ∀ L : Term,
      IsElemList L ->
      listLookup M (__eo_list_setof_rec L) v = listLookup M L v := by
  intro L
  induction L using __eo_list_setof_rec.induct with
  | case1 => intro hL; exact absurd hL (by simp [IsElemList])
  | case2 f x y ih =>
      intro hL
      obtain ⟨hf, hx, hy⟩ := hL
      have hSy := setof_rec_isElemList y hy
      have hEr := erase_all_isElemList (__eo_list_setof_rec y) x hSy hx
      have hErNS := isElemList_ne_stuck hEr
      have ihm := ih hy
      rw [setof_rec_cons, mk_apply_of_ne_stuck (by simp) hErNS, listLookup_cons,
        listLookup_cons]
      cases hxv : native_veq (__smtx_model_eval M (__eo_to_smt x)) v
      · simp only [native_ite]
        rw [erase_all_mem M v (__eo_list_setof_rec y) x hSy hx hxv, ihm]
      · simp [native_ite]
  | case3 nil hns hncons =>
      intro hL
      have hEq : __eo_list_setof_rec nil = nil := by
        unfold __eo_list_setof_rec; split <;> simp_all
      rw [hEq]

/-! #### `__eo_requires` / `__eo_and` / `__eo_ite` reductions -/

theorem req_arg_eq {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) : x = y := by
  by_cases hxy : x = y
  · exact hxy
  · exact absurd (by simp [__eo_requires, native_teq, native_ite, hxy]) h

theorem req_left_ne {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx; subst hx
  have hxy : Term.Stuck = y := req_arg_eq h
  subst hxy
  simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not] at h

theorem req_result {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) :
    __eo_requires x y z = z := by
  have hxy : x = y := req_arg_eq h
  have hx : x ≠ Term.Stuck := req_left_ne h
  subst hxy
  cases x <;> simp [__eo_requires, native_teq, native_ite, native_not,
    SmtEval.native_not] at hx ⊢

theorem eo_and_eq_true {p q : Term} (h : __eo_and p q = Term.Boolean true) :
    p = Term.Boolean true ∧ q = Term.Boolean true := by
  cases p <;> cases q <;>
    simp_all [__eo_and, native_and, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not, Bool.and_eq_true] <;>
    split at h <;> simp_all

theorem eo_ite_true (yes no : Term) : __eo_ite (Term.Boolean true) yes no = yes := rfl

theorem eo_ite_false (yes no : Term) : __eo_ite (Term.Boolean false) yes no = no := rfl

/-! #### `__eo_list_erase_rec` lemmas -/

theorem erase_rec_cons (f w y t : Term) (ht : t ≠ Term.Stuck) :
    __eo_list_erase_rec (Term.Apply (Term.Apply f w) y) t =
      __eo_ite (__eo_eq w t) y
        (__eo_mk_apply (Term.Apply f w) (__eo_list_erase_rec y t)) := by
  cases t <;> first | (exact absurd rfl ht) | rfl

theorem erase_rec_isElemList :
    ∀ L t : Term, IsElemList L -> t ≠ Term.Stuck ->
      IsElemList (__eo_list_erase_rec L t) := by
  intro L t
  induction L, t using __eo_list_erase_rec.induct with
  | case1 z => intro hL _; exact absurd hL (by simp [IsElemList])
  | case2 s hs => intro _ ht; exact absurd rfl ht
  | case3 f w y t ht ih =>
      intro hL hts
      obtain ⟨hf, hw, hy⟩ := hL
      have hTail := ih hy hts
      have hTailNS := isElemList_ne_stuck hTail
      rw [erase_rec_cons f w y t hts, eo_eq_val w t hw hts]
      cases htw : native_teq t w
      · rw [eo_ite_false, mk_apply_of_ne_stuck (by simp) hTailNS]
        exact ⟨hf, hw, hTail⟩
      · rw [eo_ite_true]; exact hy
  | case4 nil t hns hts hncons =>
      intro hL _
      have hEq : __eo_list_erase_rec nil t = nil := by
        unfold __eo_list_erase_rec; split <;> simp_all
      rw [hEq]; exact hL

theorem erase_mono (M : SmtModel) (v : SmtValue) :
    ∀ L t : Term, IsElemList L -> t ≠ Term.Stuck ->
      listLookup M (__eo_list_erase_rec L t) v = SmtValue.Boolean true ->
      listLookup M L v = SmtValue.Boolean true := by
  intro L t
  induction L, t using __eo_list_erase_rec.induct with
  | case1 z => intro hL _ _; exact absurd hL (by simp [IsElemList])
  | case2 s hs => intro _ ht _; exact absurd rfl ht
  | case3 f w y t ht ih =>
      intro hL hts hh
      obtain ⟨hf, hw, hy⟩ := hL
      have hTail := erase_rec_isElemList y t hy hts
      have hTailNS := isElemList_ne_stuck hTail
      rw [erase_rec_cons f w y t hts, eo_eq_val w t hw hts] at hh
      rw [listLookup_cons]
      cases htw : native_teq t w
      · rw [htw, eo_ite_false, mk_apply_of_ne_stuck (by simp) hTailNS,
          listLookup_cons] at hh
        cases hvw : native_veq (__smtx_model_eval M (__eo_to_smt w)) v
        · rw [hvw] at hh
          simp only [native_ite] at hh ⊢
          exact ih hy hts hh
        · simp [native_ite]
      · rw [htw, eo_ite_true] at hh
        cases hvw : native_veq (__smtx_model_eval M (__eo_to_smt w)) v
        · simp only [native_ite]; exact hh
        · simp [native_ite]
  | case4 nil t hns hts hncons =>
      intro hL _ hh
      have hEq : __eo_list_erase_rec nil t = nil := by
        unfold __eo_list_erase_rec; split <;> simp_all
      rw [hEq] at hh; exact hh

theorem erase_present (M : SmtModel) :
    ∀ L t : Term, IsElemList L -> t ≠ Term.Stuck ->
      __eo_list_erase_rec L t ≠ L ->
      listLookup M L (__smtx_model_eval M (__eo_to_smt t)) = SmtValue.Boolean true := by
  intro L t
  induction L, t using __eo_list_erase_rec.induct with
  | case1 z => intro hL _ _; exact absurd hL (by simp [IsElemList])
  | case2 s hs => intro _ ht _; exact absurd rfl ht
  | case3 f w y t ht ih =>
      intro hL hts hne
      obtain ⟨hf, hw, hy⟩ := hL
      have hTail := erase_rec_isElemList y t hy hts
      have hTailNS := isElemList_ne_stuck hTail
      rw [erase_rec_cons f w y t hts, eo_eq_val w t hw hts] at hne
      rw [listLookup_cons]
      cases htw : native_teq t w
      · rw [htw] at hne
        rw [eo_ite_false, mk_apply_of_ne_stuck (by simp) hTailNS] at hne
        have hne' : __eo_list_erase_rec y t ≠ y := by
          intro hEqyt; exact hne (by rw [hEqyt])
        have hyp := ih hy hts hne'
        rw [hyp]
        cases native_veq (__smtx_model_eval M (__eo_to_smt w))
            (__smtx_model_eval M (__eo_to_smt t)) <;> simp [native_ite]
      · have htwe : t = w := of_decide_eq_true htw
        rw [htwe]; simp [native_ite, native_veq]
  | case4 nil t hns hts hncons =>
      intro hL _ hne
      have hEq : __eo_list_erase_rec nil t = nil := by
        unfold __eo_list_erase_rec; split <;> simp_all
      exact absurd hEq hne

/-! #### `__eo_list_minclude_rec` lemmas -/

theorem minclude_rec_cons (y x z : Term) (hy : y ≠ Term.Stuck) :
    __eo_list_minclude_rec y (Term.Apply (Term.Apply Term.__eo_List_cons x) z)
        (Term.Boolean true) =
      __eo_list_minclude_rec (__eo_list_erase_rec y x) z
        (__eo_not (__eo_eq (__eo_list_erase_rec y x) y)) := by
  cases y <;> first | (exact absurd rfl hy) | rfl

theorem minclude_rec_false (y z : Term) (hy : y ≠ Term.Stuck) (hz : z ≠ Term.Stuck) :
    __eo_list_minclude_rec y z (Term.Boolean false) = Term.Boolean false := by
  cases y <;> cases z <;>
    first | (exact absurd rfl hy) | (exact absurd rfl hz) | rfl

theorem listLookup_nil_list (M : SmtModel) (v : SmtValue) :
    listLookup M Term.__eo_List_nil v = SmtValue.Boolean false := rfl

theorem minclude_mem (M : SmtModel) (v : SmtValue) :
    ∀ Y Z g : Term,
      __eo_list_minclude_rec Y Z g = Term.Boolean true ->
      IsElemList Y -> IsElemList Z ->
      listLookup M Z v = SmtValue.Boolean true ->
      listLookup M Y v = SmtValue.Boolean true := by
  intro Y Z g
  induction Y, Z, g using __eo_list_minclude_rec.induct with
  | case1 t x => intro _ hY _ _; exact absurd hY (by simp [IsElemList])
  | case2 y x hy => intro _ _ hZ _; exact absurd hZ (by simp [IsElemList])
  | case3 y z hy hz => intro h _ _ _; rw [minclude_rec_false y z hy hz] at h; cases h
  | case4 y x z hy ih =>
      intro h hY hZ hv
      obtain ⟨hxf, hx, hz⟩ := hZ
      have hEr := erase_rec_isElemList y x hY hx
      have hErNS := isElemList_ne_stuck hEr
      have hyNS := isElemList_ne_stuck hY
      have hzNS := isElemList_ne_stuck hz
      rw [minclude_rec_cons y x z hyNS] at h
      by_cases heq : __eo_list_erase_rec y x = y
      · -- erase removed nothing: guard is false, contradicting h
        exfalso
        rw [heq] at h
        rw [eo_eq_val y y hyNS hyNS] at h
        have hyy : native_teq y y = true := by simp [native_teq]
        rw [hyy] at h
        rw [show __eo_not (Term.Boolean true) = Term.Boolean false from rfl] at h
        rw [minclude_rec_false y z hyNS hzNS] at h
        cases h
      · rw [listLookup_cons] at hv
        cases hvx : native_veq (__smtx_model_eval M (__eo_to_smt x)) v
        · -- v ≠ eval x: membership comes from z
          rw [hvx] at hv
          simp only [native_ite] at hv
          have hzmem := ih h hEr hz hv
          exact erase_mono M v y x hY hx hzmem
        · -- v = eval x: x present in y (erase changed y)
          have hvxe : __smtx_model_eval M (__eo_to_smt x) = v :=
            eq_of_native_veq_true hvx
          have hp := erase_present M y x hY hx heq
          rw [hvxe] at hp
          exact hp
  | case5 y hy => intro _ _ _ hv; rw [listLookup_nil_list] at hv; cases hv
  | case6 t x g hx hg ht hcons hnil =>
      intro h _ _ _
      exfalso
      have hStuck : __eo_list_minclude_rec x t g = Term.Stuck := by
        unfold __eo_list_minclude_rec; split <;> simp_all
      rw [hStuck] at h; cases h

/-! #### `__eo_get_elements_rec` lemmas -/

theorem getelem_cons (f x y : Term) :
    __eo_get_elements_rec (Term.Apply (Term.Apply f x) y) =
      __eo_mk_apply (Term.Apply Term.__eo_List_cons x) (__eo_get_elements_rec y) := rfl

theorem getelem_isElemList :
    ∀ L : Term, IsElemList L -> IsElemList (__eo_get_elements_rec L) := by
  intro L
  induction L using __eo_get_elements_rec.induct with
  | case1 => intro hL; exact absurd hL (by simp [IsElemList])
  | case2 f x y ih =>
      intro hL
      obtain ⟨hf, hx, hy⟩ := hL
      have hTail := ih hy
      have hTailNS := isElemList_ne_stuck hTail
      rw [getelem_cons, mk_apply_of_ne_stuck (by simp) hTailNS]
      exact ⟨by simp, hx, hTail⟩
  | case3 nil hns hncons =>
      intro hL
      have hEq : __eo_get_elements_rec nil = Term.__eo_List_nil := by
        unfold __eo_get_elements_rec; split <;> simp_all
      rw [hEq]; trivial

theorem getelem_mem (M : SmtModel) (v : SmtValue) :
    ∀ L : Term, IsElemList L ->
      listLookup M (__eo_get_elements_rec L) v = listLookup M L v := by
  intro L
  induction L using __eo_get_elements_rec.induct with
  | case1 => intro hL; exact absurd hL (by simp [IsElemList])
  | case2 f x y ih =>
      intro hL
      obtain ⟨hf, hx, hy⟩ := hL
      have hTail := getelem_isElemList y hy
      have hTailNS := isElemList_ne_stuck hTail
      rw [getelem_cons, mk_apply_of_ne_stuck (by simp) hTailNS, listLookup_cons,
        ih hy, listLookup_cons]
  | case3 nil hns hncons =>
      intro hL
      have hEq : __eo_get_elements_rec nil = Term.__eo_List_nil := by
        unfold __eo_get_elements_rec; split <;> simp_all
      have hLnil : listLookup M nil v = SmtValue.Boolean false := by
        unfold listLookup; split <;> simp_all
      rw [hEq, hLnil, listLookup_nil_list]

/-! #### listLookup is Boolean-valued, and the meq membership theorem -/

theorem listLookup_isBool (M : SmtModel) :
    ∀ (L : Term) (v : SmtValue), ∃ b, listLookup M L v = SmtValue.Boolean b := by
  intro L v
  induction L, v using listLookup.induct with
  | case1 a x y v ih =>
      rw [listLookup_cons]
      cases native_veq (__smtx_model_eval M (__eo_to_smt x)) v
      · simpa [native_ite] using ih
      · exact ⟨true, by simp [native_ite]⟩
  | case2 t v hnc =>
      refine ⟨false, ?_⟩
      unfold listLookup; split
      · next a x y => exact absurd rfl (hnc a x y)
      · rfl

/-- If `__eo_list_meq` on two element lists evaluates to `true`, their `listLookup`
membership characteristic values agree everywhere. -/
theorem listLookup_meq
    (M : SmtModel) (X Y : Term) (v : SmtValue)
    (hX : IsElemList X) (hY : IsElemList Y)
    (hMeq : __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons) X Y =
      Term.Boolean true) :
    listLookup M X v = listLookup M Y v := by
  have hgeXel : IsElemList (__eo_get_elements_rec X) := getelem_isElemList X hX
  have hgeYel : IsElemList (__eo_get_elements_rec Y) := getelem_isElemList Y hY
  -- Unfold meq into the conjunction of the two minclude checks.
  have hMeq' : __eo_and
      (__eo_list_minclude_rec
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) X)
          (Term.Boolean true) (__eo_get_elements_rec X))
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) Y)
          (Term.Boolean true) (__eo_get_elements_rec Y))
        (Term.Boolean true))
      (__eo_list_minclude_rec
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) Y)
          (Term.Boolean true) (__eo_get_elements_rec Y))
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) X)
          (Term.Boolean true) (__eo_get_elements_rec X))
        (Term.Boolean true)) = Term.Boolean true := by
    simpa [__eo_list_meq] using hMeq
  obtain ⟨hXY, hYX⟩ := eo_and_eq_true hMeq'
  -- The minclude checks force the `is_list` requirements to hold.
  have hrXne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) X)
        (Term.Boolean true) (__eo_get_elements_rec X) ≠ Term.Stuck := by
    intro hStuck; rw [hStuck] at hXY; simp [__eo_list_minclude_rec] at hXY
  have hrYne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) Y)
        (Term.Boolean true) (__eo_get_elements_rec Y) ≠ Term.Stuck := by
    intro hStuck; rw [hStuck] at hYX; simp [__eo_list_minclude_rec] at hYX
  rw [req_result hrXne, req_result hrYne] at hXY hYX
  -- Membership inclusions both ways.
  have hsubXY : listLookup M (__eo_get_elements_rec Y) v = SmtValue.Boolean true ->
      listLookup M (__eo_get_elements_rec X) v = SmtValue.Boolean true :=
    fun hh => minclude_mem M v (__eo_get_elements_rec X) (__eo_get_elements_rec Y)
      (Term.Boolean true) hXY hgeXel hgeYel hh
  have hsubYX : listLookup M (__eo_get_elements_rec X) v = SmtValue.Boolean true ->
      listLookup M (__eo_get_elements_rec Y) v = SmtValue.Boolean true :=
    fun hh => minclude_mem M v (__eo_get_elements_rec Y) (__eo_get_elements_rec X)
      (Term.Boolean true) hYX hgeYel hgeXel hh
  rw [← getelem_mem M v X hX, ← getelem_mem M v Y hY]
  rcases listLookup_isBool M (__eo_get_elements_rec X) v with hX1 | hX0
  · rcases listLookup_isBool M (__eo_get_elements_rec Y) v with hY1 | hY0
    · rw [hX1, hY1]
    · exact absurd (hsubYX hX1) (by rw [hY0]; decide)
  · rcases listLookup_isBool M (__eo_get_elements_rec Y) v with hY1 | hY0
    · exact absurd (hsubXY hY1) (by rw [hX0]; decide)
    · rw [hX0, hY0]

end SetsEvalOpSupport
