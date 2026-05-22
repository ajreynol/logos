import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CoreSupport
import Cpc.Proofs.Canonical

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace SetsMemberSupport

theorem eo_typeof_or_ne_stuck
    {A B : Term}
    (h : __eo_typeof_or A B ≠ Term.Stuck) :
    A = Term.Bool ∧ B = Term.Bool := by
  cases A <;> cases B <;> simp [__eo_typeof_or] at h ⊢

theorem eo_typeof_eq_eq_bool_info
    {A B : Term}
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B ∧ A ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  by_cases hB : B = Term.Stuck
  · subst B
    cases A <;> simp [__eo_typeof_eq] at h
  have hReq :
      __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool =
        Term.Bool := by
    simpa [__eo_typeof_eq, hA, hB] using h
  have hReqNS :
      __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool ≠
        Term.Stuck := by
    rw [hReq]
    decide
  have hBA : B = A :=
    RuleProofs.eq_of_requires_eq_true_not_stuck A B Term.Bool hReqNS
  exact ⟨hBA.symm, hA⟩

theorem eo_typeof_set_member_eq_bool_info
    {A B : Term}
    (h : __eo_typeof_set_member A B = Term.Bool) :
    ∃ T : Term,
      A = T ∧
        B = Term.Apply (Term.UOp UserOp.Set) T ∧
          T ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_set_member] at h
  cases B <;> try simp [__eo_typeof_set_member] at h
  next f U =>
    cases f <;> try simp at h
    next op =>
      cases op <;> try simp at h
      have hReq :
          __eo_requires (__eo_eq A U) (Term.Boolean true) Term.Bool =
            Term.Bool := by
        simpa [__eo_typeof_set_member, hA] using h
      have hReqNS :
          __eo_requires (__eo_eq A U) (Term.Boolean true) Term.Bool ≠
            Term.Stuck := by
        rw [hReq]
        decide
      have hUA : U = A :=
        RuleProofs.eq_of_requires_eq_true_not_stuck A U Term.Bool hReqNS
      subst U
      exact ⟨A, rfl, rfl, hA⟩

theorem map_cons_head_key_type
    {k v : SmtValue} {m : SmtMap} {A B : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) = SmtType.Map A B) :
    __smtx_typeof_value k = A := by
  by_cases hEq :
      native_Teq (SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v))
        (__smtx_typeof_map_value m)
  · have hTail : __smtx_typeof_map_value m = SmtType.Map A B := by
      simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
    have hHead :
        SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
          SmtType.Map A B := by
      have hEq' :
          SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
            __smtx_typeof_map_value m := by
        simpa [native_Teq] using hEq
      exact hEq'.trans hTail
    cases hHead
    rfl
  · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy

theorem map_cons_head_value_type
    {k v : SmtValue} {m : SmtMap} {A B : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) = SmtType.Map A B) :
    __smtx_typeof_value v = B := by
  by_cases hEq :
      native_Teq (SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v))
        (__smtx_typeof_map_value m)
  · have hTail : __smtx_typeof_map_value m = SmtType.Map A B := by
      simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
    have hHead :
        SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
          SmtType.Map A B := by
      have hEq' :
          SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
            __smtx_typeof_map_value m := by
        simpa [native_Teq] using hEq
      exact hEq'.trans hTail
    cases hHead
    rfl
  · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy

theorem map_cons_tail_type
    {k v : SmtValue} {m : SmtMap} {A B : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) = SmtType.Map A B) :
    __smtx_typeof_map_value m = SmtType.Map A B := by
  by_cases hEq :
      native_Teq (SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v))
        (__smtx_typeof_map_value m)
  · simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
  · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy

theorem map_cons_tail_canonical
    {k v : SmtValue} {m : SmtMap}
    (hCan : __smtx_map_canonical (SmtMap.cons k v m) = true) :
    __smtx_map_canonical m = true := by
  have hParts := hCan
  simp [__smtx_map_canonical, SmtEval.native_and] at hParts
  exact hParts.1.1.2

theorem map_cons_head_key_canonical
    {k v : SmtValue} {m : SmtMap}
    (hCan : __smtx_map_canonical (SmtMap.cons k v m) = true) :
    __smtx_value_canonical k := by
  have hParts := hCan
  simp [__smtx_map_canonical, SmtEval.native_and] at hParts
  exact hParts.1.1.1.1

theorem map_cons_tail_ordered
    {k v : SmtValue} {m : SmtMap}
    (hCan : __smtx_map_canonical (SmtMap.cons k v m) = true) :
    __smtx_map_entries_ordered_after k m = true := by
  have hParts := hCan
  simp [__smtx_map_canonical, SmtEval.native_and] at hParts
  exact hParts.1.2

theorem set_map_cons_entry_true
    {k v : SmtValue} {m : SmtMap} {A : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) =
      SmtType.Map A SmtType.Bool)
    (hCan : __smtx_map_canonical (SmtMap.cons k v m) = true)
    (hDef : __smtx_msm_get_default (SmtMap.cons k v m) = SmtValue.Boolean false) :
    v = SmtValue.Boolean true := by
  have hvTy : __smtx_typeof_value v = SmtType.Bool :=
    map_cons_head_value_type hTy
  rcases bool_value_canonical hvTy with ⟨b, rfl⟩
  cases b
  · have hNeDefault : native_veq (SmtValue.Boolean false)
        (__smtx_msm_get_default m) = false := by
      have hParts := hCan
      simp [__smtx_map_canonical, SmtEval.native_and, SmtEval.native_not] at hParts
      exact hParts.2
    have hTailDef : __smtx_msm_get_default m = SmtValue.Boolean false := by
      simpa [__smtx_msm_get_default] using hDef
    simp [hTailDef, native_veq] at hNeDefault
  · rfl

theorem mss_op_lookup_acc
    (isInter : native_Bool) :
    ∀ {m1 m2 acc : SmtMap} {A : SmtType} {i : SmtValue},
      __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool ->
      __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool ->
      __smtx_typeof_map_value acc = SmtType.Map A SmtType.Bool ->
      __smtx_map_canonical m1 = true ->
      __smtx_map_canonical acc = true ->
      __smtx_msm_get_default m1 = SmtValue.Boolean false ->
      __smtx_msm_lookup (__smtx_mss_op_internal isInter m1 m2 acc) i =
        native_ite
          (native_and
            (native_veq (__smtx_msm_lookup m1 i) (SmtValue.Boolean true))
            (native_iff
              (native_veq (__smtx_msm_lookup m2 i) (SmtValue.Boolean true))
              isInter))
          (SmtValue.Boolean true)
          (__smtx_msm_lookup acc i)
  | SmtMap.default T efalse, m2, acc, A, i, hm1Ty, hm2Ty, haccTy, hm1Can,
      haccCan, hm1Def => by
      have hefalse : efalse = SmtValue.Boolean false := by
        simpa [__smtx_msm_get_default] using hm1Def
      simp [__smtx_mss_op_internal, __smtx_msm_lookup, hefalse, native_veq,
        SmtEval.native_and, native_ite, native_iff]
  | SmtMap.cons e etrue m1, m2, acc, A, i, hm1Ty, hm2Ty, haccTy, hm1Can,
      haccCan, hm1Def => by
      have hmTailTy : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool :=
        map_cons_tail_type hm1Ty
      have heTy : __smtx_typeof_value e = A :=
        map_cons_head_key_type hm1Ty
      have hmTailCan : __smtx_map_canonical m1 = true :=
        map_cons_tail_canonical hm1Can
      have heCan : __smtx_value_canonical e :=
        map_cons_head_key_canonical hm1Can
      have hOrdTail : __smtx_map_entries_ordered_after e m1 = true :=
        map_cons_tail_ordered hm1Can
      have hmTailDef : __smtx_msm_get_default m1 = SmtValue.Boolean false := by
        simpa [__smtx_msm_get_default] using hm1Def
      have hetrue : etrue = SmtValue.Boolean true :=
        set_map_cons_entry_true hm1Ty hm1Can hm1Def
      subst etrue
      by_cases hCond :
          native_veq (__smtx_msm_lookup m2 e) (SmtValue.Boolean true) = isInter
      · let acc' :=
          __smtx_msm_update_aux (__smtx_msm_get_default acc) acc e
            (SmtValue.Boolean true)
        have hCondDec :
            decide (__smtx_msm_lookup m2 e = SmtValue.Boolean true) = isInter := by
          simpa [native_veq] using hCond
        have hacc'Ty : __smtx_typeof_map_value acc' = SmtType.Map A SmtType.Bool := by
          dsimp [acc']
          exact map_canon_insert_typed haccTy heTy rfl
        have hacc'Can : __smtx_map_canonical acc' = true := by
          dsimp [acc']
          exact map_update_aux_canonical haccCan heCan (value_canonical_boolean true)
        have hRec := mss_op_lookup_acc isInter (m1 := m1) (m2 := m2) (acc := acc')
          (A := A) (i := i) hmTailTy hm2Ty hacc'Ty hmTailCan hacc'Can
          hmTailDef
        cases hei : native_veq e i
        · have hAccLookup :
              __smtx_msm_lookup acc' i = __smtx_msm_lookup acc i := by
            dsimp [acc']
            exact map_lookup_update_aux_other haccCan hei
          simpa [__smtx_mss_op_internal, hCond, hCondDec, __smtx_msm_lookup,
            native_ite, native_iff, hei, hAccLookup] using hRec
        · have heiEq : e = i := eq_of_native_veq_true hei
          subst i
          have hTailLookup :
              __smtx_msm_lookup m1 e = SmtValue.Boolean false := by
            calc
              __smtx_msm_lookup m1 e = __smtx_msm_get_default m1 :=
                map_lookup_eq_default_of_entries_ordered_after hmTailCan hOrdTail
              _ = SmtValue.Boolean false := hmTailDef
          have hAccLookup :
              __smtx_msm_lookup acc' e = SmtValue.Boolean true := by
            dsimp [acc']
            exact map_lookup_update_aux_same haccCan
          simpa [__smtx_mss_op_internal, hCond, hCondDec, __smtx_msm_lookup,
            native_ite, native_iff, native_veq, hTailLookup, hAccLookup,
            SmtEval.native_and] using hRec
      · have hRec := mss_op_lookup_acc isInter (m1 := m1) (m2 := m2) (acc := acc)
          (A := A) (i := i) hmTailTy hm2Ty haccTy hmTailCan haccCan hmTailDef
        have hCondDec :
            ¬ decide (__smtx_msm_lookup m2 e = SmtValue.Boolean true) = isInter := by
          intro h
          exact hCond (by simpa [native_veq] using h)
        cases hei : native_veq e i
        · simpa [__smtx_mss_op_internal, hCond, hCondDec, __smtx_msm_lookup,
            native_ite, native_iff, hei] using hRec
        · have heiEq : e = i := eq_of_native_veq_true hei
          subst i
          have hTailLookup :
              __smtx_msm_lookup m1 e = SmtValue.Boolean false := by
            calc
              __smtx_msm_lookup m1 e = __smtx_msm_get_default m1 :=
                map_lookup_eq_default_of_entries_ordered_after hmTailCan hOrdTail
              _ = SmtValue.Boolean false := hmTailDef
          simpa [__smtx_mss_op_internal, hCond, hCondDec, __smtx_msm_lookup,
            native_ite, native_iff, native_veq, hTailLookup,
            SmtEval.native_and] using hRec

end SetsMemberSupport
