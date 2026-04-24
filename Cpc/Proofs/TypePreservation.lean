import Cpc.Proofs.TypePreservation.Support

open SmtEval
open Smtm

/-!
Lightweight public surface for the type-preservation facts used by the rule
proofs.

To reconnect the final type-preservation proofs:
1. Uncomment `import Cpc.Proofs.TypePreservation.Full`.
2. Comment out or delete the stub declarations below.

The full module exposes the same theorem names in the same namespace, so the
rest of the proof development does not need to change.
-/

-- import Cpc.Proofs.TypePreservation.Full

namespace Smtm

theorem typeof_eq_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.eq t1 t2) =
      __smtx_typeof_eq (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_133]

theorem eq_term_typeof_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.eq t1 t2)) :
    __smtx_typeof (SmtTerm.eq t1 t2) = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  rw [typeof_eq_eq] at ht
  rw [typeof_eq_eq]
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, h1, h2] at ht ⊢
  all_goals
    first | exact ht

theorem typeof_not_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool SmtType.None := by
  rw [__smtx_typeof.eq_6]

theorem typeof_or_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.or t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_7]

theorem typeof_and_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.and t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_8]

theorem typeof_imp_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.imp t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_9]

theorem choice_term_guard_type_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body 0)) :
    __smtx_typeof (SmtTerm.choice_nth s T body 0) = __smtx_typeof_guard_wf T T := by
  unfold term_has_non_none_type at ht
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
        cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [__smtx_typeof_choice_nth, hEqFalse, native_ite]
  unfold __smtx_typeof
  simp [__smtx_typeof_choice_nth, hEq, native_ite]

theorem choice_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body 0)) :
    __smtx_typeof (SmtTerm.choice_nth s T body 0) = T := by
  have hGuard : __smtx_typeof (SmtTerm.choice_nth s T body 0) = __smtx_typeof_guard_wf T T :=
    choice_term_guard_type_of_non_none ht
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    unfold term_has_non_none_type at ht
    apply ht
    rw [hGuard, hNone]
  exact hGuard.trans (smtx_typeof_guard_wf_of_non_none T T hGuardNN)

theorem bool_binop_args_bool_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    __smtx_typeof t1 = SmtType.Bool ∧ __smtx_typeof t2 = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, native_ite, native_Teq, h1, h2] at ht
  simp

theorem typeof_str_len_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_len t) =
      __smtx_typeof_seq_op_1_ret (__smtx_typeof t) SmtType.Int := by
  rw [__smtx_typeof.eq_78]

axiom seq_nth_term_inhabited_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2)) :
    type_inhabited (__smtx_typeof (SmtTerm.seq_nth t1 t2))

axiom dt_sel_term_inhabited_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))

axiom supported_seq_unit_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_unit t))
    (hs : supported_preservation_term t) :
    supported_preservation_term (SmtTerm.seq_unit t)

axiom supported_set_singleton_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.set_singleton t))
    (hs : supported_preservation_term t) :
    supported_preservation_term (SmtTerm.set_singleton t)

axiom supported_seq_nth_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2))
    (hs1 : supported_preservation_term t1)
    (hs2 : supported_preservation_term t2) :
    supported_preservation_term (SmtTerm.seq_nth t1 t2)

axiom supported_dt_sel_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
    (hsx : supported_preservation_term x) :
    supported_preservation_term (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)

axiom supported_apply_of_non_none
    {f x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply f x))
    (hsf : supported_preservation_term f)
    (hsx : supported_preservation_term x) :
    supported_preservation_term (SmtTerm.Apply f x)

axiom supported_ite_of_non_none
    {c t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.ite c t1 t2))
    (hsc : supported_preservation_term c)
    (hs1 : supported_preservation_term t1)
    (hs2 : supported_preservation_term t2) :
    supported_preservation_term (SmtTerm.ite c t1 t2)

axiom supported_preservation_term_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t -> supported_preservation_term t

axiom type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t

axiom smt_model_eval_preserves_type_of_non_none
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
    term_has_non_none_type t ->
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t

axiom smt_model_eval_preserves_type_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (T : SmtType)
    (hTy : __smtx_typeof t = T)
    (hNonNone : T ≠ SmtType.None)
    (hs : supported_preservation_term t) :
    __smtx_typeof_value (__smtx_model_eval M t) = T

axiom smt_model_eval_bool_is_boolean_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool)
    (hs : supported_preservation_term t) :
    ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b

axiom smt_model_eval_preserves_type
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (T : SmtType) :
    __smtx_typeof t = T ->
    T ≠ SmtType.None ->
    type_inhabited T ->
    __smtx_typeof_value (__smtx_model_eval M t) = T

axiom smt_model_eval_bool_is_boolean
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b

axiom total_typed_model_nonvacuous :
    ∃ M : SmtModel, model_total_typed M

end Smtm
