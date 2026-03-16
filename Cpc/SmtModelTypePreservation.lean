import Cpc.SmtModel

namespace Smtm

/--
A model is well-typed when every lookup returns a value of the requested type.
This is the assumption needed to state preservation for `__smtx_model_eval`.
-/
def smtx_model_well_typed (M : SmtModel) : Prop :=
  ∀ n T, __smtx_typeof_value (__smtx_model_lookup M n T) = T

/--
Minimal well-formedness for terms used by the preservation statement.
The only non-syntactic case is `Const`, whose annotation must match the value.
-/
def smtx_term_well_formed : SmtTerm -> Prop
  | SmtTerm.Apply f x => smtx_term_well_formed f ∧ smtx_term_well_formed x
  | SmtTerm.Const v T => __smtx_typeof_value v = T
  | _ => True

theorem __smtx_model_eval_type_preservation
    {M : SmtModel} {t : SmtTerm}
    (hM : smtx_model_well_typed M)
    (hwf : smtx_term_well_formed t)
    (ht : __smtx_typeof t ≠ SmtType.None) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  sorry

end Smtm
