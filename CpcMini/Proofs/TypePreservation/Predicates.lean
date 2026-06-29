import CpcMini.SmtModel

open SmtEval
open Smtm

/-- `native_Teq` is reflexive; lets `simp` discharge the reflexive residual left
when `native_inhabited_type` is unfolded on a concrete type. -/
@[simp] theorem native_Teq_self (x : SmtType) : native_Teq x x = true := by
  simp [native_Teq]

namespace Smtm

/-- Semantic inhabitation of an SMT type. -/
def type_inhabited (T : SmtType) : Prop :=
  ∃ v : SmtValue, __smtx_typeof_value v = T

/-- Proof-facing canonicality predicate for SMT values. -/
def __smtx_value_canonical (v : SmtValue) : Prop :=
  __smtx_value_canonical_bool v = true

end Smtm
