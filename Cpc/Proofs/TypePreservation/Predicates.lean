import Cpc.SmtModel

open SmtEval
open Smtm

namespace Smtm

/-- Semantic inhabitation of an SMT type. -/
def type_inhabited (T : SmtType) : Prop :=
  ∃ v : SmtValue, __smtx_typeof_value v = T

/-- Proof-facing canonicality predicate for SMT values. -/
def __smtx_value_canonical (v : SmtValue) : Prop :=
  __smtx_value_canonical_bool v = true

end Smtm
