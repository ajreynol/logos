import Cpc.SmtModel

open Smtm

namespace Smtm

def term_has_non_none_type (t : SmtTerm) : Prop :=
  __smtx_typeof t ≠ SmtType.None

def model_total_typed (M : SmtModel) : Prop :=
  ∀ s T, __smtx_typeof_value (__smtx_model_lookup M s T) = T

def model_typed_at (M : SmtModel) (s : smt_lit_String) (T : SmtType) : Prop :=
  __smtx_typeof_value (__smtx_model_lookup M s T) = T

end Smtm
