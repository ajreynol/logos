import Cpc.Lemmas
import Cpc.Proofs.TypePreservation.Common

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

def eo_has_smt_translation (t : Term) : Prop :=
  Not (__smtx_typeof (__eo_to_smt t) = SmtType.None)

def eo_has_bool_type (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Bool

structure RuleResultFacts (M : SmtModel) (P : Term) : Prop where
  true_in_model : eo_interprets M P true
  has_smt_translation : eo_has_smt_translation P

end RuleProofs
