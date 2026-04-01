import Cpc.Lemmas
import Cpc.Proofs.Translation
import Cpc.Proofs.TypePreservation
import Cpc.Proofs.TypePreservation.Helpers

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

theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = Term.Bool ->
  __smtx_typeof s = SmtType.Bool := by
  intro hs hS hTy
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    t Term.Bool s hs hS hTy

theorem eo_typeof_bool_implies_has_bool_type
    (t : Term) :
  eo_has_smt_translation t ->
  __eo_typeof t = Term.Bool ->
  eo_has_bool_type t := by
  intro hTrans hTy
  exact eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    t (__eo_to_smt t) rfl hTrans hTy

theorem eo_has_smt_translation_of_has_bool_type (t : Term) :
  eo_has_bool_type t ->
  eo_has_smt_translation t := by
  intro hTy
  intro hNone
  rw [eo_has_bool_type] at hTy
  rw [hNone] at hTy
  cases hTy

end RuleProofs
