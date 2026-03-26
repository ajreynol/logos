import Cpc.SmtModel

open Smtm

namespace Smtm

def type_inhabited (T : SmtType) : Prop :=
  ∃ v : SmtValue, __smtx_typeof_value v = T

def term_has_non_none_type (t : SmtTerm) : Prop :=
  __smtx_typeof t ≠ SmtType.None

def term_has_inhabited_type (t : SmtTerm) : Prop :=
  type_inhabited (__smtx_typeof t)

def model_total_typed (M : SmtModel) : Prop :=
  ∀ s T, type_inhabited T -> __smtx_typeof_value (__smtx_model_lookup M s T) = T

def model_typed_at (M : SmtModel) (s : smt_lit_String) (T : SmtType) : Prop :=
  type_inhabited T -> __smtx_typeof_value (__smtx_model_lookup M s T) = T

theorem type_inhabited_bool : type_inhabited SmtType.Bool :=
  ⟨SmtValue.Boolean true, rfl⟩

theorem type_inhabited_int : type_inhabited SmtType.Int :=
  ⟨SmtValue.Numeral 0, rfl⟩

theorem type_inhabited_real : type_inhabited SmtType.Real :=
  ⟨SmtValue.Rational (smt_lit_mk_rational 0 1), rfl⟩

theorem type_inhabited_seq (T : SmtType) : type_inhabited (SmtType.Seq T) :=
  ⟨SmtValue.Seq (SmtSeq.empty T), rfl⟩

theorem type_inhabited_map {A B : SmtType} (hB : type_inhabited B) :
    type_inhabited (SmtType.Map A B) := by
  rcases hB with ⟨v, hv⟩
  exact ⟨SmtValue.Map (SmtMap.default A v), by simp [__smtx_typeof_value, __smtx_typeof_map_value, hv]⟩

noncomputable def default_typed_model : SmtModel := by
  classical
  exact fun k =>
    if h : type_inhabited k.ty then
      some (Classical.choose h)
    else
      none

end Smtm
