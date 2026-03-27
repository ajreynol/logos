import Cpc.SmtModel

open Smtm

namespace Smtm

def type_inhabited (T : SmtType) : Prop :=
  ∃ v : SmtValue, __smtx_typeof_value v = T

theorem smtx_inhabited_type_eq_true_iff (T : SmtType) :
    smt_lit_inhabited_type T = true ↔ type_inhabited T := by
  classical
  unfold smt_lit_inhabited_type type_inhabited
  simp

theorem smtx_inhabited_type_eq_false_iff (T : SmtType) :
    smt_lit_inhabited_type T = false ↔ ¬ type_inhabited T := by
  classical
  unfold smt_lit_inhabited_type type_inhabited
  by_cases h : ∃ v : SmtValue, __smtx_typeof_value v = T
  · simp [h]
  · simp [h]

def term_has_non_none_type (t : SmtTerm) : Prop :=
  __smtx_typeof t ≠ SmtType.None

def term_has_inhabited_type (t : SmtTerm) : Prop :=
  type_inhabited (__smtx_typeof t)

def generic_apply_type (f x : SmtTerm) : Prop :=
  __smtx_typeof (SmtTerm.Apply f x) =
    __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x)

def generic_apply_eval (f x : SmtTerm) : Prop :=
  ∀ M,
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x)

def model_total_typed (M : SmtModel) : Prop :=
  (∀ s T, type_inhabited T -> __smtx_typeof_value (__smtx_model_lookup M s T) = T) ∧
  (∀ s T, ¬ type_inhabited T -> __smtx_model_lookup M s T = SmtValue.NotValue)

def model_typed_at (M : SmtModel) (s : smt_lit_String) (T : SmtType) : Prop :=
  (type_inhabited T -> __smtx_typeof_value (__smtx_model_lookup M s T) = T) ∧
  (¬ type_inhabited T -> __smtx_model_lookup M s T = SmtValue.NotValue)

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
