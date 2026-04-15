import CpcMini.SmtModel

open SmtEval
open Smtm

namespace Smtm

/-- Establishes an equality relating `smtx_inhabited_type` and `true_iff`. -/
theorem smtx_inhabited_type_eq_true_iff (T : SmtType) :
    native_inhabited_type T = true ↔ type_inhabited T := by
  classical
  unfold native_inhabited_type type_inhabited
  simp

/-- Establishes an equality relating `smtx_inhabited_type` and `false_iff`. -/
theorem smtx_inhabited_type_eq_false_iff (T : SmtType) :
    native_inhabited_type T = false ↔ ¬ type_inhabited T := by
  classical
  unfold native_inhabited_type type_inhabited
  by_cases h : ∃ v : SmtValue, __smtx_typeof_value v = T
  · simp [h]
  · simp [h]

/-- Predicate asserting that an SMT term does not have type `None`. -/
def term_has_non_none_type (t : SmtTerm) : Prop :=
  __smtx_typeof t ≠ SmtType.None

/-- Predicate asserting that the SMT type of a term is inhabited. -/
def term_has_inhabited_type (t : SmtTerm) : Prop :=
  type_inhabited (__smtx_typeof t)

/-- Predicate asserting that application typing is computed by `__smtx_typeof_apply` for a pair of terms. -/
def generic_apply_type (f x : SmtTerm) : Prop :=
  __smtx_typeof (SmtTerm.Apply f x) =
    __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x)

/-- Predicate asserting that application evaluation is computed by `__smtx_model_eval_apply` for a pair of terms. -/
def generic_apply_eval (f x : SmtTerm) : Prop :=
  ∀ M,
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x)

/-- Predicate asserting that a model returns a correctly typed value, or `NotValue`, at a given symbol and type. -/
def model_typed_at (M : SmtModel) (s : native_String) (T : SmtType) : Prop :=
  (type_inhabited T -> __smtx_typeof_value (__smtx_model_lookup M s T) = T) ∧
  (¬ type_inhabited T -> __smtx_model_lookup M s T = SmtValue.NotValue)

/-- Shows that the SMT type `bool` is inhabited. -/
theorem type_inhabited_bool : type_inhabited SmtType.Bool :=
  ⟨SmtValue.Boolean true, rfl⟩

/-- Shows that the SMT type `int` is inhabited. -/
theorem type_inhabited_int : type_inhabited SmtType.Int :=
  ⟨SmtValue.Numeral 0, rfl⟩

/-- Shows that the SMT type `real` is inhabited. -/
theorem type_inhabited_real : type_inhabited SmtType.Real :=
  ⟨SmtValue.Rational (native_mk_rational 0 1), rfl⟩

/-- Shows that the SMT type `char` is inhabited. -/
theorem type_inhabited_char : type_inhabited SmtType.Char :=
  ⟨SmtValue.Char (Char.ofNat 0), rfl⟩

/-- Shows that the SMT type `reglan` is inhabited. -/
theorem type_inhabited_reglan : type_inhabited SmtType.RegLan :=
  ⟨SmtValue.RegLan native_re_none, rfl⟩

/-- Shows that the SMT type `seq` is inhabited. -/
theorem type_inhabited_seq (T : SmtType) : type_inhabited (SmtType.Seq T) :=
  ⟨SmtValue.Seq (SmtSeq.empty T), rfl⟩

/-- Shows that the SMT type `map` is inhabited. -/
theorem type_inhabited_map {A B : SmtType} (hB : type_inhabited B) :
    type_inhabited (SmtType.Map A B) := by
  rcases hB with ⟨v, hv⟩
  exact ⟨SmtValue.Map (SmtMap.default A v), by simp [__smtx_typeof_value, __smtx_typeof_map_value, hv]⟩

/-- Choice-based model that returns a canonical inhabitant for every inhabited SMT type. -/
noncomputable def default_typed_model : SmtModel := by
  classical
  exact fun k =>
    if h : type_inhabited k.ty then
      some (Classical.choose h)
    else
      none

end Smtm
