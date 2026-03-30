import Cpc.Proofs.Translation.Base

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

@[simp] theorem eo_typeof_to_int :
    __eo_typeof Term.to_int =
      Term.Apply (Term.Apply Term.FunType Term.Real) Term.Int := by
  native_decide

@[simp] theorem eo_typeof_is_int :
    __eo_typeof Term.is_int =
      Term.Apply (Term.Apply Term.FunType Term.Real) Term.Bool := by
  native_decide

@[simp] theorem eo_typeof_str_to_lower :
    __eo_typeof Term.str_to_lower =
      Term.Apply
        (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char))
        (Term.Apply Term.Seq Term.Char) := by
  native_decide

@[simp] theorem eo_typeof_str_to_upper :
    __eo_typeof Term.str_to_upper =
      Term.Apply
        (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char))
        (Term.Apply Term.Seq Term.Char) := by
  native_decide

@[simp] theorem eo_typeof_str_to_code :
    __eo_typeof Term.str_to_code =
      Term.Apply
        (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char))
        Term.Int := by
  native_decide

@[simp] theorem eo_typeof_str_from_code :
    __eo_typeof Term.str_from_code =
      Term.Apply
        (Term.Apply Term.FunType Term.Int)
        (Term.Apply Term.Seq Term.Char) := by
  native_decide

@[simp] theorem eo_typeof_str_is_digit :
    __eo_typeof Term.str_is_digit =
      Term.Apply
        (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char))
        Term.Bool := by
  native_decide

@[simp] theorem eo_typeof_str_to_int :
    __eo_typeof Term.str_to_int =
      Term.Apply
        (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char))
        Term.Int := by
  native_decide

@[simp] theorem eo_typeof_str_from_int :
    __eo_typeof Term.str_from_int =
      Term.Apply
        (Term.Apply Term.FunType Term.Int)
        (Term.Apply Term.Seq Term.Char) := by
  native_decide

@[simp] theorem eo_typeof_str_to_re :
    __eo_typeof Term.str_to_re =
      Term.Apply
        (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char))
        Term.RegLan := by
  native_decide

@[simp] theorem eo_typeof_re_mult :
    __eo_typeof Term.re_mult =
      Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan := by
  native_decide

@[simp] theorem eo_typeof_re_plus :
    __eo_typeof Term.re_plus =
      Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan := by
  native_decide

@[simp] theorem eo_typeof_re_opt :
    __eo_typeof Term.re_opt =
      Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan := by
  native_decide

@[simp] theorem eo_typeof_re_comp :
    __eo_typeof Term.re_comp =
      Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan := by
  native_decide

end TranslationProofs
