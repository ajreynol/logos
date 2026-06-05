import Cpc.Spec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

def native_eo_to_smt_uop_indices_safe : Term -> native_Bool
  | Term.Apply f x =>
    native_and (native_eo_to_smt_uop_indices_safe f) (native_eo_to_smt_uop_indices_safe x)
  | Term.UOp1 _ x =>
    native_and (native_eo_to_smt_closed x) (native_eo_to_smt_uop_indices_safe x)
  | Term.UOp2 _ x y =>
    native_and
      (native_and (native_eo_to_smt_closed x) (native_eo_to_smt_closed y))
      (native_and (native_eo_to_smt_uop_indices_safe x) (native_eo_to_smt_uop_indices_safe y))
  | Term.UOp3 _ x y z =>
    native_and
      (native_and (native_and (native_eo_to_smt_closed x) (native_eo_to_smt_closed y)) (native_eo_to_smt_closed z))
      (native_and
        (native_and (native_eo_to_smt_uop_indices_safe x) (native_eo_to_smt_uop_indices_safe y))
        (native_eo_to_smt_uop_indices_safe z))
  | _ => true

def NativeEoToSmtUOpIndicesSafe (x : Term) : Prop :=
  native_eo_to_smt_uop_indices_safe x = true

/-
Central theorem to prove here:

  theorem eo_to_smt_well_typed_implies_uop_indices_safe
      (t : Term) :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      NativeEoToSmtUOpIndicesSafe t

`NativeEoToSmtUOpIndicesSafe` says every indexed EO operator occurrence has
standalone-closed immediate indices. The guarded branches in `__eo_to_smt`
discharge the opaque term-index cases; the numeric-index branches are intended
to be discharged from the SMT typing rules that require their indices to
translate to `SmtTerm.Numeral`.
-/
