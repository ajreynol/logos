import CpcMini.Logos

open Eo

private def openBool : Term :=
  Term.Var (Term.String []) Term.Bool

private def openPushAccepted : Bool :=
  match __eo_invoke_cmd CState.nil (CCmd.assume_push openBool) with
  | CState.cons (CStateObj.assume_push _) CState.nil => true
  | _ => false

-- Mini CPC follows the same local-assumption policy as the full checker.
#guard __eo_is_closed openBool == Term.Boolean false
#guard __eo_is_bool_type openBool == Term.Boolean true
#guard openPushAccepted
