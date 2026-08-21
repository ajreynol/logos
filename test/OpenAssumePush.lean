import Cpc.Logos

open Eo

private def openBool : Term :=
  Term.Var (Term.String []) Term.Bool

-- A free Boolean variable is open but still has the required assumption type.
#guard __eo_is_closed openBool == Term.Boolean false
#guard __eo_is_bool_type openBool == Term.Boolean true

private def openPushAccepted : Bool :=
  match __eo_invoke_cmd CState.nil (CCmd.assume_push openBool) with
  | CState.cons (CStateObj.assume_push _) CState.nil => true
  | _ => false

-- `assume-push` now accepts an open Boolean formula.
#guard openPushAccepted

-- Ordinary pointwise rules remain available in an open local context.
#guard __eo_step_context_guard
    (CState.cons (CStateObj.assume_push openBool) CState.nil) CRule.refl ==
  Term.Boolean true

private def openReflAccepted : Bool :=
  let s := CState.cons (CStateObj.assume_push openBool) CState.nil
  let c := CCmd.step CRule.refl (CArgList.cons openBool CArgList.nil) CIndexList.nil
  match __eo_invoke_cmd s c with
  | CState.cons (CStateObj.proven _) (CState.cons (CStateObj.assume_push _) CState.nil) =>
      true
  | _ => false

#guard openReflAccepted

-- Rules that require variable-model stability are conservatively blocked.
#guard __eo_step_context_guard
    (CState.cons (CStateObj.assume_push openBool) CState.nil) CRule.cong ==
  Term.Boolean false

-- A closed local context continues to admit guarded rules.
#guard __eo_step_context_guard
    (CState.cons (CStateObj.assume_push (Term.Boolean true)) CState.nil) CRule.cong ==
  Term.Boolean true
