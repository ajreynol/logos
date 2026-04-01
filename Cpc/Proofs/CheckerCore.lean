import Cpc.Spec
import Cpc.Proofs.Rules.Support

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

def checkerTruthInvariant (_M : SmtModel) (_s : CState) : Prop := True

def checkerTypeInvariant (_s : CState) : Prop := True

def checkerTranslationInvariant (_s : CState) : Prop := True

structure CmdStepFacts (M : SmtModel) (s : CState) (P : Term) : Prop where
  placeholder : True

structure CmdStepPopFacts
    (root tail : CState) (A P : Term) : Prop where
  placeholder : True
