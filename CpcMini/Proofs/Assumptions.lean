module

public import CpcMini.Spec
import all CpcMini.Spec
public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.SmtModel
import all CpcMini.SmtModel

@[expose] public section

open Eo
open Smtm

/-- Predicate asserting that translating an EO term yields a non-`None` SMT term. -/
def eoHasSmtTranslation (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

/-- Predicate asserting that every argument in a checker argument list is translation-safe. -/
def cArgListTranslationOk : CArgList -> Prop
  | CArgList.nil => True
  | CArgList.cons a args => eoHasSmtTranslation a ∧ cArgListTranslationOk args

/-- Predicate asserting that a checker command meets the translation side conditions used by the rule proofs. -/
def cmdTranslationOk : CCmd -> Prop
  | CCmd.assume_push A => eoHasSmtTranslation A
  | CCmd.step _ args _ => cArgListTranslationOk args
  | _ => True

/-- Inductive predicate for valid assumption lists whose entries all have SMT translations. -/
inductive TranslatableAssumptionList : Term -> Prop
  | base : TranslatableAssumptionList (Term.Boolean true)
  | step (A rest : Term) :
      eoHasSmtTranslation A ->
      TranslatableAssumptionList rest ->
      TranslatableAssumptionList (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest)

/-- Inductive predicate asserting that every command in a checker command list satisfies `cmdTranslationOk`. -/
inductive CmdListTranslationOk : CCmdList -> Prop
  | nil : CmdListTranslationOk CCmdList.nil
  | cons (c : CCmd) (cs : CCmdList) :
      cmdTranslationOk c ->
      CmdListTranslationOk cs ->
      CmdListTranslationOk (CCmdList.cons c cs)

/-! ## Deciding the side conditions

The executable has to decide the predicates above at run time: `CpcMini/Api.lean`
runs `decide (cmdTranslationOk c)` and `decide (eoHasSmtTranslation A)` on the
parser's output, and `CpcMini/ApiChecks.lean` turns those into the hypotheses of
`correct___eo_is_refutation`.

The instances are *derived from* the definitions above rather than restating
them, so there is no second copy of the side conditions to keep in sync: a case
added to `cmdTranslationOk` is part of what the executable checks as soon as it
is written here.  Deriving them is why this section is `@[expose]`: a `Decidable`
instance is data, and data may not depend on a definition whose body the module
does not export.
-/

/-- Decides `eoHasSmtTranslation`. -/
instance instDecidableEoHasSmtTranslation (t : Term) : Decidable (eoHasSmtTranslation t) := by
  unfold eoHasSmtTranslation; infer_instance

/-- Decides `cArgListTranslationOk`. -/
instance instDecidableCArgListTranslationOk :
    (args : CArgList) -> Decidable (cArgListTranslationOk args)
  | CArgList.nil => isTrue trivial
  | CArgList.cons a args =>
      have := instDecidableCArgListTranslationOk args
      inferInstanceAs (Decidable (eoHasSmtTranslation a ∧ cArgListTranslationOk args))

/-- Decides `cmdTranslationOk`, one case per case of the definition. -/
instance instDecidableCmdTranslationOk (c : CCmd) : Decidable (cmdTranslationOk c) := by
  unfold cmdTranslationOk; split <;> infer_instance

/-- Decides `CmdListTranslationOk`. -/
instance instDecidableCmdListTranslationOk :
    (cmds : CCmdList) -> Decidable (CmdListTranslationOk cmds)
  | CCmdList.nil => isTrue CmdListTranslationOk.nil
  | CCmdList.cons c cmds =>
      if hc : cmdTranslationOk c then
        match instDecidableCmdListTranslationOk cmds with
        | isTrue hcs => isTrue (CmdListTranslationOk.cons c cmds hc hcs)
        | isFalse hcs => isFalse fun h => hcs (by cases h; assumption)
      else isFalse fun h => hc (by cases h; assumption)
