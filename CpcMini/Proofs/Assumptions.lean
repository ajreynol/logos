import CpcMini.Spec
import CpcMini.SmtModel

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

/-- Inductive predicate for valid assumption lists whose entries are non-stuck EO Boolean terms. -/
inductive TypedAssumptionList : Term -> Prop
  | base : TypedAssumptionList (Term.Boolean true)
  | step (A rest : Term) :
      A ≠ Term.Stuck ->
      __eo_typeof A = Term.Bool ->
      TypedAssumptionList rest ->
      TypedAssumptionList (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest)

/-- Inductive predicate for valid assumption lists whose entries all admit SMT translations. -/
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
