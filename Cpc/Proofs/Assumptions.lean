import Cpc.Spec
import Cpc.SmtModel

open Eo
open Smtm

/-- Predicate asserting that translating an EO term yields a non-`None` SMT term. -/
def eoHasSmtTranslation (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

/-- Predicate asserting that every element of an EO list has an SMT translation. -/
def EoListAllHaveSmtTranslation : Term -> Prop
  | Term.__eo_List_nil => True
  | Term.Apply (Term.Apply Term.__eo_List_cons t) ts =>
      eoHasSmtTranslation t ∧ EoListAllHaveSmtTranslation ts
  | _ => False

/-- Classifies checker rule arguments by the translation side condition they require. -/
inductive ArgTranslationKind where
  | term
  | list
  | type

/-- Interprets a command-argument mask entry. -/
def argTranslationOkMasked : ArgTranslationKind -> Term -> Prop
  | ArgTranslationKind.term, t => eoHasSmtTranslation t
  | ArgTranslationKind.list, t => EoListAllHaveSmtTranslation t
  | ArgTranslationKind.type, _ => True

/-- Predicate asserting that every argument in a checker argument list is translation-safe. -/
def cArgListTranslationOk : CArgList -> Prop
  | CArgList.nil => True
  | CArgList.cons a args => eoHasSmtTranslation a ∧ cArgListTranslationOk args

/-- Predicate asserting that a checker argument list matches a translation mask. -/
def cArgListTranslationOkMask : List ArgTranslationKind -> CArgList -> Prop
  | [], CArgList.nil => True
  | kind :: mask, CArgList.cons a args =>
      argTranslationOkMasked kind a ∧ cArgListTranslationOkMask mask args
  | _, _ => False

/-- Predicate asserting that a checker command meets the translation side conditions used by the rule proofs. -/
def cmdTranslationOk : CCmd -> Prop
  | CCmd.assume_push A => eoHasSmtTranslation A
  | CCmd.step CRule.chain_resolution args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.list, ArgTranslationKind.list] args
  | CCmd.step CRule.chain_m_resolution args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.list,
        ArgTranslationKind.list] args
  | CCmd.step CRule.instantiate args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.list] args
  | CCmd.step CRule.alpha_equiv args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.list,
        ArgTranslationKind.list] args
  | CCmd.step CRule.exists_string_length args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.type, ArgTranslationKind.term,
        ArgTranslationKind.term] args
  | CCmd.step CRule.sets_eq_singleton_emp args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_member_emp args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_inter_emp1 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_inter_emp2 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_minus_emp1 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_minus_emp2 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_union_emp1 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_union_emp2 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_minus_self args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.sets_is_empty_elim args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_empty_range args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_empty_start args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_empty_start_neg args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_substr_start_geq_len args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.str_concat_unify_base args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_concat_unify_base_rev args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_contains_char args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.str_len_eq_zero_concat_rec args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_len_eq_zero_base args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_indexof_self args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_char_start_eq_len args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step _ args _ => cArgListTranslationOk args
  | _ => True

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
