module

public import Logos.Parser
import all Logos.Parser
public import CpcMini.Logos
import all CpcMini.Logos

public section

namespace Eo

open SmtEval

private def parserNil (op : Term) : Option Term → Term
  | some seed => __eo_nil op (__eo_typeof seed)
  | none => __eo_nil op Term.Type

private def parseBinaryDigits : List Char → Option Nat
  | [] => some 0
  | digit :: rest => do
    let bit ← if digit == '0' then some 0 else if digit == '1' then some 1 else none
    return bit * (2 ^ rest.length) + (← parseBinaryDigits rest)

private def parserLiteral (value : String) : Option Term :=
  if value.startsWith "\"" && value.endsWith "\"" then
    some (.String (native_string_lit (((value.drop 1).toString.dropEnd 1).toString)))
  else if value.startsWith "#b" then
    let digits := (value.drop 2).toString.toList
    (parseBinaryDigits digits).map fun n => .Binary digits.length n
  else
    match value.splitOn "/" with
    | [num, den] => do
      let num ← num.toInt?
      let den ← den.toInt?
      if den == 0 then none else some (.Rational (native_mk_rational num den))
    | _ => value.toInt?.map .Numeral

private def parserOps : List (Logos.Parser.OpDecl Term) := [
  { name := "Type", arity := .exact 0, build := fun | [] => some .Type | _ => none },
  { name := "Bool", arity := .exact 0, build := fun | [] => some .Bool | _ => none },
  { name := "false", arity := .exact 0,
    build := fun | [] => some (.Boolean false) | _ => none },
  { name := "true", arity := .exact 0,
    build := fun | [] => some (.Boolean true) | _ => none },
  { name := "->", arity := .rightAssoc,
    build := fun | [] => some .FunType | _ => none },
  { name := "@list", arity := .rightAssocNil (fun _ => .__eo_List_nil),
    build := fun | [] => some .__eo_List_cons | _ => none },
  { name := "Int"
    indexArity := 0
    arity := .exact 0
    build := fun
      | [] => some (Term.UOp UserOp.Int)
      | _ => none },
  { name := "Real"
    indexArity := 0
    arity := .exact 0
    build := fun
      | [] => some (Term.UOp UserOp.Real)
      | _ => none },
  { name := "BitVec"
    indexArity := 0
    arity := .exact 1
    build := fun
      | [] => some (Term.UOp UserOp.BitVec)
      | _ => none },
  { name := "Char"
    indexArity := 0
    arity := .exact 0
    build := fun
      | [] => some (Term.UOp UserOp.Char)
      | _ => none },
  { name := "Seq"
    indexArity := 0
    arity := .exact 1
    build := fun
      | [] => some (Term.UOp UserOp.Seq)
      | _ => none },
  { name := "not"
    indexArity := 0
    arity := .exact 1
    build := fun
      | [] => some (Term.UOp UserOp.not)
      | _ => none },
  { name := "or"
    indexArity := 0
    arity := .rightAssocNil (parserNil (Term.UOp UserOp.or))
    build := fun
      | [] => some (Term.UOp UserOp.or)
      | _ => none },
  { name := "and"
    indexArity := 0
    arity := .rightAssocNil (parserNil (Term.UOp UserOp.and))
    build := fun
      | [] => some (Term.UOp UserOp.and)
      | _ => none },
  { name := "=>"
    indexArity := 0
    arity := .rightAssoc
    build := fun
      | [] => some (Term.UOp UserOp.imp)
      | _ => none },
  { name := "="
    indexArity := 0
    arity := .chainable (fun ts => Logos.Parser.rightAssocNil Term.Apply (Term.UOp UserOp.and) (parserNil (Term.UOp UserOp.and)) ts)
    build := fun
      | [] => some (Term.UOp UserOp.eq)
      | _ => none },
]

/-- The proof rules of the calculus, by their name in the Eunoia signature. -/
private def parserRules : List (String × CRule) := [
  ("scope", .scope),
  ("contra", .contra),
  ("refl", .refl),
  ("symm", .symm),
  ("trans", .trans)
]

private def parserRuleMap : Std.HashMap String CRule := .ofList parserRules

private def parserRule (name : String) : Option CRule := parserRuleMap[name]?

def parserConfig : Logos.Parser.Config Term CRule CCmd CCmdList where
  ops := parserOps
  parseLiteral := parserLiteral
  isType := (· == .Type)
  mkUSort := .USort
  mkUConst := .UConst
  apply := .Apply
  parseRule := parserRule
  mkAssumePush := .assume_push
  mkStep := fun rule args premises =>
    .step rule (args.foldr .cons .nil)
      (premises.foldr (fun i rest => .cons (Int.ofNat i) rest) .nil)
  mkStepPop := fun rule args premises =>
    .step_pop rule (args.foldr .cons .nil)
      (premises.foldr (fun i rest => .cons (Int.ofNat i) rest) .nil)
  mkCmdList := (·.foldr .cons .nil)

def parseProof (proof : String) : Except String (List Term × CCmdList) :=
  Logos.Parser.parseProof parserConfig proof

end Eo
