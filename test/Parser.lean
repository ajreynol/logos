module

public import Logos.Parser
import all Logos.Parser

namespace Logos.Parser.Tests

private inductive TestTerm where
  | atom (name : String)
  | app (fn arg : TestTerm)
  | gathered (args : List TestTerm)
  | type
  | usort (i : Nat)
  | uconst (i : Nat) (ty : TestTerm)
deriving BEq, Repr

private def mkApply : TestTerm → TestTerm → TestTerm := .app
private def gather : List TestTerm → TestTerm := .gathered

private def f : TestTerm := .atom "f"
private def a : TestTerm := .atom "a"
private def b : TestTerm := .atom "b"

example :
    mkOpApp mkApply (.argList gather) f [a, b] =
      some (.app f (.gathered [a, b])) := by
  rfl

example : mkOpApp mkApply (.argList gather) f [] = none := by
  rfl

example : (Arity.argList gather).admits 0 = false := by
  rfl

example : (Arity.argList gather).admits 1 = true := by
  rfl

example : (Arity.argList gather).admits 3 = true := by
  rfl

/-!
## Commands

A minimal signature, with just enough operators to write the types of declared
symbols, exercises the command grammar independently of any calculus.
-/

private abbrev TestCmd := String × List TestTerm × List Nat

private def testConfig : Config TestTerm String TestCmd (List TestCmd) where
  ops := [
    { name := "Type", arity := .exact 0, build := fun | [] => some .type | _ => none },
    { name := "->", arity := .rightAssoc, build := fun | [] => some (.atom "->") | _ => none }
  ]
  parseLiteral := fun _ => none
  isType := (· == .type)
  mkUSort := .usort
  mkUConst := .uconst
  apply := .app
  parseRule := some
  mkAssumePush := fun t => ("assume-push", [t], [])
  mkStep := fun rule args premises => (rule, args, premises)
  mkStepPop := fun rule args premises => ("pop:" ++ rule, args, premises)
  mkCmdList := id

/-- The assumptions of a parsed proof, or `none` if it does not parse. -/
private def assumptions (input : String) : Option (List TestTerm) :=
  match parseProof testConfig input with
  | .ok (assums, _) => some assums
  | .error _ => none

private def arrow (dom cod : TestTerm) : TestTerm := .app (.app (.atom "->") dom) cod

-- `include` is ignored, `declare-sort` declares an uninterpreted sort and
-- `declare-fun` a symbol of the corresponding function type.
#guard assumptions
    "(include \"../theories/Builtin.eo\")
     (declare-sort U 0)
     (declare-fun f (U) U)
     (declare-const x U)
     (assume @p0 (f x))"
  == some [.app (.uconst 1 (arrow (.usort 1) (.usort 1))) (.uconst 2 (.usort 1))]

-- A `declare-sort` of non-zero arity declares a symbol of type `(-> Type … Type)`.
#guard assumptions
    "(declare-sort U 0)
     (declare-sort Box 1)
     (declare-const b (Box U))
     (assume @p0 b)"
  == some [.uconst 2 (.app (.uconst 1 (arrow .type .type)) (.usort 1))]

-- `declare-type` is the Eunoia spelling of the same declaration.
#guard assumptions
    "(declare-type U ())
     (declare-type Box (Type))
     (declare-const b (Box U))
     (assume @p0 b)"
  == some [.uconst 2 (.app (.uconst 1 (arrow .type .type)) (.usort 1))]

-- `reference` is ignored as well.
#guard assumptions
    "(reference \"problem.smt2\")
     (declare-sort U 0)
     (declare-const x U)
     (assume @p0 x)"
  == some [.uconst 1 (.usort 1)]

-- A `define` with arguments is rejected rather than silently ignored.
#guard assumptions
    "(declare-sort U 0)
     (declare-const x U)
     (define f ((y U)) y)
     (assume @p0 x)"
  == none

end Logos.Parser.Tests
