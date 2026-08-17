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

/-!
### `define`

A `define` with parameters is a macro: it is expanded wherever it is applied.
-/

private def binary : String := "(declare-sort U 0) (declare-fun g (U U) U)
  (declare-const a U) (declare-const b U)"

private def gTy : TestTerm := arrow (.usort 1) (arrow (.usort 1) (.usort 1))

-- The body is read with the parameters bound to the arguments at the use site.
#guard assumptions (binary ++ "(define swap ((x U) (y U)) (g y x)) (assume @p0 (swap a b))")
  == some [.app (.app (.uconst 1 gTy) (.uconst 3 (.usort 1))) (.uconst 2 (.usort 1))]

-- Macros may be used in the body of another macro.
#guard assumptions (binary ++
    "(define dup ((x U)) (g x x)) (define dupA () (dup a)) (assume @p0 (dupA))")
  == some [.app (.app (.uconst 1 gTy) (.uconst 2 (.usort 1))) (.uconst 2 (.usort 1))]

-- A parameter shadows a symbol of the same name only inside the body.
#guard assumptions (binary ++
    "(define f ((a U)) (g a a)) (assume @p0 (f b)) (assume @p1 a)")
  == some
    [.app (.app (.uconst 1 gTy) (.uconst 3 (.usort 1))) (.uconst 3 (.usort 1)),
     .uconst 2 (.usort 1)]

-- A macro whose body denotes a function may be applied to further arguments.
#guard assumptions (binary ++ "(define ap ((h U)) (g h)) (assume @p0 (ap a b))")
  == some [.app (.app (.uconst 1 gTy) (.uconst 2 (.usort 1))) (.uconst 3 (.usort 1))]

-- A macro may not be under-applied, or used unapplied.
#guard assumptions (binary ++ "(define swap ((x U) (y U)) (g y x)) (assume @p0 (swap a))")
  == none
#guard assumptions (binary ++ "(define swap ((x U) (y U)) (g y x)) (assume @p0 swap)")
  == none

-- A recursive `define` is rejected rather than expanded forever.
#guard assumptions (binary ++ "(define f ((x U)) (g x (f x))) (assume @p0 (f a))")
  == none

-- A `define` without parameters is still read where it is given.
#guard assumptions (binary ++ "(define ga () (g a a)) (assume @p0 ga)")
  == some [.app (.app (.uconst 1 gTy) (.uconst 2 (.usort 1))) (.uconst 2 (.usort 1))]

end Logos.Parser.Tests
