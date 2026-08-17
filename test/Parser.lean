module

public import Logos.Parser
import all Logos.Parser

namespace Logos.Parser.Tests

private inductive TestTerm where
  | atom (name : String)
  | app (fn arg : TestTerm)
  | gathered (args : List TestTerm)
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

end Logos.Parser.Tests
