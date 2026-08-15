module

/-
A generic, table-driven parser for proofs in the s-expression (Eunoia/Ethos)
syntax produced by `cvc5 --dump-proofs --proof-format=cpc`.

The parser itself is independent of any particular signature: everything that is
specific to a calculus (its operators, its literals and its proof rules) is
supplied by a `Logos.Parser.Config`.  The configurations for the calculi in this
repository (`Cpc.Parser`, `CpcMini.Parser`) are generated from the corresponding
Eunoia signature, so this module is the only hand-written part of the pipeline.
-/

public import Std.Data.HashMap
public import Logos.Sexp
import all Logos.Sexp

public section

namespace Logos.Parser

variable {T R C CL : Type}

/-!
## Operator declarations
-/

/--
How the explicit arguments of an operator are combined into a term.  These
correspond to the argument-list attributes of Eunoia's `declare-const`.
-/
inductive Arity (T : Type) where
  /-- The operator takes exactly `n` explicit arguments. -/
  | exact (n : Nat)
  /-- N-ary, left associative: `(f a b c)` denotes `((a f b) f c)`. -/
  | leftAssoc
  /-- N-ary, right associative: `(f a b c)` denotes `(a f (b f c))`. -/
  | rightAssoc
  /--
  N-ary, right associative with a nil terminator: `(f a b c)` denotes
  `(a f (b f (c f nil)))`.  The terminator is computed from the first argument,
  since in Eunoia it is typically indexed by that argument's type; `none` is
  passed when `f` is applied to no arguments at all.
  -/
  | rightAssocNil (nil : Option T → T)
  /--
  Chainable: `(f a b c)` denotes `mk [(f a b), (f b c)]`, where `mk` builds the
  chaining operator's application (usually an n-ary `and`).  As in Ethos, a
  binary application is *not* wrapped, i.e. `(f a b)` denotes `(f a b)`.
  -/
  | chainable (mk : List T → T)

/--
The declaration of a single operator of the signature.

`indexArity` is the number of indices the operator takes, i.e. the `k` in
`(_ f i₁ … i_k)`; `build` turns those indices into the head term and is only
ever called with a list of exactly `indexArity` elements.  A name may be
declared more than once as long as the overloads are distinguishable by their
index/argument counts (e.g. unary `-` versus n-ary `-`).
-/
structure OpDecl (T : Type) where
  name : String
  indexArity : Nat := 0
  arity : Arity T
  build : List T → Option T

/-!
## Term-building helpers

These are also used by generated configurations, e.g. to describe the operator
that chains a chainable predicate.
-/

/-- `(a op (b op (c op nil)))`, where `nil` is computed from the first element. -/
def rightAssocNil (apply : T → T → T) (op : T) (nil : Option T → T) (ts : List T) : T :=
  ts.foldr (fun t acc => apply (apply op t) acc) (nil ts.head?)

/-- `((a op b) op c)`; `none` on an empty list. -/
def leftAssoc (apply : T → T → T) (op : T) : List T → Option T
  | [] => none
  | t :: ts => some (ts.foldl (fun acc u => apply (apply op acc) u) t)

/-- `(a op (b op c))`; `none` on an empty list. -/
def rightAssoc (apply : T → T → T) (op : T) : List T → Option T
  | [] => none
  | t :: ts => some (go t ts)
where
  go (t : T) : List T → T
    | [] => t
    | u :: us => apply (apply op t) (go u us)

/-- The pairwise applications `[(op a b), (op b c), …]` of a chainable operator. -/
def chainSteps (apply : T → T → T) (op : T) : List T → List T
  | a :: b :: rest => apply (apply op a) b :: chainSteps apply op (b :: rest)
  | _ => []

/-- Combine the arguments of an operator according to its arity. -/
def mkOpApp (apply : T → T → T) (arity : Arity T) (op : T) (args : List T) : Option T :=
  match arity with
  | .exact _ => some (args.foldl apply op)
  | .leftAssoc => leftAssoc apply op args
  | .rightAssoc => rightAssoc apply op args
  | .rightAssocNil nil => some (rightAssocNil apply op nil args)
  | .chainable mk =>
    match args with
    | [] => none
    | [_] => none
    | [a, b] => some (apply (apply op a) b)
    | args => some (mk (chainSteps apply op args))

/--
Whether an arity admits the given number of explicit arguments.  Operators of a
fixed arity may be under-applied, since terms are curried and producers do print
partially applied operators (e.g. `(_ extract 3 0)` as the argument of `cong`).
-/
def Arity.admits : Arity T → Nat → Bool
  | .exact n, k => k ≤ n
  | .leftAssoc, k => k ≥ 2
  | .rightAssoc, k => k ≥ 2
  | .chainable _, k => k ≥ 2
  | .rightAssocNil _, _ => true

/-!
## Configuration
-/

/--
Everything the parser needs to know about a particular calculus.

`T` is the type of terms, `R` of proof rules, `C` of commands and `CL` of
command lists.
-/
structure Config (T R C CL : Type) where
  /-- The operators of the signature. -/
  ops : List (OpDecl T)
  /-- Interpret an atom as a literal (numeral, rational, string, bit-vector, …). -/
  parseLiteral : String → Option T
  /-- Whether a term is the sort of sorts, i.e. whether `declare-const` declares a sort. -/
  isType : T → Bool
  /-- The `n`-th uninterpreted sort. -/
  mkUSort : Nat → T
  /-- The `n`-th uninterpreted constant, of the given type. -/
  mkUConst : Nat → T → T
  /-- Function application. -/
  apply : T → T → T
  /-- Interpret the name of a proof rule. -/
  parseRule : String → Option R
  mkAssumePush : T → C
  /-- `mkStep rule args premises`, where premises are offsets into the proof stack. -/
  mkStep : R → List T → List Nat → C
  mkStepPop : R → List T → List Nat → C
  mkCmdList : List C → CL

/-!
## Parser state
-/

structure State (T : Type) where
  /-- Number of uninterpreted sorts declared so far. -/
  usCount : Nat := 0
  /-- Number of uninterpreted constants declared so far. -/
  ufCount : Nat := 0
  /-- Number of proof-stack entries pushed so far. -/
  stackHeight : Nat := 0
  /-- Heights of the currently open `assume-push` scopes, innermost first. -/
  pushHeights : List Nat := []
  /-- Position in the proof stack of each proof step, by name. -/
  idToPos : Std.HashMap String Nat := {}
  /-- Terms bound by `declare-const`/`define`, by name. -/
  terms : Std.HashMap String T := {}
  /-- The operators of the signature, indexed by name. -/
  ops : Std.HashMap String (List (OpDecl T)) := {}

abbrev ParserM (T : Type) := StateT (State T) (Except String)

def State.ofOps (ops : List (OpDecl T)) : State T :=
  { ops := ops.foldl (fun m d => m.insert d.name (m.getD d.name [] ++ [d])) {} }

/-- Record a proof step named `id` at the top of the proof stack. -/
def registerStep (id : String) : ParserM T Unit :=
  modify fun s =>
    { s with idToPos := s.idToPos.insert id s.stackHeight, stackHeight := s.stackHeight + 1 }

/-- Record an `assume-push` step and open a scope at the current height. -/
def registerAssumePush (id : String) : ParserM T Unit :=
  modify fun s =>
    { s with
      idToPos := s.idToPos.insert id s.stackHeight,
      stackHeight := s.stackHeight + 1,
      pushHeights := s.stackHeight :: s.pushHeights }

/-- Record a `step-pop` step, closing the innermost open scope. -/
def registerStepPop (id : String) : ParserM T Unit := do
  let s ← get
  let pushPos :: pushRest := s.pushHeights | throw "Error: step-pop without matching assume-push"
  modify fun s =>
    { s with
      idToPos := s.idToPos.insert id pushPos,
      stackHeight := pushPos + 1,
      pushHeights := pushRest }

/-!
## Terms
-/

/-- Split the tail of `(_ f i₁ … i_k)` into the operator name and its indices. -/
def splitIndexed : List Sexp → ParserM T (String × List Sexp)
  | .atom name :: idxs => return (name, idxs)
  | ss => throw s!"Error: expected an indexed operator name, got {Sexp.expr ss}"

/-- Recognize `f` or `(_ f i₁ … i_k)` as the head of an application. -/
def asOpHead : Sexp → Option (String × List Sexp)
  | .atom name => some (name, [])
  | .expr (.atom "_" :: .atom name :: idxs) => some (name, idxs)
  | _ => none

/-- Select the overload of an operator matching the given index and argument counts. -/
def resolveOp (decls : List (OpDecl T)) (numIndices numArgs : Nat) : Option (OpDecl T) :=
  let decls := decls.filter (·.indexArity == numIndices)
  -- An exact-arity overload always wins, so that e.g. `(- x)` is unary negation
  -- even though `-` is also declared as an n-ary operator.
  let isExact (d : OpDecl T) : Bool := match d.arity with
    | .exact n => n == numArgs
    | _ => false
  match decls.find? isExact with
  | some d => some d
  | none => decls.find? (·.arity.admits numArgs)

mutual

/-- Parse a term, reporting the failing subterm on error. -/
partial def parseTerm (cfg : Config T R C CL) (s : Sexp) : ParserM T T := do
  try
    parseTermCore cfg s
  catch e =>
    throw s!"{e}\nError: failed to parse term {s}"

partial def parseTermCore (cfg : Config T R C CL) : Sexp → ParserM T T
  | .atom a => do
    if let some decls := (← get).ops[a]? then
      -- A bare operator name denotes the (possibly partially applied) head term.
      let decls := decls.filter (·.indexArity == 0)
      let isNullary (d : OpDecl T) : Bool := match d.arity with
        | .exact 0 => true
        | _ => false
      if let some d := decls.find? isNullary <|> decls.head? then
        let some t := d.build [] | throw s!"Error: could not build operator {a}"
        return t
    if let some t := (← get).terms[a]? then
      return t
    if let some t := cfg.parseLiteral a then
      return t
    throw s!"Error: unknown identifier {a}"
  | .expr [] => throw "Error: empty s-expression"
  | .expr (.atom "_" :: rest) => do
    let (name, idxs) ← splitIndexed rest
    parseApp cfg name idxs []
  | .expr (f :: args) => do
    let args ← args.mapM (parseTerm cfg)
    match asOpHead f with
    | some (name, idxs) => parseApp cfg name idxs args
    | none => return args.foldl cfg.apply (← parseTerm cfg f)

/--
Build the application of the operator (or declared symbol) `name`, indexed by
`idxs`, to the already-parsed `args`.
-/
partial def parseApp (cfg : Config T R C CL) (name : String) (idxs : List Sexp)
    (args : List T) : ParserM T T := do
  let decls := (← get).ops.getD name []
  if !decls.isEmpty then
    let idxs ← idxs.mapM (parseTerm cfg)
    let some d := resolveOp decls idxs.length args.length
      | throw s!"Error: no declaration of {name} takes {idxs.length} indices and \
                 {args.length} arguments"
    let some head := d.build idxs | throw s!"Error: bad indices for operator {name}"
    let some t := mkOpApp cfg.apply d.arity head args
      | throw s!"Error: wrong number of arguments ({args.length}) for operator {name}"
    return t
  if !idxs.isEmpty then
    throw s!"Error: unknown indexed operator {name}"
  return args.foldl cfg.apply (← parseTermCore cfg (.atom name))

end

/-!
## Commands
-/

def parseName : Sexp → ParserM T String
  | .atom a => return a
  | s => throw s!"Error: expected a name, got {s}"

/-- Resolve a premise, given by step name, to its offset from the top of the stack. -/
def parsePremise (p : Sexp) : ParserM T Nat := do
  let name ← parseName p
  let some pos := (← get).idToPos[name]? | throw s!"Error: unknown premise {name}"
  let height := (← get).stackHeight
  if height ≤ pos then throw s!"Error: premise {name} is not in scope"
  return height - pos - 1

/-- The `:rule`/`:premises`/`:args` annotations of a `step` or `step-pop`. -/
structure StepAnnots where
  rule : Option String := none
  premises : List Sexp := []
  args : List Sexp := []

def parseAnnots (ctx : Sexp) : List Sexp → ParserM T StepAnnots :=
  go {}
where
  go (acc : StepAnnots) : List Sexp → ParserM T StepAnnots
    | [] => return acc
    | .atom ":rule" :: v :: rest => do go { acc with rule := some (← parseName v) } rest
    | .atom ":premises" :: .expr ps :: rest => go { acc with premises := ps } rest
    | .atom ":args" :: .expr as :: rest => go { acc with args := as } rest
    | k :: _ => throw s!"Error: unexpected annotation {k} in {ctx}"

/--
Drop the conclusion of a step if one is present; Logos recomputes conclusions
from the rule, so the printed one is redundant.
-/
def dropConclusion : List Sexp → List Sexp
  | [] => []
  | c :: rest =>
    match c with
    | .atom a => if a.startsWith ":" then c :: rest else rest
    | .expr _ => rest

/-- The result of parsing one top-level command. -/
inductive Command (T C : Type) where
  /-- An `assume`, which becomes an assumption of the proof. -/
  | assumption (t : T)
  /-- A proof-stack command. -/
  | cmd (c : C)
  /-- A declaration or definition, which only updates the parser state. -/
  | decl

def parseCommand (cfg : Config T R C CL) (s : Sexp) : ParserM T (Command T C) := do
  try
    go s
  catch e =>
    throw s!"{e}\nError: failed to parse command {s}"
where
  annots (rest : List Sexp) : ParserM T (R × List T × List Nat) := do
    let annots ← parseAnnots s (dropConclusion rest)
    let some ruleName := annots.rule | throw s!"Error: missing :rule in {s}"
    let some rule := cfg.parseRule ruleName | throw s!"Error: unknown rule {ruleName}"
    let premises ← annots.premises.mapM parsePremise
    let args ← annots.args.mapM (parseTerm cfg)
    return (rule, args, premises)
  go : Sexp → ParserM T (Command T C)
    | .expr [.atom "declare-const", name, ty] => do
      let name ← parseName name
      let ty ← parseTerm cfg ty
      if cfg.isType ty then
        modify fun s =>
          { s with
            usCount := s.usCount + 1,
            terms := s.terms.insert name (cfg.mkUSort (s.usCount + 1)) }
      else
        modify fun s =>
          { s with
            ufCount := s.ufCount + 1,
            terms := s.terms.insert name (cfg.mkUConst (s.ufCount + 1) ty) }
      return .decl
    | .expr [.atom "define", name, .expr [], body] => do
      let name ← parseName name
      let body ← parseTerm cfg body
      modify fun s => { s with terms := s.terms.insert name body }
      return .decl
    | .expr [.atom "assume", name, t] => do
      let name ← parseName name
      let t ← parseTerm cfg t
      registerStep name
      return .assumption t
    | .expr [.atom "assume-push", name, t] => do
      let name ← parseName name
      let t ← parseTerm cfg t
      registerAssumePush name
      return .cmd (cfg.mkAssumePush t)
    | .expr (.atom "step" :: name :: rest) => do
      let name ← parseName name
      let (rule, args, premises) ← annots rest
      registerStep name
      return .cmd (cfg.mkStep rule args premises)
    | .expr (.atom "step-pop" :: name :: rest) => do
      let name ← parseName name
      let (rule, args, premises) ← annots rest
      registerStepPop name
      return .cmd (cfg.mkStepPop rule args premises)
    | s => throw s!"Error: unrecognized command {s}, expected one of declare-const, define, \
                    assume, assume-push, step or step-pop"

/--
Some producers wrap the whole proof in a single pair of parentheses; accept both
that shape and a bare sequence of commands.
-/
def unwrapProof : List Sexp → List Sexp
  | [.expr ss] => if !ss.isEmpty && ss.all Sexp.isExpr then ss else [.expr ss]
  | ss => ss

def parseCommands (cfg : Config T R C CL) (ss : List Sexp) : ParserM T (List T × CL) := do
  let mut assums := #[]
  let mut cmds := #[]
  for s in ss do
    match ← parseCommand cfg s with
    | .assumption t =>
      if !cmds.isEmpty then
        throw s!"Error: assumption after the first proof step: {s}"
      assums := assums.push t
    | .cmd c => cmds := cmds.push c
    | .decl => pure ()
  return (assums.toList, cfg.mkCmdList cmds.toList)

/-- Parse a proof into its assumptions and its list of commands. -/
def parseProof (cfg : Config T R C CL) (input : String) : Except String (List T × CL) := do
  let ss ← Sexp.Parser.manySexps!.run input
  (parseCommands cfg (unwrapProof ss)).run' (State.ofOps cfg.ops)

end Logos.Parser
