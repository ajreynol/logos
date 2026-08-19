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
  Argument list: `(f a b c)` denotes `(f (mk [a, b, c]))`.  This corresponds
  to Eunoia's `:arg-list` attribute, whose argument names the n-ary operator
  represented here by `mk`.  The annotated operator is unary, and at least one
  argument must be gathered.
  -/
  | argList (mk : List T → T)

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
  | .argList mk =>
    if args.isEmpty then none else some (apply op (mk args))

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
  | .argList _, k => k > 0
  | .rightAssocNil _, _ => true

/-!
## Literals

Lexing literals is the same for every calculus, so it happens here; a `Config`
only has to say how to turn a lexed literal into a term.
-/

/-- A literal, before it is mapped into the term language of a calculus. -/
inductive Literal where
  /-- An integer literal, e.g. `12` or `-12`. -/
  | numeral (n : Int)
  /-- A rational literal, e.g. `1/2` or `0.5`.  The denominator is positive. -/
  | rational (num den : Int)
  /-- A string literal; the enclosing quotes are removed and `""` unescaped to `"`. -/
  | string (s : String)
  /-- A bit-vector literal, e.g. `#b0110` or `#x1f`, of the given width and value. -/
  | binary (width : Nat) (value : Nat)
deriving Repr, BEq, Inhabited

namespace Literal

private def digitsToNat (base : Nat) (digitValue : Char → Option Nat) :
    List Char → Option Nat
  | [] => none
  | ds => ds.foldlM (fun acc c => do return base * acc + (← digitValue c)) 0

private def binDigit (c : Char) : Option Nat :=
  if c == '0' then some 0 else if c == '1' then some 1 else none

private def decDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat) else none

private def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Replace each `""` by a single `"`, as in the SMT-LIB string escape. -/
private def unescape : List Char → List Char
  | '"' :: '"' :: cs => '"' :: unescape cs
  | c :: cs => c :: unescape cs
  | [] => []

/-- Normalize a fraction so that its denominator is positive; fails on `0`. -/
private def mkRational (num den : Int) : Option Literal :=
  if den == 0 then none
  else if den < 0 then some (.rational (-num) (-den))
  else some (.rational num den)

/-- A decimal literal such as `1.5` or `-0.25`, as a fraction. -/
private def ofDecimal (s : String) : Option Literal := do
  let [intPart, fracPart] := s.splitOn "." | none
  if fracPart.isEmpty then none
  let sign := if intPart.startsWith "-" then -1 else 1
  let intPart := if intPart.startsWith "-" then (intPart.drop 1).toString else intPart
  let whole ← digitsToNat 10 decDigit intPart.toList
  let frac ← digitsToNat 10 decDigit fracPart.toList
  let scale := 10 ^ fracPart.length
  mkRational (sign * (Int.ofNat (whole * scale + frac))) (Int.ofNat scale)

/-- Lex an atom as a literal, if it is one. -/
def ofString (value : String) : Option Literal :=
  if value.startsWith "\"" && value.endsWith "\"" && value.length ≥ 2 then
    some (.string (String.ofList (unescape (value.drop 1).toString.toList.dropLast)))
  else if value.startsWith "#b" then
    let digits := (value.drop 2).toString.toList
    (digitsToNat 2 binDigit digits).map (.binary digits.length)
  else if value.startsWith "#x" then
    let digits := (value.drop 2).toString.toList
    (digitsToNat 16 hexDigit digits).map (.binary (4 * digits.length))
  else
    match value.splitOn "/" with
    | [num, den] => do mkRational (← num.toInt?) (← den.toInt?)
    | _ => match value.toInt? with
      | some n => some (.numeral n)
      | none => ofDecimal value

end Literal

/-!
## Datatypes
-/

/-- A constructor of a datatype: its name and its selectors, with their argument types. -/
structure ConsSpec (T : Type) where
  name : String
  selectors : List (String × T)

/-- One datatype of a `declare-datatypes` block. -/
structure DatatypeSpec (T : Type) where
  name : String
  constructors : List (ConsSpec T)

/-- How a calculus represents the contents of a `declare-datatypes` block. -/
structure DatatypeOps (T : Type) where
  /--
  A reference to a datatype of the block currently being declared.  Occurrences
  of the block's own datatypes in its constructors' argument types are parsed as
  such references, since the block is not yet built when they are read.
  -/
  mkRef : String → T
  /--
  The bindings (one per sort, constructor and selector) introduced by a block.
  The datatypes and their constructors are in declaration order.
  -/
  mkDecls : List (DatatypeSpec T) → Option (List (String × T))

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
  /-- Interpret a literal (numeral, rational, string, bit-vector) as a term. -/
  parseLiteral : Literal → Option T
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
  /-- Datatype support; `none` if the calculus has no datatypes. -/
  datatypes : Option (DatatypeOps T) := none

/-!
## Parser state
-/

/--
A `define` that takes parameters.  Eunoia has no lambda, so such a definition is
a macro: its body is kept as an s-expression and read again wherever the defined
symbol is applied, with the parameters bound to the arguments given there.
-/
structure Macro where
  /-- The names of the parameters, in order; their declared types are unused. -/
  params : List String
  body : Sexp

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
  /-- Macros introduced by a `define` with parameters, by name. -/
  macros : Std.HashMap String Macro := {}
  /-- The macros currently being expanded, used to reject recursive `define`s. -/
  expanding : List String := []
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

/--
Select an indexed operator written in Eunoia's flat form, `(f i₁ … iₖ a₁ … aₙ)`.
The indices are part of the ordinary argument list in that syntax.  Prefer an
exactly saturated overload, as `resolveOp` does for explicit indexed syntax.
-/
def resolveFlatOp (decls : List (OpDecl T)) (numArgs : Nat) : Option (OpDecl T) :=
  let decls := decls.filter fun d =>
    d.indexArity > 0 && d.indexArity ≤ numArgs &&
      d.arity.admits (numArgs - d.indexArity)
  let isExact (d : OpDecl T) : Bool := match d.arity with
    | .exact n => n == numArgs - d.indexArity
    | _ => false
  match decls.find? isExact with
  | some d => some d
  | none => decls.head?

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
    if let some t := (Literal.ofString a).bind cfg.parseLiteral then
      return t
    if let some m := (← get).macros[a]? then
      throw s!"Error: {a} takes {m.params.length} arguments and cannot be used unapplied"
    throw s!"Error: unknown identifier {a}"
  | .expr [] => throw "Error: empty s-expression"
  | .expr [.atom "as", .atom name, ty] =>
    -- CPC uses SMT-LIB's type-ascription syntax for indexed constants such as
    -- `(as set.empty (Set Int))`; its sort is the operator's Eunoia index.
    parseApp cfg name [ty] []
  | .expr [.atom "let", .expr bindings, body] =>
    parseLet cfg bindings body
  | .expr (.atom "_" :: rest) => do
    let (name, idxs) ← splitIndexed rest
    parseUnderscoreApp cfg name idxs []
  | .expr (f :: args) => do
    let args ← args.mapM (parseTerm cfg)
    match f with
    | .expr (.atom "_" :: rest) => do
      let (name, idxs) ← splitIndexed rest
      parseUnderscoreApp cfg name idxs args
    | _ =>
      match asOpHead f with
      | some (name, idxs) => parseApp cfg name idxs args
      | none => return args.foldl cfg.apply (← parseTerm cfg f)

/--
Parse an expression headed by `_`.  If the name has an operator declaration
with the given number of indices, this is SMT-style indexed syntax such as
`(_ extract 1 0)`.  Otherwise `_` is Eunoia's higher-order application marker,
so `(_ BitVec 4)` is parsed like `(BitVec 4)`.  Any outer arguments are then
applied to the resulting term.
-/
partial def parseUnderscoreApp (cfg : Config T R C CL) (name : String)
    (idxs : List Sexp) (args : List T) : ParserM T T := do
  let decls := (← get).ops.getD name []
  if decls.any (·.indexArity == idxs.length) then
    parseApp cfg name idxs args
  else
    let head ← parseTerm cfg (.expr (.atom name :: idxs))
    return args.foldl cfg.apply head

/--
Build the application of the operator (or declared symbol) `name`, indexed by
`idxs`, to the already-parsed `args`.
-/
partial def parseApp (cfg : Config T R C CL) (name : String) (idxs : List Sexp)
    (args : List T) : ParserM T T := do
  if let some m := (← get).macros[name]? then
    if !idxs.isEmpty then
      throw s!"Error: {name} is defined by define and cannot be indexed"
    if args.length < m.params.length then
      throw s!"Error: {name} takes {m.params.length} arguments but is applied to {args.length}"
    -- A macro whose body denotes a function may be applied to further arguments.
    let (args, extra) := args.splitAt m.params.length
    return extra.foldl cfg.apply (← expandMacro cfg name m args)
  let decls := (← get).ops.getD name []
  if !decls.isEmpty then
    let idxs ← idxs.mapM (parseTerm cfg)
    if let some d := resolveOp decls idxs.length args.length then
      return ← buildOpApp cfg name d idxs args
    -- `declare-parameterized-const` uses ordinary arguments for its indices,
    -- and this is the flat form emitted by cvc5: `(extract 1 0 x)` rather than
    -- `((_ extract 1 0) x)`.  Explicit indexed syntax above takes precedence.
    if idxs.isEmpty then
      if let some d := resolveFlatOp decls args.length then
        let (flatIdxs, flatArgs) := args.splitAt d.indexArity
        return ← buildOpApp cfg name d flatIdxs flatArgs
    throw s!"Error: no declaration of {name} takes {idxs.length} indices and \
              {args.length} arguments"
  if !idxs.isEmpty then
    throw s!"Error: unknown indexed operator {name}"
  return args.foldl cfg.apply (← parseTermCore cfg (.atom name))

/-- Build an already-resolved operator application. -/
partial def buildOpApp (cfg : Config T R C CL) (name : String) (d : OpDecl T)
    (idxs args : List T) : ParserM T T := do
  let some head := d.build idxs | throw s!"Error: bad indices for operator {name}"
  let some t := mkOpApp cfg.apply d.arity head args
    | throw s!"Error: wrong number of arguments ({args.length}) for operator {name}"
  return t

/--
Parse an SMT-LIB `let`.  Binding values are read in the surrounding scope
(parallel-binding semantics), then all names are in scope only for the body.
-/
partial def parseLet (cfg : Config T R C CL) (bindings : List Sexp)
    (body : Sexp) : ParserM T T := do
  let bindings : List (String × Sexp) ← bindings.mapM fun
    | .expr [.atom name, value] => return (name, value)
    | binding => throw s!"Error: expected a let binding, got {binding}"
  let values ← bindings.mapM fun (name, value) => do
    return (name, ← parseTerm cfg value)
  let saved := (← get).terms
  modify fun s =>
    { s with terms := values.foldl (fun terms (name, value) =>
        terms.insert name value) s.terms }
  let restore : ParserM T Unit := modify fun s => { s with terms := saved }
  try
    let result ← parseTerm cfg body
    restore
    return result
  catch e =>
    restore
    throw e

/--
Expand the macro `name` at a use site: read its body with the parameters bound to
`args`.  The bindings are undone afterwards, so a parameter shadows any symbol of
the same name only within the body.
-/
partial def expandMacro (cfg : Config T R C CL) (name : String) (m : Macro)
    (args : List T) : ParserM T T := do
  if (← get).expanding.contains name then
    throw s!"Error: recursive define {name}"
  let saved := (← get).terms
  modify fun s =>
    { s with
      terms := (m.params.zip args).foldl (fun ts (p, t) => ts.insert p t) s.terms,
      expanding := name :: s.expanding }
  let restore : ParserM T Unit :=
    modify fun s => { s with terms := saved, expanding := s.expanding.tail }
  try
    let t ← parseTerm cfg m.body
    restore
    return t
  catch e =>
    restore
    throw e

end

/-!
## Commands
-/

def parseName : Sexp → ParserM T String
  | .atom a => return a
  | s => throw s!"Error: expected a name, got {s}"

/-- Parse `(name arity)` from the sort list of a `declare-datatypes` block. -/
def parseDatatypeName : Sexp → ParserM T String
  | .expr [.atom name, .atom arity] =>
    if arity == "0" then return name
    else throw s!"Error: parametric datatype {name} (arity {arity}) is not supported"
  | s => throw s!"Error: expected a datatype name and arity, got {s}"

/-- Parse one constructor, `(cname (sel type) …)`. -/
def parseConsSpec (cfg : Config T R C CL) : Sexp → ParserM T (ConsSpec T)
  | .expr (.atom name :: sels) => do
    let selectors ← sels.mapM fun
      | .expr [.atom sel, ty] => do return (sel, ← parseTerm cfg ty)
      | s => throw s!"Error: expected a selector and its type, got {s}"
    return { name, selectors }
  | s => throw s!"Error: expected a datatype constructor, got {s}"

/--
Parse a `declare-datatypes` block and bind the sorts, constructors and selectors
it introduces.
-/
def parseDatatypes (cfg : Config T R C CL) (sorts bodies : List Sexp) : ParserM T Unit := do
  let some dtOps := cfg.datatypes
    | throw "Error: this calculus does not support declare-datatypes"
  let names ← sorts.mapM parseDatatypeName
  if names.length != bodies.length then
    throw s!"Error: {names.length} datatype names but {bodies.length} datatype bodies"
  -- While the block is being read, occurrences of its own datatypes in the
  -- constructors' argument types are parsed as references.
  let saved := (← get).terms
  modify fun s =>
    { s with terms := names.foldl (fun m n => m.insert n (dtOps.mkRef n)) s.terms }
  let specs ← (names.zip bodies).mapM fun (name, body) => do
    let .expr ctors := body | throw s!"Error: expected a list of constructors, got {body}"
    if let .atom "par" :: _ := ctors then
      throw s!"Error: parametric datatype {name} is not supported"
    let constructors ← ctors.mapM (parseConsSpec cfg)
    return ({ name, constructors } : DatatypeSpec T)
  modify fun s => { s with terms := saved }
  let some bindings := dtOps.mkDecls specs
    | throw s!"Error: could not build the declaration of {String.intercalate ", " names}"
  modify fun s =>
    { s with terms := bindings.foldl (fun m (n, t) => m.insert n t) s.terms }

/-!
## Declarations
-/

/-- Bind `name` to a fresh uninterpreted sort or constant, according to `ty`. -/
def declareSymbol (cfg : Config T R C CL) (name : String) (ty : T) : ParserM T Unit :=
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

/--
The type `(-> t₁ … tₙ res)` of a symbol declared by `declare-fun`, `declare-sort`
or `declare-type`.  It is built from the signature's own `->` operator, so a
calculus without function types simply rejects these commands with more than
zero arguments.
-/
def parseFunType (cfg : Config T R C CL) (args : List Sexp) (res : Sexp) : ParserM T T :=
  match args with
  | [] => parseTerm cfg res
  | args => parseTerm cfg (.expr (.atom "->" :: (args ++ [res])))

/--
Parse the parameter list of a `define`.  Only the parameter names are recorded:
the body is read where the macro is used, so its parameters are given the types
of the arguments they stand for.
-/
def parseMacroParams : List Sexp → ParserM T (List String)
  | [] => return []
  | .expr (.atom name :: _ :: _) :: rest => return name :: (← parseMacroParams rest)
  | s :: _ => throw s!"Error: expected a parameter and its type, got {s}"

/-- Parse the arity of a `declare-sort`. -/
def parseArity : Sexp → ParserM T Nat
  | .atom a =>
    match a.toNat? with
    | some n => return n
    | none => throw s!"Error: expected a sort arity, got {a}"
  | s => throw s!"Error: expected a sort arity, got {s}"

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
  /--
  A command that does not extend the proof: a declaration or definition, which
  only updates the parser state, or an ignored command such as `include`.
  -/
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
      declareSymbol cfg (← parseName name) (← parseTerm cfg ty)
      return .decl
    | .expr [.atom "declare-fun", name, .expr args, ty] => do
      declareSymbol cfg (← parseName name) (← parseFunType cfg args ty)
      return .decl
    | .expr [.atom "declare-sort", name, arity] => do
      -- `(declare-sort S n)` declares a symbol of type `(-> Type … Type)`; for
      -- `n = 0` that is `Type` itself, i.e. an uninterpreted sort.
      let arity ← parseArity arity
      let ty ← parseFunType cfg (List.replicate arity (.atom "Type")) (.atom "Type")
      declareSymbol cfg (← parseName name) ty
      return .decl
    | .expr [.atom "declare-type", name, .expr args] => do
      -- The Eunoia spelling of `declare-sort`, whose arguments are given by type.
      declareSymbol cfg (← parseName name) (← parseFunType cfg args (.atom "Type"))
      return .decl
    | .expr [.atom "declare-datatypes", .expr sorts, .expr bodies] => do
      parseDatatypes cfg sorts bodies
      return .decl
    | .expr [.atom "define", name, .expr [], body] => do
      -- A definition without parameters is read once, where it is given.
      let name ← parseName name
      let body ← parseTerm cfg body
      modify fun s => { s with terms := s.terms.insert name body }
      return .decl
    | .expr [.atom "define", name, .expr params, body] => do
      let name ← parseName name
      let params ← parseMacroParams params
      modify fun s => { s with macros := s.macros.insert name { params, body } }
      return .decl
    | .expr (.atom "include" :: _) =>
      -- Logos has the whole signature built in, so included files are ignored.
      return .decl
    | .expr (.atom "reference" :: _) =>
      -- The input problem is not checked against, so references are ignored.
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
    | s => throw s!"Error: unrecognized command {s}, expected one of declare-const, \
                    declare-fun, declare-sort, declare-type, declare-datatypes, define, \
                    include, reference, assume, assume-push, step or step-pop"

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
