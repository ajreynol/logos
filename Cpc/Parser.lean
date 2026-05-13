import Cpc.Sexp
import Cpc.Logos

namespace Eo

structure Parser.State where
  usCount : Nat := 0
  ufCount : Nat := 0
  stackHeight : Nat := 0
  pushHeights : List Nat := []
  idToPos : Std.HashMap Nat Nat := {}
  terms : Std.HashMap String Eo.Term := {}
deriving Repr

abbrev ParserM := StateT Parser.State (Except String)

namespace Parser

def reservedPrefix : String := "@@"

def rejectReservedName (kind name : String) : ParserM Unit := do
  if name.startsWith reservedPrefix then
    throw s!"Error: {kind} {name} uses reserved prefix {reservedPrefix}"

def registerAssumePush (id : Nat) : ParserM Unit := do
  modify fun s => { s with
    idToPos := s.idToPos.insert id s.stackHeight,
    stackHeight := s.stackHeight + 1,
    pushHeights := s.stackHeight :: s.pushHeights }

def registerStep (id : Nat) : ParserM Unit := do
  modify fun s => { s with idToPos := s.idToPos.insert id s.stackHeight, stackHeight := s.stackHeight + 1 }

def registerStepPop (id : Nat) : ParserM Unit := do
  let s ← get
  let pushPos :: pushRest := s.pushHeights | throw "Error: step-pop without matching assume-push"
  modify fun s => { s with
    idToPos := s.idToPos.insert id pushPos,
    stackHeight := pushPos + 1,
    pushHeights := pushRest }

partial def parseTerm (t : Sexp) : ParserM Eo.Term := do
  try
    go t
  catch e =>
    throw s!"{e}\nError: failed to parse term {t}"
where
  go (t : Sexp) : ParserM Eo.Term := do
    if let sexp!{Type} := t then
      return .Type
    if let sexp!{(-> ⦃αs⦄)} := t then
      return ← rightAssoc .FunType αs
    if let sexp!{Bool} := t then
      return .Bool
    if let sexp!{false} := t then
      return .Boolean false
    if let sexp!{true} := t then
      return .Boolean true
    if let sexp!{(not {t})} := t then
      let t ← parseTerm t
      return .Apply (Term.UOp UserOp.not) t
    if let sexp!{(and ⦃ts⦄)} := t then
      return ← rightAssocNil (Term.UOp UserOp.and) ts (.Boolean true)
    if let sexp!{(or ⦃ts⦄)} := t then
      return ← rightAssocNil (Term.UOp UserOp.or) ts (.Boolean false)
    if let sexp!{(=> ⦃ts⦄)} := t then
      return ← rightAssoc (Term.UOp UserOp.imp) ts
    if let sexp!{(xor ⦃ts⦄)} := t then
      return ← leftAssoc (Term.UOp UserOp.xor) ts
    if let sexp!{(= {t1} {t2})} := t then
      -- TODO: support n-ary equality?
      let t1 ← parseTerm t1
      let t2 ← parseTerm t2
      return .Apply (.Apply (Term.UOp UserOp.eq) t1) t2
    if let sexp!{Int} := t then
      return Term.UOp UserOp.Int
    if let sexp!{(@list ⦃ts⦄)} := t then
      return ← rightAssocNil .__eo_List_cons ts .__eo_List_nil
    -- Function application. Note that this must come after all the special forms above,
    -- since they also look like function application.
    if let sexp!{({f} ⦃ts⦄)} := t then
      let f ← parseTerm f
      let ts ← ts.mapM parseTerm
      return ts.foldl (fun acc t => .Apply acc t) f
    if let .atom x := t then
      if x.isNat then
        return .Numeral x.toNat!
      -- look up x in terms
      if let .some t := (← get).terms[x]? then
        return t
      throw s!"Error: unknown identifier {x}"
    throw s!"Error: unrecognized s-expr {t}"
  leftAssocNil (op : Term) (ts : List Sexp) (nil : Term) : ParserM Term := do
    let ts ← ts.mapM parseTerm
    return ts.foldl (fun acc t => .Apply (.Apply op acc) t) nil
  rightAssocNil (op : Term) (ts : List Sexp) (nil : Term) : ParserM Term := do
    let ts ← ts.mapM parseTerm
    return ts.foldr (fun acc t => .Apply (.Apply op acc) t) nil
  leftAssoc (op : Term) (ts : List Sexp) : ParserM Term := do
    let t :: ts ← ts.mapM parseTerm | throw s!"Error: expected at least one argument to {repr op}, got {ts}"
    return ts.foldl (fun acc t => .Apply (.Apply op acc) t) t
  rightAssoc (op : Term) (ts : List Sexp) : ParserM Term := do
    let t :: ts ← ts.mapM parseTerm | throw s!"Error: expected at least one argument to {repr op}, got {ts}"
    let (ts, t) := ((t :: ts).dropLast, (t :: ts).getLast nofun)
    return ts.foldr (fun t acc => .Apply (.Apply op t) acc) t

def parseDecl (s : Sexp) : ParserM Unit := do
  let sexp!{(declare-const {.atom x} {α})} := s | throw s!"Error: expected a declare-const, got {s}"
  rejectReservedName "declare-const name" x
  let t ← parseTerm α
  match t with
  | .Type =>
    -- TODO: support arbitrary arities
    modify fun s => { s with usCount := s.usCount + 1, terms := s.terms.insert x (.USort s.usCount) }
  | _ =>
    modify fun s => { s with ufCount := s.ufCount + 1, terms := s.terms.insert x (.UConst s.ufCount t) }

def parseDef (s : Sexp) : ParserM Unit := do
  let sexp!{(define {.atom t} () {v})} := s | throw s!"Error: expected a define, got {s}"
  rejectReservedName "define name" t
  let v ← parseTerm v
  modify fun st => { st with terms := st.terms.insert t v }

def parseId (s : String) : ParserM Nat := do
  if !s.startsWith "@p" then throw s!"Error: expected a step index starting with @p, got {s}"
  let s := s.drop 2
  if let some i := s.toNat? then
    return i
  throw s!"Error: invalid step index {s}"

def parsePremise (p : Sexp) : ParserM CIndex := do
  let .atom s := p | throw s!"Error: expected a premise index, got {p}"
  let i ← parseId s
  let some pos := (← get).idToPos[i]? | throw s!"Error: unknown premise @p{i}, {(← get).idToPos.toList}"
  let h := (← get).stackHeight
  return h - pos - 1

def parseAssum (s : Sexp) : ParserM Term := do
  let sexp!{(assume {.atom name} {t})} := s | throw s!"Error: expected an assume, got {s}"
  let id ← parseId name
  registerStep id
  parseTerm t

def parseRule (s : String) : ParserM CRule := do
  match s with
  | "symm" => return .symm
  | "and_elim" => return .and_elim
  | "chain_resolution" => return .chain_resolution
  | "chain_m_resolution" => return .chain_m_resolution
  | "scope" => return .scope
  | "process_scope" => return .process_scope
  | "and_intro" => return .and_intro
  | "modus_ponens" => return .modus_ponens
  | "implies_elim" => return .implies_elim
  | "cnf_and_neg" => return .cnf_and_neg
  | "cnf_and_pos" => return .cnf_and_pos
  | "resolution" => return .resolution
  | "reordering" => return .reordering
  | "cong" => return .cong
  | _ => throw s!"Error: unknown rule {s}"

def parseCmd (c : Sexp) : ParserM Eo.CCmd := do
  try
    go c
  catch e =>
    throw s!"{e}\nError: failed to parse command {c}"
where
  go (c : Sexp) : ParserM Eo.CCmd := do
    match c with
    | sexp!{(assume-push {.atom name} {t})} => do
      let id ← parseId name
      let t ← parseTerm t
      registerAssumePush id
      return .assume_push t
    | sexp!{(step {.atom s} :rule {.atom r} :premises (⦃ps⦄) :args (⦃as⦄))} => do
      let sid ← parseId s
      let r ← parseRule r
      let ps ← ps.mapM parsePremise
      let as ← as.mapM parseTerm
      registerStep sid
      return .step r (as.foldr .cons .nil) (ps.foldr .cons .nil)
    | sexp!{(step {.atom s} {_} :rule {.atom r} :premises (⦃ps⦄) :args (⦃as⦄))} => do
      let sid ← parseId s
      let r ← parseRule r
      let ps ← ps.mapM parsePremise
      let as ← as.mapM parseTerm
      registerStep sid
      return .step r (as.foldr .cons .nil) (ps.foldr .cons .nil)
    | sexp!{(step-pop {.atom s} :rule {.atom r} :premises (⦃ps⦄) :args (⦃as⦄))} => do
      let sid ← parseId s
      let r ← parseRule r
      let ps ← ps.mapM parsePremise
      let as ← as.mapM parseTerm
      registerStepPop sid
      return .step_pop r (as.foldr .cons .nil) (ps.foldr .cons .nil)
    | _ => throw s!"Error: unrecognized command {c}"

def withDecls (decls : List Sexp) (k : ParserM α) : ParserM α := do
  decls.forM parseDecl
  k

def withDefs (defs : List Sexp) (k : ParserM α) : ParserM α := do
  defs.forM parseDef
  k

def parseAssums (assms : List Sexp) : ParserM (List Term) := do
  assms.mapM parseAssum

def parseCmds (cmds : List Sexp) : ParserM CCmdList := do
  let cmds ← cmds.mapM parseCmd
  return cmds.foldr CCmdList.cons CCmdList.nil

structure Query where
  decls  : List Sexp := []
  defs   : List Sexp := []
  assums : List Sexp := []
  cmds   : List Sexp := []

def partitionSexps : List Sexp → ParserM Query :=
  go {}
where
  go (query : Query) : List Sexp → ParserM Query
  | sexp!{(declare-const {x} {α})} :: ss =>
    go { query with decls := sexp!{(declare-const {x} {α})} :: query.decls } ss
  | sexp!{(define {t} () {v})} :: ss =>
    go { query with defs := sexp!{(define {t} () {v})} :: query.defs } ss
  | sexp!{(assume {s} {t})} :: ss =>
    go { query with assums := sexp!{(assume {s} {t})} :: query.assums } ss
  | sexp!{(assume-push {s} {t})} :: ss =>
    go { query with cmds := sexp!{(assume-push {s} {t})} :: query.cmds } ss
  | sexp!{(step {s} :rule {r} :premises (⦃ps⦄))} :: ss =>
    go { query with cmds := sexp!{(step {s} :rule {r} :premises (⦃ps⦄) :args ())} :: query.cmds } ss
  | sexp!{(step {s} :rule {r} :args (⦃as⦄))} :: ss =>
    go { query with cmds := sexp!{(step {s} :rule {r} :premises () :args (⦃as⦄))} :: query.cmds } ss
  | sexp!{(step {s} :rule {r} :premises (⦃ps⦄) :args (⦃as⦄))} :: ss =>
    go { query with cmds := sexp!{(step {s} :rule {r} :premises (⦃ps⦄) :args (⦃as⦄))} :: query.cmds } ss
  | sexp!{(step {s} {c} :rule {r} :premises (⦃ps⦄))} :: ss =>
    go { query with cmds := sexp!{(step {s} {c} :rule {r} :premises (⦃ps⦄) :args ())} :: query.cmds } ss
  | sexp!{(step {s} {c} :rule {r} :args (⦃as⦄))} :: ss =>
    go { query with cmds := sexp!{(step {s} {c} :rule {r} :premises () :args (⦃as⦄))} :: query.cmds } ss
  | sexp!{(step {s} {c} :rule {r} :premises (⦃ps⦄) :args (⦃as⦄))} :: ss =>
    go { query with cmds := sexp!{(step {s} {c} :rule {r} :premises (⦃ps⦄) :args (⦃as⦄))} :: query.cmds } ss
  | sexp!{(step-pop {s} :rule {r} :premises (⦃ps⦄))} :: ss =>
    go { query with cmds := sexp!{(step-pop {s} :rule {r} :premises (⦃ps⦄) :args ())} :: query.cmds } ss
  | sexp!{(step-pop {s} :rule {r} :args (⦃as⦄))} :: ss =>
    go { query with cmds := sexp!{(step-pop {s} :rule {r} :premises () :args (⦃as⦄))} :: query.cmds } ss
  | sexp!{(step-pop {s} :rule {r} :premises (⦃ps⦄) :args (⦃as⦄))} :: ss =>
    go { query with cmds := sexp!{(step-pop {s} :rule {r} :premises (⦃ps⦄) :args (⦃as⦄))} :: query.cmds } ss
  | s :: _ =>
    throw s!"Error: unrecognized command {s}, expected one of declare-const, define, assume, assume-push, step, or step-pop"
  | [] =>
    return { decls := query.decls.reverse
             defs := query.defs.reverse
             assums := query.assums.reverse
             cmds := query.cmds.reverse }

def parseProof (ss : List Sexp) : ParserM (List Term × CCmdList) := do
  let [.expr ss] := ss | throw s!"Error: expected a list of commands, got {ss}"
  let query ← partitionSexps ss
  withDecls query.decls do
  withDefs query.defs do
  let assums ← parseAssums query.assums
  let cmds ← parseCmds query.cmds
  return (assums, cmds)

end Parser

def parseProof (p : String) : Except String (List Term × CCmdList) := do
  let ss ← Sexp.Parser.manySexps!.run p
  (Parser.parseProof ss).run' {}

end Eo
