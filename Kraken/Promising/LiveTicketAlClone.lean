/-
**Re-elaborating an existing module's source with identifiers substituted**
The tool that instantiates the `ldadda` ticket lock
proofs (`LiveTicket*.lean`, worker `tkWorker`) at the `ldaddal` worker
`tkWorkerAl`, which differs from `tkWorker` in exactly one cell.

`#tk_clone "File.lean" with ["a" => "b", …]` reads `File.lean` (a path
relative to the directory of the current file), drops its `import` lines,
replaces every whole-word occurrence of each `a` by `b` (one pass, first
match wins; a word boundary is any character that is not ASCII alphanumeric,
`_`, `'`, `!` or `?`), and elaborates the result command by command in the
current module. Nothing is assumed: every cloned declaration is elaborated
and kernel-checked as if it had been written out; only the source text is
shared. Messages carry positions in the substituted text under the name
`File.lean[clone]`.

Lake does not track the source file as an input; a clone module should also
`import` the cloned module (so a change to it rebuilds the clone), and a script
that lists `include_str` dependencies should list this command too.
-/
import Lean

namespace Kraken.Promising.Live.TkClone

open Lean Elab Command

/-- Characters that continue an identifier (for whole-word matching). -/
def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

/-- Replace every whole-word occurrence of each `from` by its `to` (one
left-to-right pass; at each position the first matching pair wins). -/
def substWords (subst : List (String × String)) (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let pats := subst.map fun (a, b) => (a.toList.toArray, b)
  let mut out : String := ""
  let mut i := 0
  let mut prevWord := false
  while i < cs.size do
    let mut hit : Option (Nat × String) := none
    if !prevWord then
      for (a, b) in pats do
        if hit.isNone && i + a.size ≤ cs.size && (List.range a.size).all (fun j => cs[i + j]! == a[j]!) &&
            (i + a.size == cs.size || !isWordChar cs[i + a.size]!) then
          hit := some (a.size, b)
    match hit with
    | some (n, b) =>
      out := out ++ b
      i := i + n
      prevWord := true
    | none =>
      out := out.push cs[i]!
      prevWord := isWordChar cs[i]!
      i := i + 1
  return out

/-- Drop the `import` lines of a module source. -/
def dropImports (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").map fun l => if l.startsWith "import " then "" else l)

/-- Elaborate `src` command by command in the current module. -/
def elabSource (fileName src : String) : CommandElabM Unit := do
  let inputCtx := Parser.mkInputContext src fileName
  let mut mps : Parser.ModuleParserState := {}
  repeat
    let scope ← getScope
    let pmctx : Parser.ParserModuleContext :=
      { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls }
    let (stx, mps', msgs) := Parser.parseCommand inputCtx pmctx mps {}
    mps := mps'
    for m in msgs.toList do logMessage m
    if Parser.isTerminalCommand stx then break
    withReader (fun ctx => { ctx with fileName, fileMap := inputCtx.fileMap }) <|
      withRef stx <| elabCommand stx

/-- **The `ldadda` → `ldaddal` substitution** used by every `LiveTicketAl*`
clone: the worker and its start structure, the ticket RMW's tree and kind,
the cloned namespaces (`Live.TicketX` → `Live.TicketAlX`), the statement
names of `LiveTicket.lean` (→ `LiveTicketAl.lean`) and the theorem names. -/
def ticketAlSubst : List (String × String) :=
  [("tkWorker", "tkWorkerAl"), ("StartState", "StartStateAl"), ("exec_ldadda", "exec_ldaddal"),
   (".rmw .acq", ".rmw .acqRel"),
   ("TicketTrees", "TicketAlTrees"), ("TicketInv", "TicketAlInv"), ("TicketInvP", "TicketAlInvP"),
   ("TicketDrop", "TicketAlDrop"), ("TicketSolo", "TicketAlSolo"), ("TicketPF", "TicketAlPF"),
   ("TicketSem", "TicketAlSem"), ("Ticket", "TicketAl"),
   ("TkStart", "TkStartAl"), ("TkWaiting", "TkWaitingAl"), ("TkDone", "TkDoneAl"),
   ("TicketLiveUnder", "TicketAlLiveUnder"), ("TicketLivePF", "TicketAlLivePF"),
   ("TicketLiveWF", "TicketAlLiveWF"), ("TicketLive", "TicketAlLive"), ("TicketLiveSem", "TicketAlLiveSem"),
   ("ticket_live_pf", "ticket_al_live_pf"), ("ticket_live_pf_concrete", "ticket_al_live_pf_concrete"),
   ("ticket_live_sem", "ticket_al_live_sem"), ("ticket_live_sem_concrete", "ticket_al_live_sem_concrete")]

/-- Clone `file` (relative to the current file's directory) under `subst`. -/
def cloneFile (file : String) (subst : List (String × String)) : CommandElabM Unit := do
  let here ← getFileName
  let dir := (System.FilePath.mk here).parent.getD "."
  let src ← IO.FS.readFile (dir / file)
  elabSource (file ++ "[clone]") (substWords subst (dropImports src))

syntax (name := tkCloneCmd) "#tk_clone " str " with " "[" (str " => " str),* "]" : command

@[command_elab tkCloneCmd] def elabTkClone : CommandElab := fun stx => do
  match stx with
  | `(#tk_clone $file:str with [$[$as:str => $bs:str],*]) =>
    cloneFile file.getString ((as.zip bs).toList.map fun (a, b) => (a.getString, b.getString))
  | _ => throwUnsupportedSyntax

/-- `#ticket_al_clone "File.lean"` (optionally `with [extra pairs]`, tried
first): `#tk_clone` under `ticketAlSubst`. -/
syntax (name := ticketAlCloneCmd) "#ticket_al_clone " str (" with " "[" (str " => " str),* "]")? : command

@[command_elab ticketAlCloneCmd] def elabTicketAlClone : CommandElab := fun stx => do
  match stx with
  | `(#ticket_al_clone $file:str) => cloneFile file.getString ticketAlSubst
  | `(#ticket_al_clone $file:str with [$[$as:str => $bs:str],*]) =>
    cloneFile file.getString
      ((as.zip bs).toList.map (fun (a, b) => (a.getString, b.getString)) ++ ticketAlSubst)
  | _ => throwUnsupportedSyntax

end Kraken.Promising.Live.TkClone
