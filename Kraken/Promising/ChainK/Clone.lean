/-
**`#chaink_clone`: a selective source-level instantiation of the Stage 2
chain at the K world**. ISA-neutral;
used only by the `ChainK/*` clone modules.

`#chaink_clone "File.lean", … skip ["name", …]` reads each file (a path
relative to the directory of the current file), drops its `import` lines,
and walks it command by command:

- **Which declarations are cloned.** A command that declares something (it
  contains a `declId`) is cloned iff one of its identifiers (docstrings
  ignored) is a *trigger*: a name of the executable machine (`Path`,
  `Reachable`, `succs`, `succs_cases`, `Live`) or the name of a declaration
  cloned before (in this command or in an imported clone module); or if it
  sits in a `section`/`namespace` whose `variable` command hits a trigger.
  The `skip` list (names as written in the source) is never cloned. Bare
  occurrences of the common names `kNoTrigger` do not trigger. Other
  commands that declare something are dropped; `#` commands are dropped;
  `namespace`, `section`, `end`, `open`, `variable`, `universe`,
  `set_option`, `include`, `omit` and macro/syntax/notation commands are
  always elaborated (on
  the substituted text); any other command only if it hits a trigger.
- **Substitution.** Whole words (`substK`) are replaced:
  `kBase` (`Live.Bridge` kept, `Path ↦ PathK`, `Reachable ↦ ReachableKF`, `succs ↦ succsK`,
  `succs_cases ↦ succsK_cases`, `Live ↦ LiveKF`), the explicit `ReachableK` twins
  `kTwins` (`Reachable.x ↦ ReachableK.x`, `Config.Live.x ↦ Config.LiveK.x`),
  and the renames of cloned declarations (a rename of an undotted name is
  not applied right after a `.`).
- **Naming.** A cloned declaration whose full name the substitution already
  changes (it, or its namespace, mentions a substituted word) keeps that
  name; otherwise its last component gets the suffix `K` (`caseD2' ↦
  caseD2'K`), and the rename is applied to the rest of the source. If the
  new name is a hand-written `ReachableK` twin (`kTwinNames`), the declaration is
  not elaborated again (the rename still applies); any other clash with an
  existing constant is an error.
- **Logging.** Each command logs one `info` message listing every rename
  `old ↦ new` (full names), with counts of cloned, skipped and existing
  declarations. Renames and triggers are recorded in an environment
  extension, so a later clone module (which imports the earlier ones) sees
  them.

Nothing is assumed: every cloned declaration is elaborated and
kernel-checked as if it had been written out; only the source text is
shared. Messages carry the source file's line numbers (in the substituted
text; one `#chaink_clone` per source file keeps them unambiguous). Lake does not track the source files as inputs: a
clone module must also `import` the modules it clones.

The opt-in variant `#chaink_clone'` is described at its definition
below.
-/
import Lean
import Kraken.Promising.LiveTicketAlClone

namespace Kraken.Promising.ChainK

open Lean Elab Command

/-- An entry of the clone state: `(name as written, new name as written,
renamed?)`. Every entry's first component is a trigger; renamed entries are
applied to later sources. -/
abbrev CloneEntry := String × String × Bool

/-- The persistent clone state (renames and triggers of every clone module
imported so far). -/
initialize chainkExt : SimplePersistentEnvExtension CloneEntry (List CloneEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun l e => e :: l
    addImportedFn := fun arrs => arrs.foldl (fun acc a => a.foldl (fun acc e => e :: acc) acc) []
  }

/-- The machine's names and their K-world counterparts (`ReachableK.lean`). -/
def kBase : List (String × String) :=
  [("Live.Bridge", "Live.Bridge"), ("Path", "PathK"), ("Reachable", "ReachableKF"), ("succs_cases", "succsK_cases"), ("succs", "succsK"),
   ("Live", "LiveKF")]

/-- The trigger words of `kBase`. -/
def kTriggers : List String := ["Path", "Reachable", "succs_cases", "succs", "Live"]

/-- The hand-written fuel-free `ReachableK` twins whose names the base
substitution would get wrong (`Reachable.x ↦ ReachableK.x`, not
`ReachableKF.x`), or that live outside the cloned modules
(`configInv_reachable ↦ configInv_reachableK`); tried before `kBase`. -/
def kTwins : List (String × String) :=
  ["views_mono", "relPre_mono", "vwOldNT_mono", "vwNew_mono", "mem_prefix", "vwOldNT_armv8", "noNTInv"].map
      (fun n => (s!"Reachable.{n}", s!"ReachableK.{n}")) ++
    ["vwNew_lt", "vCAP_lt", "wfloor_lt", "wfProm", "vCAP_coh_lt"].map
      (fun n => (s!"Config.Live.{n}", s!"Config.LiveK.{n}")) ++
    [("configInv_reachable", "configInv_reachableK"), ("Config.ntFree_of_noNTInv", "Config.ntFree_of_noNTInvK")]

/-- `Live.TkClone.substWords` for the clone: the pairs of `base` apply at
every word start; the renames `ren` apply only at word starts not preceded
by `.` when their key has no `.` (so a rename `Inv ↦ InvK` of a cloned
`SLR.Inv` leaves `Ctx.Inv` and `ht.Inv` alone). -/
def substK (base ren : List (String × String)) (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let pats := base.map (fun (a, b) => (a.toList.toArray, b, false)) ++
    ren.map (fun (a, b) => (a.toList.toArray, b, !a.contains '.'))
  let mut out : String := ""
  let mut i := 0
  let mut prevWord := false
  let mut prevDot := false
  while i < cs.size do
    let mut hit : Option (Nat × String) := none
    if !prevWord then
      for (a, b, noDot) in pats do
        if hit.isNone && !(noDot && prevDot) && i + a.size ≤ cs.size &&
            (List.range a.size).all (fun j => cs[i + j]! == a[j]!) &&
            (i + a.size == cs.size || !Live.TkClone.isWordChar cs[i + a.size]!) then
          hit := some (a.size, b)
    match hit with
    | some (n, b) =>
      out := out ++ b
      i := i + n
      prevWord := true
      prevDot := false
    | none =>
      out := out.push cs[i]!
      prevWord := Live.TkClone.isWordChar cs[i]!
      prevDot := cs[i]! == '.'
      i := i + 1
  return out

/-- Hand-written `ReachableK` twins whose names are `rule(old)` of a declaration
of a cloned module: the clone does not elaborate the original again. Any
other clash of a new name with an existing constant is an error. -/
def kTwinNames : List Name :=
  [`Kraken.Promising.Config.Bnd.succK, `Kraken.Promising.Config.ntFree_armv8K]

/-- Cloned names that are also common field names (`ThreadRuleRX.Inv`, …):
a bare occurrence does not make a command a clone (it is still renamed in a
command cloned for another reason). -/
def kNoTrigger : List String :=
  ["Inv", "Inv'", "Status", "Status'", "Valid", "valid", "refl", "trans", "X", "Post", "conclude",
   "conclude'"]

/-- Names declared by a command (its `declId`s). -/
partial def declIds (stx : Syntax) : Array Name :=
  if stx.isOfKind ``Lean.Parser.Command.declId then #[stx[0].getId]
  else stx.getArgs.foldl (fun acc s => acc ++ declIds s) #[]

/-- Identifier words of a command (full identifiers and their components;
docstrings and `Live.Bridge` names skipped). -/
partial def identWords (stx : Syntax) (acc : Array String := #[]) : Array String :=
  if stx.isOfKind ``Lean.Parser.Command.docComment then acc
  else match stx with
    | .ident _ _ n _ =>
      -- `Live.Bridge.ReachableK…` is the K world already (hand-written twins)
      if (n.toString.splitOn "Live.Bridge").length > 1 then acc
      else (acc.push n.toString) ++ n.components.toArray.map toString
    | .node _ _ args => args.foldl (fun a s => identWords s a) acc
    | _ => acc

/-- Commands that are elaborated whether or not they hit a trigger. -/
def alwaysKinds : List Name :=
  [``Lean.Parser.Command.namespace, ``Lean.Parser.Command.section, ``Lean.Parser.Command.end,
   ``Lean.Parser.Command.open, ``Lean.Parser.Command.variable, ``Lean.Parser.Command.universe,
   ``Lean.Parser.Command.set_option, ``Lean.Parser.Command.include, ``Lean.Parser.Command.omit]

/-- Macro, syntax and notation commands (needed by the cloned proofs). -/
def isMacroLike (k : Name) : Bool :=
  let s := k.toString
  (s.splitOn "macro").length > 1 || (s.splitOn "syntax").length > 1 || (s.splitOn "notation").length > 1 ||
    (s.splitOn "elab").length > 1

/-- The name `n` with the suffix `K` on its last component. -/
def addK (n : Name) : Name :=
  match n with
  | .str p s => .str p (s ++ "K")
  | _ => n

/-- The components of a name written in a `namespace` command. -/
def nsName (stx : Syntax) : Name :=
  stx[1].getId

/-- Clone the triggered declarations of `src`. -/
def cloneSource (fileName src : String) (skip : List String) (log : IO.Ref (Array String))
    (counts : IO.Ref (Nat × Nat × Nat)) : CommandElabM Unit := do
  let inputCtx := Parser.mkInputContext src fileName
  let mut mps : Parser.ModuleParserState := {}
  -- one entry per open `namespace`/`section`: (original namespace, variables hit a trigger)
  let mut stack : List (Name × Bool) := [((← getScope).currNamespace, false)]
  repeat
    let scope ← getScope
    let pmctx : Parser.ParserModuleContext :=
      { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls }
    let pos0 := mps.pos
    let (stx, mps', msgs) := Parser.parseCommand inputCtx pmctx mps {}
    mps := mps'
    for m in msgs.toList do logMessage m
    if Parser.isTerminalCommand stx then break
    let txt := String.Pos.Raw.extract src pos0 mps.pos
    if (String.ofList (txt.toList.dropWhile Char.isWhitespace)).startsWith "#" then continue
    let line := (inputCtx.fileMap.toPosition pos0).line
    let entries := chainkExt.getState (← getEnv)
    let ren := entries.filterMap fun (a, b, r) => if r then some (a, b) else none
    let hit := (identWords stx).any fun w =>
      kTriggers.contains w || (!kNoTrigger.contains w && entries.any (·.1 == w))
    let k := stx.getKind
    let (origNs, secHit) := stack.head!
    if k == ``Lean.Parser.Command.namespace then
      stack := (origNs ++ nsName stx, secHit) :: stack
    else if k == ``Lean.Parser.Command.section then
      stack := (origNs, secHit) :: stack
    else if k == ``Lean.Parser.Command.end then
      stack := match stack.tail with
        | [] => stack
        | s => s
    else if k == ``Lean.Parser.Command.variable && hit then
      stack := (origNs, true) :: stack.tail
    let ids := declIds stx
    let mut newRen : List (String × String) := []
    if ids.size > 0 then
      if !(hit || secHit) || ids.any (fun n => skip.contains n.toString) then
        counts.modify fun (c, s, e) => (c, s + 1, e)
        continue
      let mut exists_ := false
      for n in ids do
        let s := n.toString
        let s' := substK (kTwins ++ kBase) ren s
        let newNs := (← getScope).currNamespace
        let cand := newNs ++ s'.toName
        let (newS, newFull) :=
          if cand == origNs ++ n then ((addK n).toString, newNs ++ addK n) else (s', cand)
        if newS != s' then newRen := newRen ++ [(s, newS)]
        if (← getEnv).contains newFull then
          if kTwinNames.contains newFull then exists_ := true
          else logError m!"chaink_clone: new name {newFull} (for {origNs ++ n}) already exists"
        modifyEnv fun env => chainkExt.addEntry env (s, newS, newS != s')
        log.modify (·.push s!"{origNs ++ n} ↦ {newFull}")
      if exists_ then
        counts.modify fun (c, s, e) => (c, s, e + 1)
        continue
      counts.modify fun (c, s, e) => (c + 1, s, e)
    else if !(alwaysKinds.contains k || isMacroLike k || hit) then
      continue
    -- padded so that positions in messages are the source file's lines
    let txt' := String.ofList (List.replicate (line - 1) '\n') ++
      substK (kTwins ++ kBase) (newRen ++ ren) txt
    let name := s!"{fileName}:{line}"
    let ictx := Parser.mkInputContext txt' name
    let (stx', _, msgs') := Parser.parseCommand ictx pmctx {} {}
    for m in msgs'.toList do logMessage m
    withReader (fun ctx => { ctx with fileName := name, fileMap := ictx.fileMap }) <|
      withRef stx' <| elabCommand stx'

/-- `#chaink_clone` on a list of files with a skip list. -/
def cloneFiles (files skip : List String) : CommandElabM Unit := do
  let here ← getFileName
  let dir := (System.FilePath.mk here).parent.getD "."
  let log ← IO.mkRef (#[] : Array String)
  let counts ← IO.mkRef ((0, 0, 0) : Nat × Nat × Nat)
  for file in files do
    let src ← IO.FS.readFile (dir / file)
    cloneSource (file ++ "[chaink]") (Live.TkClone.dropImports src) skip log counts
  let (c, s, e) ← counts.get
  let l ← log.get
  logInfo m!"chaink_clone: cloned {c}, skipped {s}, existing twins {e}; renames ({l.size}):\n{"\n".intercalate l.toList}"

syntax (name := chainkCloneCmd) "#chaink_clone " str,* (" skip " "[" str,* "]")? : command

@[command_elab chainkCloneCmd] def elabChainkClone : CommandElab := fun stx => do
  match stx with
  | `(#chaink_clone $fs:str,*) => cloneFiles (fs.getElems.toList.map (·.getString)) []
  | `(#chaink_clone $fs:str,* skip [$ss:str,*]) =>
    cloneFiles (fs.getElems.toList.map (·.getString)) (ss.getElems.toList.map (·.getString))
  | _ => throwUnsupportedSyntax

/-!
### `#chaink_clone'`: the opt-in variant 

`#chaink_clone' "File.lean", … skip [...] only [...] keep_names [...]` (each
list optional) is `#chaink_clone` with the following changes. It is used by
the `SLR/ChainK/Twins*` clone modules. `#chaink_clone` itself is unchanged.

- **`only [n, …]`.** A declaration is cloned only if one of its names (as
  written in the source) is listed, and it is still subject to the trigger
  rule and to `skip`. A listed name that the walk never clones is an error.
- **`keep_names [n, …]`.** The renames and triggers of earlier clone modules
  whose old name is listed are ignored. Use it for a source whose own
  declaration shares a name with a cloned one (a local `Inv`). Renames made
  by this command still apply.
- **Local attributes.** An `attribute` command that contains `local` or
  `scoped` is always elaborated (on the substituted text), like `open`.
- **Qualified renames.** For a rename `x ↦ xK` of an undotted name, a
  qualified occurrence `Q.x` in a command (`SLR.x`, `Kraken.Promising.SLR.x`)
  is renamed to `Q.xK` when `P.Q.xK` exists, where `P` is a prefix of the
  current namespace or an `open`ed namespace.
- **`hoist_alias`.** In a cloned `hoist_alias [o ↦ n, …]`, a pair whose `o`
  is renamed gets the new name `n` with the suffix `K` on its last component.
  This rename applies to the rest of the source and to later clone modules.
-/

/-- The options of `#chaink_clone'`. -/
structure CloneOpts where
  /-- Declarations never cloned (names as written). -/
  skips : List String := []
  /-- If given, the only declarations cloned (names as written). -/
  onlys : Option (List String) := none
  /-- Old names whose imported renames and triggers are ignored. -/
  keeps : List String := []

/-- The identifiers of a command (docstrings skipped). -/
partial def identNames (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  if stx.isOfKind ``Lean.Parser.Command.docComment then acc
  else match stx with
    | .ident _ _ n _ => acc.push n
    | .node _ _ args => args.foldl (fun a s => identNames s a) acc
    | _ => acc

/-- The qualified forms `Q.x ↦ Q.xK` of the undotted renames `keys` (`x ↦ xK`)
that occur in the identifiers `ids` of a command: `Q.x` is a run of
components of an identifier, with `Q` nonempty, such that `P ++ Q.xK` exists
for a namespace `P` in `nss`. -/
def qualPairs (env : Environment) (nss : List Name) (keys : Std.HashSet String)
    (ids : Array Name) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  for n in ids do
    let cs := n.components.map toString
    for j in [1:cs.length] do
      let x := cs[j]!
      if keys.contains x then
        for i in [0:j] do
          let q := ".".intercalate ((cs.drop i).take (j - i))
          let qx := q ++ "." ++ x
          let qxK := q.toName ++ (x ++ "K").toName
          if !out.any (·.1 == qx) && nss.any (fun p => env.contains (p ++ qxK)) then
            out := (qx, qx ++ "K") :: out
  return out

/-- The namespaces tried by `qualPairs`: the prefixes of the current
namespace (the root included) and the `open`ed namespaces. -/
def qualNamespaces (scope : Scope) : List Name :=
  let rec prefixes : Name → List Name
    | .anonymous => [.anonymous]
    | n@(.str p _) => n :: prefixes p
    | n@(.num p _) => n :: prefixes p
  prefixes scope.currNamespace ++ scope.openDecls.filterMap fun
    | .simple ns _ => some ns
    | _ => none

/-- The `hoist_alias` command kind (`SLR/EnvG/Alias.lean`, not imported). -/
def hoistAliasKind : Name := `Kraken.Promising.SLR.EnvG.Alias.hoistAlias

/-- `cloneSource` with the options of `#chaink_clone'`. `n0` is the number
of clone entries before the command (for `keep_names`); `seen` collects the
cloned names (for `only`). -/
def cloneSource' (fileName src : String) (opts : CloneOpts) (n0 : Nat)
    (seen : IO.Ref (List String)) (log : IO.Ref (Array String))
    (counts : IO.Ref (Nat × Nat × Nat)) : CommandElabM Unit := do
  let inputCtx := Parser.mkInputContext src fileName
  let mut mps : Parser.ModuleParserState := {}
  -- one entry per open `namespace`/`section`: (original namespace, variables hit a trigger)
  let mut stack : List (Name × Bool) := [((← getScope).currNamespace, false)]
  repeat
    let scope ← getScope
    let pmctx : Parser.ParserModuleContext :=
      { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls }
    let pos0 := mps.pos
    let (stx, mps', msgs) := Parser.parseCommand inputCtx pmctx mps {}
    mps := mps'
    for m in msgs.toList do logMessage m
    if Parser.isTerminalCommand stx then break
    let txt := String.Pos.Raw.extract src pos0 mps.pos
    if (String.ofList (txt.toList.dropWhile Char.isWhitespace)).startsWith "#" then continue
    let line := (inputCtx.fileMap.toPosition pos0).line
    let all := chainkExt.getState (← getEnv)
    let nNew := all.length - n0
    let entries := all.take nNew ++ (all.drop nNew).filter (fun e => !opts.keeps.contains e.1)
    let ren0 := entries.filterMap fun (a, b, r) => if r then some (a, b) else none
    let keys : Std.HashSet String := ren0.foldl
      (fun s (a, b) => if !a.contains '.' && b == a ++ "K" then s.insert a else s) {}
    let ren := ren0 ++ qualPairs (← getEnv) (qualNamespaces scope) keys (identNames stx)
    let hit := (identWords stx).any fun w =>
      kTriggers.contains w || (!kNoTrigger.contains w && entries.any (·.1 == w))
    let k := stx.getKind
    let (origNs, secHit) := stack.head!
    if k == ``Lean.Parser.Command.namespace then
      stack := (origNs ++ nsName stx, secHit) :: stack
    else if k == ``Lean.Parser.Command.section then
      stack := (origNs, secHit) :: stack
    else if k == ``Lean.Parser.Command.end then
      stack := match stack.tail with
        | [] => stack
        | s => s
    else if k == ``Lean.Parser.Command.variable && hit then
      stack := (origNs, true) :: stack.tail
    let ids := declIds stx
    let mut newRen : List (String × String) := []
    if ids.size > 0 then
      if !(hit || secHit) || ids.any (fun n => opts.skips.contains n.toString) ||
          opts.onlys.any (fun l => !ids.any (fun n => l.contains n.toString)) then
        counts.modify fun (c, s, e) => (c, s + 1, e)
        continue
      let mut exists_ := false
      for n in ids do
        let s := n.toString
        seen.modify (s :: ·)
        let s' := substK (kTwins ++ kBase) ren s
        let newNs := (← getScope).currNamespace
        let cand := newNs ++ s'.toName
        let (newS, newFull) :=
          if cand == origNs ++ n then ((addK n).toString, newNs ++ addK n) else (s', cand)
        if newS != s' then newRen := newRen ++ [(s, newS)]
        if (← getEnv).contains newFull then
          if kTwinNames.contains newFull then exists_ := true
          else logError m!"chaink_clone: new name {newFull} (for {origNs ++ n}) already exists"
        modifyEnv fun env => chainkExt.addEntry env (s, newS, newS != s')
        log.modify (·.push s!"{origNs ++ n} ↦ {newFull}")
      if exists_ then
        counts.modify fun (c, s, e) => (c, s, e + 1)
        continue
      counts.modify fun (c, s, e) => (c + 1, s, e)
    else if k == hoistAliasKind && hit then
      for p in stx[2].getSepArgs do
        let o := p[0].getId
        let n := p[2].getId
        if substK (kTwins ++ kBase) ren o.toString != o.toString then
          let n' := addK n
          newRen := newRen ++ [(n.toString, n'.toString)]
          if (← getEnv).contains n' then
            logError m!"chaink_clone: new name {n'} (for {n}) already exists"
          if let (.str _ a, .str _ b) := (n, n') then
            modifyEnv fun env => chainkExt.addEntry env (a, b, true)
          log.modify (·.push s!"{n} ↦ {n'}")
          counts.modify fun (c, s, e) => (c + 1, s, e)
    else if !(alwaysKinds.contains k || isMacroLike k || hit ||
        (k == ``Lean.Parser.Command.attribute &&
          ((txt.splitOn "local").length > 1 || (txt.splitOn "scoped").length > 1))) then
      continue
    -- padded so that positions in messages are the source file's lines
    let txt' := String.ofList (List.replicate (line - 1) '\n') ++
      substK (kTwins ++ kBase) (newRen ++ ren) txt
    let name := s!"{fileName}:{line}"
    let ictx := Parser.mkInputContext txt' name
    let (stx', _, msgs') := Parser.parseCommand ictx pmctx {} {}
    for m in msgs'.toList do logMessage m
    withReader (fun ctx => { ctx with fileName := name, fileMap := ictx.fileMap }) <|
      withRef stx' <| elabCommand stx'

/-- `#chaink_clone'` on a list of files. -/
def cloneFiles' (files : List String) (opts : CloneOpts) : CommandElabM Unit := do
  let here ← getFileName
  let dir := (System.FilePath.mk here).parent.getD "."
  let log ← IO.mkRef (#[] : Array String)
  let counts ← IO.mkRef ((0, 0, 0) : Nat × Nat × Nat)
  let seen ← IO.mkRef ([] : List String)
  let n0 := (chainkExt.getState (← getEnv)).length
  for file in files do
    let src ← IO.FS.readFile (dir / file)
    cloneSource' (file ++ "[chaink]") (Live.TkClone.dropImports src) opts n0 seen log counts
  if let some l := opts.onlys then
    let s ← seen.get
    for n in l do
      unless s.contains n do logError m!"chaink_clone': `only` name {n} was not cloned"
  let (c, s, e) ← counts.get
  let l ← log.get
  logInfo m!"chaink_clone: cloned {c}, skipped {s}, existing twins {e}; renames ({l.size}):\n{"\n".intercalate l.toList}"

syntax (name := chainkClonePCmd) "#chaink_clone' " str,* (" skip " "[" str,* "]")?
  (" only " "[" str,* "]")? (" keep_names " "[" str,* "]")? : command

/-- The strings of an optional `kw [s, …]` clause, if present. -/
def optStrs (stx : Syntax) : Option (List String) :=
  if stx.getNumArgs == 0 then none
  else some (stx[2].getSepArgs.toList.filterMap (·.isStrLit?))

@[command_elab chainkClonePCmd] def elabChainkCloneP : CommandElab := fun stx => do
  let files := stx[1].getSepArgs.toList.filterMap (·.isStrLit?)
  cloneFiles' files
    { skips := (optStrs stx[2]).getD [], onlys := optStrs stx[3], keeps := (optStrs stx[4]).getD [] }

end Kraken.Promising.ChainK
