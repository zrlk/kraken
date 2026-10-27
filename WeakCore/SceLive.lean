/-
# SceLive — `sce`'s live stage, mode A

A scenario (a `scenario S` item, or `--threads`) is run exactly as cldoc's `threads=` runs it: the setup block to
completion (`TermSmoke.runSetup`), then every interleaving of the threads from `TermSmoke.spawn` with the setup's
results prepended to each thread's arguments, kept as a graph (`TermLive.exploreG`, `Knobs.all`, `.arm`,
`maxP := promises`, `depth`, the crash moves) and analysed (`TermLive.analyse`).  These are the functions
`Doc.threads` calls, with the same arguments; nothing is copied, and `SceTest` checks the verdict and the
configuration count against `Doc.threads`' own status line.  The start is the scenario start, never `main`.

The report is plain text: the status line (cldoc's words), the verdict (`Live.describe`), each thread's results,
the final-state table (`--final`/`--watch`), and for each kind of livelock one class, every thread placed in the
source: its current core term is a subterm of an elaborated block (the machine runs the block's own terms in an
environment), found by structural equality, and the parser's span table gives its UnElab range (`UDiag.spanOf`).
Nothing here is trusted: a misplaced thread misplaces a line of the report, never a verdict.

`reps` recomputes `analyse`'s classes keeping one configuration per class (for the rendering only); the run
compares its classes with `analyse`'s and renders nothing when they differ.
-/
import WeakCore.SceText
import WeakCore.UDiag
import WeakCore.Doc

namespace SceLive
open CoreLang CoreTerm Syntax UnElab USyntax UDiag TermRun TermLive TermSmoke

/-- A scenario, resolved to blocks; a type `none` is the block's own argument type. -/
structure Spec where
  name     : String
  f        : String
  argTy    : Option Ty := none
  args     : List Nat := []
  thr      : List (String × Option Ty × List Nat) := []
  promises : Nat := 0
  depth    : Nat := 300
  crash    : Option Nat := none
  live     : Option Nat := none
  final    : Option (List (List Nat)) := none
  watch    : List (String × Nat × Nat) := []
  /-- `cert = N`: also produce and check a liveness certificate of at most `N` configurations (item 38) -/
  cert     : Option Nat := none
  deriving Inhabited

/-- What the renderer needs: per unit with an implementation, its file, blocks, spans; and the sources. -/
structure Ctx where
  prog  : Prog
  units : List (String × Prog × List Span)
  src   : String → String

structure LOut where
  report : List String := []
  errs   : List String := []
  /-- a thread entry whose argument type is outside `TermSpawn.KidOK`'s shapes (`kidOf`): no scenario instance -/
  noKid  : Option (String × Ty) := none
  /-- the scenario ran (its setup completed): the setup's argument type and the resolved threads (`SceCert`) -/
  ran    : Option (Ty × List (String × Ty × List Nat)) := none
  deriving Inhabited, BEq, Repr

/-! ## Values, plainly -/

def showVal : WeakMem.Val → String
  | .num n => toString n
  | .null => "null"
  | .undef => "undef"
  | .loc a t => "ℓ" ++ toString a.label ++ (if a.offset == 0 then "" else "+" ++ toString a.offset) ++
                (if t == 0 then "" else "^" ++ toString t)

def showVals : List WeakMem.Val → String
  | [] => "()"
  | [v] => showVal v
  | vs => "(" ++ ", ".intercalate (vs.map showVal) ++ ")"

def commas (xs : List Nat) : String := ", ".intercalate (xs.map toString)

/-! ## Classes with a representative (rendering only) -/

/-- `analyse`'s terminal classes with a thread step inside, each with one of its configurations. -/
def reps (g : Graph) : List (Livelock × Cfg) := Id.run do
  let n := g.nodes.size
  let comp := sccs (g.edges.map fun es => es.filterMap fun (_, t, d) => if t then some d else none)
  let ncomp := comp.foldl max 0 + 1
  let mut closed : Array Bool := Array.replicate ncomp true
  let mut inside : Array (List Nat) := Array.replicate ncomp []
  let mut members : Array (List Nat) := Array.replicate ncomp []
  for v in [0:n] do
    let c := comp[v]!
    members := members.set! c (v :: members[c]!)
    for (i, t, d) in g.edges[v]! do
      if t then
        if comp[d]! == c then inside := inside.set! c (i :: inside[c]!)
        else closed := closed.set! c false
  let mut out : List (Livelock × Cfg) := []
  for c in [0:ncomp] do
    if !closed[c]! then continue
    match members[c]!, inside[c]! with
    | v :: _, ins@(_ :: _) =>
        let cfg := g.nodes[v]!
        let ths := List.range cfg.ths.size
        let stepping := ths.filter ins.contains
        let done := ths.filter fun i => (cfg.ths[i]?.map isDone).getD false
        let blocked := ths.filter fun i => !stepping.contains i && !done.contains i
        let promised := cfg.ths.any fun th => !th.promises.isEmpty
        out := (⟨(members[c]!).length, stepping, done, blocked, promised⟩, cfg) :: out
    | _, _ => pure ()
  return out.reverse

/-! ## Placing a thread -/

/-- The path of `t` inside `e` (children in `UDiag.kids` order, as the span table's paths). -/
partial def findPath (t : Expr) (e : Expr) (path : List Nat := []) : Option (List Nat) :=
  if e == t then some path
  else (UDiag.kids e).zipIdx.findSome? fun (c, i) => findPath t c (path ++ [i])

/-- The source place of a thread's current term: file, block, range. -/
def place (cx : Ctx) (t : Expr) : Option (String × String × Rng) :=
  cx.units.findSome? fun (file, own, sp) =>
    own.findSome? fun d =>
      (findPath t d.body).bind fun path => (spanOf sp d.name path).map fun s => (file, d.name, Rng.ofSpan s)

def renderThread (cx : Ctx) (ll : Livelock) (cfg : Cfg) (i : Nat) : List String :=
  -- an outstanding promise is in the verdict (`Live.describe`), not in the tag
  let tag := if ll.stepping.contains i then SceText.tagSpins else if ll.done.contains i then SceText.tagFinished
    else SceText.tagBlocked
  match cfg.ths[i]? >>= fun th => place cx th.term with
  | some (file, _, r) =>
      let lines := ((cx.src file).splitOn "\n").toArray
      let w := (toString r.line).length
      ("  " ++ SceText.liveThreadAt i tag s!"{file}:{r.line}:{r.col}") :: (excerpt lines w r).map ("   " ++ ·)
  | none => ["  " ++ SceText.liveThread i tag]

/-! ## The run -/

/-- Space-aligned rows: each column left-aligned to its widest cell (header included), one space between columns,
no trailing spaces. -/
def alignRows (rows : List (List String)) : List String :=
  let n := rows.foldl (fun m r => max m r.length) 0
  let w := (List.range n).map fun j => rows.foldl (fun m r => max m ((r[j]?.getD "").length)) 0
  rows.map fun r =>
    " ".intercalate ((r.zip w).zipIdx.map fun ((c, k), j) =>
      if j + 1 == r.length then c else c ++ String.ofList (List.replicate (k - c.length) ' '))

#guard alignRows [["spin", "setter", "c"], ["0", "()", "1"]] == ["spin setter c", "0    ()     1"]
#guard alignRows [["a", "bb"], ["ccc", "d"]] == ["a   bb", "ccc d"]


def resolveTy (p : Prog) (g : String) (t : Option Ty) : Option Ty :=
  match t with
  | some t => some t
  | none => (p.find? (·.name == g)).map (·.argTy)

/-- A scenario thread as a spawned kid (`TermSpawn.Kid`), in one of `TermSpawn.KidOK`'s shapes for the setup's
result type `rt`: the argument is the result itself (no literals), a pair of the result and the literals, or the
literals alone (a result of no words).  `none`: none of these (the search still runs; there is no scenario
instance). -/
def kidOf (rt : Ty) (g : String) (t : Ty) (xs : List Nat) : Option TermSpawn.Kid :=
  let k (useRes : Bool) (vals : List Nat) : TermSpawn.Kid :=
    { f := g, ts := [], ty := t, useRes, vals := vals.map fun n => .num n }
  let alone := if rt.words == some 0 then some (k false xs) else none
  if xs.isEmpty && t == rt then some (k true [])
  else match t with
    | .prod a _ => if a == rt then some (k true xs) else alone
    | _ => alone

#guard (kidOf .int "g" .int []).map (·.useRes) == some true
#guard (kidOf .int "g" (.prod .int .int) [1]).map (·.useRes) == some true
#guard (kidOf .unit "g" .int [1]).map (·.useRes) == some false
#guard (kidOf .int "g" (.prod .int .int) []).isNone == false
#guard (kidOf (.prod .int .int) "g" (.prod .int (.prod .int .int)) [3]).isNone == true

/-- The kids of a scenario (the search and the scenario instance use the same list) and the first thread outside
the shapes.  Such a thread still runs, as the plain kid (`Doc.kidsOf`'s; the same argument words). -/
def kidsFor (rt : Ty) (thr : List (String × Ty × List Nat)) : List TermSpawn.Kid × Option (String × Ty) :=
  let plain (g : String) (t : Ty) (xs : List Nat) : TermSpawn.Kid :=
    { f := g, ts := [], ty := t, useRes := true, vals := xs.map fun n => .num n }
  (thr.map fun (g, t, xs) => (kidOf rt g t xs).getD (plain g t xs),
   (thr.find? fun (g, t, xs) => (kidOf rt g t xs).isNone).map fun (g, t, _) => (g, t))

/-- The kids of scenario `sp` for its instance (`kidsFor`, with the thread types resolved as `runSpec` does), or
`none` if a block it names is missing (the search reports that). -/
def scenKids (cx : Ctx) (sp : Spec) : Option (List TermSpawn.Kid × Option (String × Ty)) := do
  let p := cx.prog
  let d ← p.find? (·.name == sp.f)
  let thr ← sp.thr.mapM fun (g, t, xs) => (resolveTy p g t).map fun t => (g, t, xs)
  pure (kidsFor d.retTy thr)

/-- `runSpec` once the blocks and the setup's arity are checked. -/
def runSpecT (cx : Ctx) (sp : Spec) (strict : Bool) (argTy : Ty) (thr : List (String × Ty × List Nat)) : LOut :=
  let p := cx.prog
  let start := SceText.liveStart sp.name sp.f (commas sp.args)
    (thr.map fun (g, _, xs) => g ++ "(" ++ commas xs ++ ")")
  match runSetupCfg p sp.f [] argTy (sp.args.map fun n => cst (.num n)) sp.depth with
  | none => { report := [start], errs := [SceText.liveSetup sp.f] }
  | some (fin, res) =>
    let bad := thr.filterMap fun (g, t, xs) => t.words.bind fun m =>
      if m == res.length + xs.length then none else some (g, xs.length, m - res.length)
    if let some (g, k, m) := bad.head? then { report := [start], errs := [SceText.liveArity g k m] } else
    let rt := ((p.find? (·.name == sp.f)).map (·.retTy)).getD .unit
    let (kids, noKid) := kidsFor rt thr
    -- the real spawn: the scenario start of the liveness theorems (`TermLiveL3.ScenarioStartK`)
    let g := exploreG p Promises.Knobs.all WeakMem.Arch.arm { maxP := sp.promises } sp.depth
      (TermSpawn.spawnS fin res kids)
      (fun d => match sp.crash with | some i => (crashCfg d i).toList | none => [])
    let l := analyse g
    let ex := g.toExplored
    let reasons := g.why.reasons
    let status := SceText.liveStatus (if sp.promises > 0 then SceText.scopePromises sp.promises else SceText.scopeFree)
      ex.seen (if ex.cut then some reasons else none)
    let results := thr.zipIdx.map fun ((gname, _, xs), i) =>
      SceText.liveResults i gname (commas xs) ((resultsOf (some ex) i).map showVals)
    let fins := Doc.finalOutcomes ex thr.length sp.watch
    let cells : List (List String) := (thr.map (·.1) ++ sp.watch.map (·.1)) ::
      fins.map fun (rs, ms) => rs.map (fun r => (r.map showVals).getD "-") ++ ms.map fun m => (m.map showVal).getD "-"
    let table := if sp.watch.isEmpty && sp.final.isNone then [] else
      SceText.finalsHead fins.length :: (alignRows cells).map ("  " ++ ·)
    let rs := reps g
    let kinds := if rs.map (·.1) == l.livelocks then
        (l.kinds.zipIdx).flatMap fun ((k, cnt, sizes), j) =>
          match rs.find? (fun (ll, _) => { ll with size := 0 } == k) with
          | some (ll, cfg) => SceText.liveKind (j + 1) cnt sizes ::
              (List.range cfg.ths.size).flatMap (renderThread cx ll cfg)
          | none => []
      else []
    let found := l.livelocks.length + l.stuck
    let errs := (match sp.live with
        | some n => if found == n then [] else [SceText.liveExpected n found]
        | none => []) ++
      (if strict && ex.cut then [SceText.liveStrict reasons] else []) ++
      (match sp.final with
        | none => []
        | some es =>
          let got := fins.map (Doc.finalNums · sp.crash)
          let want := es.map some
          if got.all want.contains && want.all got.contains then []
          else [SceText.liveFinal ("[" ++ ", ".intercalate (got.map fun | some l => toString l | none => "?") ++ "]")
            (toString es)])
    { report := [start, "  " ++ status, "  " ++ SceText.liveVerdict l.describe] ++ results.map ("  " ++ ·) ++
        table.map ("  " ++ ·) ++ kinds.map ("  " ++ ·),
      errs, noKid, ran := some (argTy, thr) }

/-- Run one scenario on the elaborated program `cx.prog`.  `strict`: a cut search fails. -/
def runSpec (cx : Ctx) (sp : Spec) (strict : Bool) : LOut :=
  let p := cx.prog
  let missing := (sp.f :: sp.thr.map (·.1)).filter fun g => !(p.any (·.name == g))
  if let some g := missing.head? then { errs := [SceText.liveNoBlock sp.name g] } else
  let affine := sp.thr.filterMap fun (g, _, _) =>
    (p.find? (·.name == g)).bind fun d => if Ty.affine d.retTy then some (g, d.retTy) else none
  if let some (g, t) := affine.head? then { errs := [SceText.liveAffine g (showType t)] } else
  let argTy := (resolveTy p sp.f sp.argTy).getD .unit
  let thr : List (String × Ty × List Nat) := sp.thr.map fun (g, t, xs) => (g, (resolveTy p g t).getD .unit, xs)
  if argTy.words.any (· != sp.args.length) then { errs := [SceText.liveArity sp.f sp.args.length (argTy.words.getD 0)] }
  else runSpecT cx sp strict argTy thr

/-- Whitespace-trimmed. -/
def strip (s : String) : String := s.trimAscii.toString

/-! ## Option values (`--threads`, `--final`, `--watch`): literals and UnElab types -/

/-- Split `s` at the top-level occurrences of `sep` (outside `()`, `[]`, `{}` and `"…"`). -/
def splitTop (s : String) (sep : Char := ',') : List String := Id.run do
  let mut out : List String := []
  let mut cur : List Char := []
  let mut depth : Int := 0
  let mut q := false
  for c in s.toList do
    if c == '"' then q := !q
    if !q && (c == '(' || c == '[' || c == '{') then depth := depth + 1
    if !q && (c == ')' || c == ']' || c == '}') then depth := depth - 1
    if !q && depth == 0 && c == sep then
      out := String.ofList cur.reverse :: out
      cur := []
    else cur := c :: cur
  return (String.ofList cur.reverse :: out).reverse.map strip

/-- `{a}{b}…` → `[a, b, …]`. -/
def groups (s : String) : Option (List String) := do
  let s := (strip s)
  if s.isEmpty then return []
  let rec go (cs : List Char) (acc : List String) (fuel : Nat) : Option (List String) :=
    match fuel with
    | 0 => none
    | f + 1 =>
      match cs.dropWhile Char.isWhitespace with
      | [] => some acc.reverse
      | '{' :: rest =>
        let rec take (cs : List Char) (d : Nat) (acc2 : List Char) (fuel : Nat) : Option (List Char × List Char) :=
          match fuel, cs with
          | 0, _ | _, [] => none
          | f + 1, c :: t =>
            if c == '}' then (if d == 0 then some (acc2.reverse, t) else take t (d - 1) (c :: acc2) f)
            else if c == '{' then take t (d + 1) (c :: acc2) f
            else take t d (c :: acc2) f
        match take rest 0 [] (rest.length + 1) with
        | some (g, t) => go t ((strip (String.ofList g)) :: acc) f
        | none => none
      | _ => none
  go s.toList [] (s.length + 1)

def unwrap (s : String) (o c : Char) : Option String :=
  let s := (strip s)
  if s.startsWith (String.singleton o) && s.endsWith (String.singleton c) then
    some ((s.drop 1).dropEnd 1).toString
  else none

def natList (s : String) : Option (List Nat) := do
  let b ← unwrap s '[' ']'
  if (strip b).isEmpty then return []
  (splitTop b).mapM String.toNat?

def nameOf (s : String) : String :=
  match unwrap s '"' '"' with | some n => n | none => (strip s)

/-- An UnElab type, or `_` (the block's own). -/
def tyOf (env : Syntax.Env) (s : String) : Except String (Option Ty) :=
  if (strip s) == "_" then .ok none else
  match parseTyE (strip s) env with
  | .ok t => .ok (some t)
  | .error e => .error s!"type {(strip s)}: {e.msg}"

/-- `--threads={f}{argTy}{args}{thr}`: f a block, argTy an UnElab type or `_`, args `[n, …]`, thr
`[(g, Ty, [n, …]), …]`. -/
def parseThreads (env : Syntax.Env) (v : String) : Except String (String × Option Ty × List Nat × List (String × Option Ty × List Nat)) := do
  let some [f, ty, args, thr] := groups v | throw SceText.threadsSyntax
  let argTy ← tyOf env ty
  let some args := natList args | throw SceText.threadsSyntax
  let some body := unwrap thr '[' ']' | throw SceText.threadsSyntax
  let ts ← if (strip body).isEmpty then pure [] else (splitTop body).mapM fun t => do
    let some inner := unwrap t '(' ')' | throw SceText.threadsSyntax
    let [g, ty, xs] := splitTop inner | throw SceText.threadsSyntax
    let some xs := natList xs | throw SceText.threadsSyntax
    pure (nameOf g, ← tyOf env ty, xs)
  pure (nameOf f, argTy, args, ts)

/-- `--final={[[n, …], …]}` (the braces optional). -/
def parseFinal (v : String) : Option (List (List Nat)) := do
  let v := (unwrap v '{' '}').getD v
  let b ← unwrap v '[' ']'
  if (strip b).isEmpty then return []
  (splitTop b).mapM natList

/-- `--watch={[("x", label, offset), …]}` (the braces optional). -/
def parseWatch (v : String) : Option (List (String × Nat × Nat)) := do
  let v := (unwrap v '{' '}').getD v
  let b ← unwrap v '[' ']'
  if (strip b).isEmpty then return []
  (splitTop b).mapM fun t => do
    let inner ← unwrap t '(' ')'
    let [x, l, o] := splitTop inner | none
    pure (nameOf x, ← (strip l).toNat?, ← (strip o).toNat?)

/-- A literal scenario argument as words (`()` has none). -/
def litWords : At → List Nat
  | .lit n => [n]
  | _ => []

/-- A `scenario` item as a `Spec`. -/
def ofScenario (s : Scenario) : Spec :=
  { name := s.name, f := s.setup.1, args := s.setup.2.flatMap litWords,
    thr := s.threads.map fun (g, as) => (g, none, as.flatMap litWords),
    promises := s.promises.getD 0, depth := s.depth.getD 300, crash := s.crash, live := some s.live,
    cert := s.cert }

#guard groups "{a}{.int b}{[0]}{[(\"w\", T, [])]}" == some ["a", ".int b", "[0]", "[(\"w\", T, [])]"]
#guard groups "{a}{b" == none
#guard splitTop "(a, [1, 2]), (b, {x, y}), \"c,d\"" == ["(a, [1, 2])", "(b, {x, y})", "\"c,d\""]
#guard natList "[1, 2, 30]" == some [1, 2, 30] && natList "[]" == some [] && natList "[x]" == none
#guard parseFinal "{[[0, 1], [2]]}" == some [[0, 1], [2]]
#guard parseWatch "{[(\"b_0\", 0, 0), (b_1, 1, 2)]}" == some [("b_0", 0, 0), ("b_1", 1, 2)]
#guard match parseThreads {} "{init}{_}{[0]}{[(worker, _, [1]), (\"w2\", Int, [])]}" with
  | .ok (f, none, [0], [("worker", none, [1]), ("w2", some .int, [])]) => f == "init"
  | _ => false
#guard (parseThreads {} "{init}{_}{[0]}").toOption.isNone

end SceLive
