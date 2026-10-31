/-
# SceFront — the front half of `sce` as a library

`elaborate root incl fs` does what `sce` does to a `.u` root before its live stage: it finds the imports
(`-I` directories, the importer's directory, `.i` preferred for the importers' view), parses and elaborates
every unit, checks each unit's blocks (`UDiag.diagnose`), and, when no unit has an error, checks each block
against the whole program (`checkDecl`), then `checkProg` itself, then the scope (`ProgScopeOKW`). It reads
files only through `fs` (`loadWith` and `elaborateIO` read them for a client). `SceRun.runU` is `elaborate`
followed by the live stage and emission, so `sce` and any other client elaborate identically.

Nothing here is trusted: every verdict is the checker's (shared, not copied). A client takes the program
from `Front.checked?`, which runs `checkProg`, `ProgScopeOKW` and `rtCheck` on it directly and returns it
with their proofs (`Checked`). The round trip of the printer and parser is checked per program (`RoundTrip`,
decided by `rtCheck`; `rtCheck_iff` proves the check equivalent to the property), not proved for all
programs, and only at run time: the parser is `partial`, so the kernel cannot evaluate `rtCheck`. The
`checkProg` and `ProgScopeOKW` parts are kernel-reducible.
-/
import WeakCore.SceCli
import WeakCore.UDiag
import WeakCore.TermScopeW

namespace SceRun
open CoreLang CoreTerm Syntax UnElab USyntax UDiag SceCli

/-! ## Diagnostics across files -/

/-- A secondary range, possibly in another file, with its message. -/
structure Note where
  file : String
  rng  : Rng
  msg  : String := ""
  deriving Repr, Inhabited

/-- A diagnostic with its exit class (`1` parse, `3` import/interface, `2` check, `0` warning). -/
structure SDiag where
  cls    : Nat
  d      : Diag
  xnotes : List Note := []
  /-- printed as the message alone (a live error of the `--threads` scenario, which has no source position) -/
  bare   : Bool := false
  deriving Repr, Inhabited

def mkD (cls : Nat) (file msg : String) (rng : Rng) (block : Option String := none) (xnotes : List Note := []) :
    SDiag :=
  { cls, d := { file := file, block := block, msg := msg, at_ := rng }, xnotes }

def at1 : Rng := { line := 1, col := 1, eline := 1, ecol := 2 }

def errRng (e : Err) : Rng := { line := e.line, col := e.col, eline := e.line, ecol := e.col + 1 }

/-- The file system `sce` sees: a file's text, or the reason it cannot be read. -/
abbrev FS := String → Except String String

structure Result where
  stdout : String := ""
  stderr : String := ""
  write  : Option (String × String) := none
  /-- `--live-proof`: the instance file to write and build (`Sce.lean` builds it). -/
  proof  : Option (String × String) := none
  /-- The PROVED lines, printed (by `Sce.lean`) only once the instance file has built. -/
  proved : List String := []
  /-- `--live-proof` with eligible certificates: the directory `root.cert`, the text of
  its `prog.lean`, and per scenario its directory, its PROVED lines and its files (relative, in build order). -/
  cert   : Option (String × String × List (String × List String × List (String × String))) := none
  code   : Nat := 0
  deriving Repr, Inhabited, BEq

def srcOf (fs : FS) (f : String) : String := match fs f with | .ok s => s | .error _ => ""

def exists_ (fs : FS) (f : String) : Bool := match fs f with | .ok _ => true | .error _ => false

def renderS (fs : FS) (s : SDiag) : String :=
  if s.bare then s.d.msg else
  let main := render (srcOf fs s.d.file) s.d
  let notes := s.xnotes.map fun n =>
    let lines := ((srcOf fs n.file).splitOn "\n").toArray
    let w := (toString n.rng.line).length
    String.intercalate "\n" ((s!"{n.file}:{n.rng.line}:{n.rng.col}: note:" ++ (if n.msg.isEmpty then "" else " " ++ n.msg)) :: excerpt lines w n.rng)
  String.intercalate "\n" (main :: notes)

/-- The exit code of a list of diagnostics: the first failing stage, parse → import → check → live. -/
def codeOf (ds : List SDiag) : Nat :=
  if ds.any (·.cls == 1) then 1 else if ds.any (·.cls == 3) then 3 else if ds.any (·.cls == 2) then 2
  else if ds.any (·.cls == 5) then 5 else if ds.any (·.cls == 4) then 4 else 0

def isErr (s : SDiag) : Bool := s.cls != 0

/-! ## Paths -/

def dirOf (f : String) : String :=
  match f.splitOn "/" with
  | [] | [_] => "."
  | ps => "/".intercalate ps.dropLast

def joinP (d x : String) : String := if d == "." then x else d ++ "/" ++ x

def baseName (f : String) : String :=
  let b := (f.splitOn "/").getLast?.getD f
  match b.splitOn "." with
  | [] | [_] => b
  | ps => ".".intercalate ps.dropLast

/-! ## Imports -/

/-- The `import` lines of a source: the module name and the range `import X`. -/
def importsOf (src : String) : List (String × Rng) :=
  match ulex src with
  | .error _ => []
  | .ok (toks, _) =>
    let rec go (i : Nat) (fuel : Nat) (acc : List (String × Rng)) : List (String × Rng) :=
      match fuel with
      | 0 => acc.reverse
      | f + 1 =>
        match toks[i]?, toks[i + 1]? with
        | some ⟨.id "import", l, c⟩, some ⟨.id n, l2, c2⟩ | some ⟨.id "import", l, c⟩, some ⟨.qid n, l2, c2⟩ =>
            let e := if l2 == l then c2 + n.length else c + 6
            go (i + 2) f ((n, { line := l, col := c, eline := l, ecol := e }) :: acc)
        | _, _ => acc.reverse
    go 0 toks.size []

structure UnitF where
  name  : String
  ufile : Option String
  ifile : Option String
  deriving Repr, Inhabited, BEq

structure LState where
  done  : List UnitF := []     -- dependencies first
  diags : List SDiag := []
  /-- every path looked up (for `Sce.lean`, which reads them before the pure run) -/
  probed : List String := []

/-- A frame of the import stack: the unit, and the import (file, range) that entered it. -/
structure Frame where
  name  : String
  via   : Option Note
  deriving Inhabited

def find (fs : FS) (dirs : List String) (f : String) : Option String :=
  (dirs.map (joinP · f)).find? (exists_ fs)

/-- Depth-first over the imports of `file`, `stk` the units being loaded (innermost first). -/
def loadImports (fs : FS) (incl : List String) (checkOnly : Bool) :
    Nat → List Frame → String → LState → LState
  | 0, _, _, st => st
  | fuel + 1, stk, file, st =>
    (importsOf (srcOf fs file)).foldl (init := st) fun st (x, rng) =>
      let here : Note := { file, rng, msg := SceText.importsHere ((stk.head?.map (·.name)).getD "") x }
      if let some k := stk.findIdx? (·.name == x) then
        -- the cycle: `x`, the units entered after it, back to `x`; a note on each import line entering them
        let inner := (stk.take k).reverse
        let names := x :: inner.map (·.name) ++ [x]
        let d := mkD 3 file (SceText.importCycle names) rng (xnotes := inner.filterMap (·.via))
        { st with diags := st.diags ++ [d] }
      else if st.done.any (·.name == x) then st
      else
        let dirs := dirOf file :: incl
        let st := { st with probed := st.probed ++ dirs.flatMap fun d => [joinP d (x ++ ".i"), joinP d (x ++ ".u")] }
        let fi := find fs dirs (x ++ ".i")
        let fu := find fs dirs (x ++ ".u")
        match fi, fu with
        | none, none => { st with diags := st.diags ++ [mkD 3 file (SceText.importNotFound x dirs) rng] }
        | _, _ =>
          let st := if fu.isNone && !checkOnly then
              { st with diags := st.diags ++ [mkD 3 file (SceText.importNoImpl x) rng] }
            else st
          let f := fu.getD (fi.getD "")
          let st := loadImports fs incl checkOnly fuel ({ name := x, via := some here } :: stk) f st
          if st.done.any (·.name == x) then st
          else { st with done := st.done ++ [{ name := x, ufile := fu, ifile := fi }] }

/-! ## Units -/

/-- The range of the first occurrence of `n` on line `l` at or after column `c`. -/
def nameRng (src : String) (l c : Nat) (n : String) : Rng :=
  let line := ((src.splitOn "\n").toArray)[l - 1]?.getD ""
  let rest := line.toList.drop (c - 1)
  let rec idx (cs : List Char) (i : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | f + 1 => if cs.take n.length == n.toList then some i else match cs with
      | [] => none
      | _ :: t => idx t (i + 1) f
  match idx rest 0 (rest.length + 1) with
  | some i => { line := l, col := c + i, eline := l, ecol := c + i + n.length }
  | none => { line := l, col := c, eline := l, ecol := c + 1 }

/-- The blocks of a parsed unit with the range of each name. -/
def declSites (src : String) (r : UParsed) : List (String × Rng) :=
  (r.unit.items.zip r.itemAt).filterMap fun
    | (.decl d _, (l, c)) => some (d.name, nameRng src l c ("def " ++ d.name) |> fun g =>
        { g with col := g.col + 4 })
    | _ => none

/-- One unit of the elaborated program that has an implementation (`Front.units`). -/
structure UnitOut where
  /-- the unit's `.u` file -/
  file   : String
  /-- its blocks, elaborated -/
  blocks : Prog
  /-- the source span of each node of its blocks that has one (`Span.block`, `Span.path`) -/
  spans  : List Span
  /-- the environment the unit was parsed in: its imports' types and protocols -/
  env    : Env

structure PState where
  env   : Env := {}
  prog  : Prog := []
  /-- per unit with an implementation: file, its blocks, spans, and the env it was parsed in -/
  units : List UnitOut := []
  sites : List (String × Note) := []
  diags : List SDiag := []
  /-- the signatures of imported units with an interface but no implementation (`--check-only`) -/
  isigs : Prog := []

def classify (nParse : Nat) (ds : List Diag) : List SDiag :=
  (ds.take nParse).map (fun d => { cls := 1, d }) ++
  (ds.drop nParse).map fun d => { cls := if d.severity == "warning" then 0 else 2, d }

def dupCheck (f : String) (sites : List (String × Note)) (ds : List (String × Rng)) :
    List SDiag × List (String × Note) :=
  ds.foldl (init := (([] : List SDiag), sites)) fun (acc, sites) (n, rng) =>
    match sites.find? (·.1 == n) with
    | some (_, first) =>
        (acc ++ [mkD 3 f (SceText.duplicate n) rng (some n) [{ first with msg := SceText.firstDefinedHere }]], sites)
    | none => (acc, sites ++ [(n, { file := f, rng })])

def processUnit (fs : FS) (st : PState) (u : UnitF) : PState :=
  let env0 := st.env
  let st := match u.ufile with
    | none => st
    | some f =>
      let src := srcOf fs f
      let r := parseUnitAll src env0
      let ds := classify r.errs.length (diagnose f src env0)
      let own := elabProg r.unit.decls
      let (dups, sites) := dupCheck f st.sites (declSites src r)
      { st with env := r.env, prog := st.prog ++ own, units := st.units ++ [{ file := f, blocks := own, spans := r.spans.toList, env := env0 }],
                sites := sites, diags := st.diags ++ ds ++ dups }
  match u.ifile with
  | none => st
  | some fi =>
    let src := srcOf fs fi
    let r := parseUnitAll src env0 (isI := true)
    -- the importers see the interface
    let sigs := if u.ufile.isSome then [] else r.unit.items.filterMap fun | .sig d _ => some d | _ => none
    { st with env := r.env, isigs := st.isigs ++ sigs, diags := st.diags ++ r.errs.map fun e => mkD 1 fi e.msg (errRng e) }

/-! ## The scope check, placed -/

/-- The first block failing the scope check, with the reason: the verdict is `ProgScopeOK`'s and `declWrapOK`'s
(per block, as `ProgScopeOKW` is their conjunction over the blocks); the reason is `checkW`'s message where it
fails, else the name of the failing predicate. -/
def scopeFail (p : Prog) (ctx : Prog := []) : Option (String × String) :=
  let q := ctx ++ p
  p.findSome? fun d =>
    if !TermScope.ProgScopeOK [d] then some (d.name, "ProgScopeOK")
    else if TermScope.declWrapOK q d then none
    else match TermScope.checkW q { inames := d.idx.reverse, vars := [(d.arg, d.argTy, true)], ret := d.retTy,
                                    ke := d.tparams.reverse.map some } d.body with
      | .error m => some (d.name, m)
      | .ok _ => some (d.name, "wrapOK")

/-- With no context, `scopeFail` is exactly `ProgScopeOKW`'s verdict. -/
theorem scopeFail_none {p : Prog} (h : scopeFail p = none) : TermScope.ProgScopeOKW p = true := by
  simp only [scopeFail, List.nil_append, List.findSome?_eq_none_iff] at h
  simp only [TermScope.ProgScopeOKW, TermScope.ProgWrapOK, TermScope.ProgScopeOK, Bool.and_eq_true,
    List.all_eq_true]
  refine ⟨fun d hd => ?_, fun d hd => ?_⟩
  · have := h d hd
    by_cases h1 : TermScope.ProgScopeOK [d] = true
    · simpa [TermScope.ProgScopeOK] using h1
    · simp [h1] at this
  · have := h d hd
    by_cases h1 : TermScope.ProgScopeOK [d] = true
    · by_cases h2 : TermScope.declWrapOK p d = true
      · exact h2
      · revert this
        simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ite_false]
        split <;> simp
    · simp [h1] at this

/-! ## Emission and re-check -/

/-- Re-parse an emitted text (in `env`) and re-check it against the program it was printed from (`ctx`: the
blocks it may call that it does not contain); `some reason` if that fails. -/
def recheck (text : String) (env : Env) (ctx want : Prog) : Option String :=
  match parseProg text env with
  | .error e => some (toString e)
  | .ok q =>
    if !(q.length == want.length && (want.zip q).all fun (a, b) => sameDecl a b) then some SceText.rDiffers
    else match q.forM (checkDecl (ctx ++ q)) with
      | .error m => some m
      | .ok _ => if ctx.isEmpty then (scopeFail q).map fun (_, r) => SceText.rScope r else none

def errText (fs : FS) (ds : List SDiag) : String :=
  let e := String.intercalate "\n" (ds.map (renderS fs))
  if e.isEmpty then "" else e ++ "\n"

end SceRun

namespace SceFront
open CoreLang CoreTerm Syntax UnElab USyntax UDiag SceRun

/-! The exit classes of `SDiag.cls` (named constants; `cls` stays a `Nat`). -/
namespace DiagClass
/-- A warning (exit 0). -/
def warning : Nat := 0
/-- A parse error (exit 1). -/
def parse : Nat := 1
/-- A check error (exit 2). -/
def check : Nat := 2
/-- An import, interface or duplicate-name error (exit 3). -/
def imports : Nat := 3
/-- An unreadable root file (exit 4): `sce` reports an unreadable root before any diagnostic; as a diagnostic it comes only from `elaborate`. -/
def io : Nat := 4
/-- A live-stage error (exit 5); never produced by `elaborate`. -/
def live : Nat := 5
end DiagClass

/-- An error (any class but `DiagClass.warning`). -/
abbrev SDiag.isError (s : SDiag) : Bool := isErr s

/-- What `elaborate` returns: the elaborated program and everything `sce` reports about it. -/
structure Front where
  /-- The elaborated program, dependencies first: a whole program only when `isigs` is empty; take it from
  `checked?`. -/
  prog    : Prog
  /-- Each unit with an implementation, dependencies first. -/
  units   : List UnitOut
  /-- Each block name with the file and range of its name in the source. -/
  sites   : List (String × Note)
  /-- Every diagnostic, in `sce`'s order. Class 1 is a parse error, 3 an import, interface or duplicate-name
  error, 2 a check error, 0 a warning, and 4 an unreadable root file (printed as the message alone). Class 5
  (the live stage) never comes from `elaborate`. The classes are named in `DiagClass`. -/
  diags   : List SDiag
  /-- The environment the root unit was parsed in: its imports' types and protocols. -/
  rootEnv : Env
  /-- With `checkOnly`: the signatures of imported units that have an interface but no implementation;
  otherwise empty. When it is not empty, `prog` is not a whole program (it may call blocks it does not
  contain), and `checked?` is `none`. -/
  isigs   : Prog := []

def loadRoot (fs : FS) (input : String) (incl : List String) (checkOnly : Bool) : LState :=
  loadImports fs incl checkOnly 64 [{ name := baseName input, via := none }] input {}

/-- `sce`'s front half on the root `input`. `incl` lists the `-I` directories, in order. With `checkOnly`
(`sce --check-only`), an import with an interface and no implementation is allowed, and its signatures are
the context of the whole-program check. When every block passes `checkDecl` but `checkProg` rejects the
program (a whole program only), the result has a class 2 diagnostic with `checkProg`'s own message. -/
def elaborate (input : String) (incl : List String) (fs : FS) (checkOnly : Bool := false) : Front :=
  match fs input with
  | .error e =>
    { prog := [], units := [], sites := [], rootEnv := {},
      diags := [{ cls := DiagClass.io, d := { file := input, msg := SceText.cannotRead input e, at_ := at1 },
                  bare := true }] }
  | .ok _ =>
  let ls := loadRoot fs input incl checkOnly
  let units := ls.done ++ [{ name := baseName input, ufile := some input, ifile := none }]
  let ps := units.foldl (processUnit fs) {}
  let ds := ls.diags ++ ps.diags
  -- the whole program (only when every unit is clean): a checker error is placed on its block
  let ds := if ds.any isErr then ds else
    ds ++ ps.prog.filterMap fun d => match checkDecl (ps.isigs ++ ps.prog) d with
      | .ok _ => none
      | .error m =>
        let site := (ps.sites.find? (·.1 == d.name)).map (·.2)
        some (mkD 2 ((site.map (·.file)).getD input) m ((site.map (·.rng)).getD at1) (some d.name))
  let ds := if ds.any isErr || !ps.isigs.isEmpty then ds else match checkProg ps.prog with
    | .ok _ => ds
    | .error m => ds ++ [{ cls := DiagClass.check, d := { file := input, msg := m, at_ := at1 }, bare := true }]
  let ds := if ds.any isErr then ds else match scopeFail ps.prog ps.isigs with
    | some (b, r) =>
        let site := (ps.sites.find? (·.1 == b)).map (·.2)
        ds ++ [mkD 2 ((site.map (·.file)).getD input) (SceText.scopeError r) ((site.map (·.rng)).getD at1)
                (if b.isEmpty then none else some b)]
    | none => ds
  { prog := ps.prog, units := ps.units, sites := ps.sites, diags := ds, isigs := ps.isigs,
    rootEnv := match ps.units.getLast? with | some u => u.env | none => {} }

/-- The files `elaborate input incl _ checkOnly` may read, given what `fs` can read so far: the root and every
import candidate looked up. A client reads them and calls `probes` again until no new file appears;
`loadWith` does that. -/
def probes (input : String) (incl : List String) (fs : FS) (checkOnly : Bool := false) : List String :=
  input :: (loadRoot fs input incl checkOnly).probed

/-- The file system of a cache: a file not in it is "not read". -/
def cacheFS (cache : List (String × Except String String)) : FS := fun f =>
  match cache.find? (·.1 == f) with
  | some (_, r) => r
  | none => .error "not read"

def fixLoad {m : Type → Type} [Monad m] (probe : FS → List String) (read : String → m (Except String String)) :
    m (List (String × Except String String)) := do
  let mut cache : List (String × Except String String) := []
  for _ in [0:1000] do
    let new := (probe (cacheFS cache)).eraseDups.filter fun f => !cache.any (·.1 == f)
    if new.isEmpty then break
    for f in new do
      cache := cache ++ [(f, ← read f)]
  return cache

/-- Reads, with `read`, every file `elaborate input incl _ checkOnly` may look at: `probes` again and again
until no new file appears (at most 1000 rounds), as `sce` does. The result is a cache for `cacheFS`. -/
def loadWith {m : Type → Type} [Monad m] (read : String → m (Except String String)) (input : String)
    (incl : List String) (checkOnly : Bool := false) : m (List (String × Except String String)) :=
  fixLoad (fun fs => probes input incl fs checkOnly) read

def readIO (f : String) : IO (Except String String) := do
  try return .ok (← IO.FS.readFile f) catch e => return .error (toString e)

/-- `elaborate` on the real file system: `loadWith` with `IO.FS.readFile`, then `elaborate`. -/
def elaborateIO (input : String) (incl : List String) (checkOnly : Bool := false) : IO Front := do
  let cache ← loadWith readIO input incl checkOnly
  return elaborate input incl (cacheFS cache) checkOnly

/-- Decides `RoundTrip` by printing and re-parsing. -/
def rtCheck (p : Prog) : Bool :=
  match parseProg (showProg p) with
  | .ok q => q.length == p.length && (p.zip q).all fun (a, b) => sameDecl a b
  | .error _ => false

/-- The printed program parses back to the same program: `parseProg (showProg p)` succeeds, with as many
blocks as `p`, each `sameDecl` to its original. `sameDecl` compares the blocks' fields and the `repr` text
of their bodies. Stated for the empty environment and for the program text alone (no header line); this is
how `sce` emits a whole program. -/
def RoundTrip (p : Prog) : Prop :=
  ∃ q, parseProg (showProg p) = .ok q ∧ q.length = p.length ∧
    ∀ a b, (a, b) ∈ p.zip q → sameDecl a b = true

/-- The check decides exactly the property. -/
theorem rtCheck_iff (p : Prog) : rtCheck p = true ↔ RoundTrip p := by
  constructor
  · intro h
    unfold rtCheck at h
    split at h
    · rename_i q hq
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      exact ⟨q, hq, h.1, fun a b hab => h.2 (a, b) hab⟩
    · simp at h
  · rintro ⟨q, hq, hl, hall⟩
    simp only [rtCheck, hq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    exact ⟨hl, fun x hx => hall x.1 x.2 hx⟩

instance (p : Prog) : Decidable (RoundTrip p) := decidable_of_iff _ (rtCheck_iff p)

/-- No error diagnostic, and the round trip of the elaborated program is checked (`rtCheck`). With
`checkOnly` this can hold for a program that is not whole (`isigs`); use `checked?` for the program. -/
def Front.ok (f : Front) : Bool := !f.diags.any isErr && rtCheck f.prog

/-- When `Front.ok` holds, `RoundTrip` holds for that program (checked per program, not proved in general;
usable at run time only, since the kernel cannot evaluate the parser). -/
theorem Front.ok_roundTrip {f : Front} (h : f.ok = true) : RoundTrip f.prog := by
  simp only [Front.ok, Bool.and_eq_true] at h
  exact (rtCheck_iff _).1 h.2

/-- A whole program with the proofs a client needs: it is accepted by `checkProg`, it passes the scope check,
and its round trip is checked (`RoundTrip`, at run time). -/
structure Checked where
  prog    : Prog
  checked : checkProg prog = .ok ()
  scope   : TermScope.ProgScopeOKW prog = true
  rt      : RoundTrip prog

/-- The elaborated program with its proofs: `some` only when no diagnostic is an error, `isigs` is empty,
and `checkProg`, `ProgScopeOKW` and `rtCheck` all accept `prog` (each run here, directly). -/
def Front.checked? (f : Front) : Option Checked :=
  if f.diags.any isErr || !f.isigs.isEmpty then none else
  match hc : checkProg f.prog, hs : TermScope.ProgScopeOKW f.prog, hr : rtCheck f.prog with
  | .ok (), true, true => some ⟨f.prog, hc, hs, (rtCheck_iff _).1 hr⟩
  | _, _, _ => none

/-- `checked?` returns the elaborated program itself. -/
theorem Front.checked_prog {f : Front} {c : Checked} (h : f.checked? = some c) : c.prog = f.prog := by
  unfold Front.checked? at h
  split at h
  · simp at h
  · split at h
    · cases h; rfl
    · simp at h

/-- The source span of a node of the elaborated program: its block and its path (child indices from the
block's body, as `Span.path`), with the `.u` file it came from (`UnitOut.file`); `none` for a node with no
span (e.g. one the elaboration introduced). -/
def Front.spanOf (f : Front) (block : String) (path : List Nat) : Option (String × Span) :=
  f.units.findSome? fun u => (spanAt u.spans block path).map (u.file, ·)

end SceFront

#print axioms SceFront.rtCheck_iff
#print axioms SceFront.Front.ok_roundTrip
#print axioms SceFront.Front.checked_prog
