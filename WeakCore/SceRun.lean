/-
# SceRun — the `sce` pipeline as a pure function

`run args fs` reads files only through `fs` and returns what `sce` prints, the file it writes (`-o`) and the
exit code; `Sce.lean` is the I/O shell.  Nothing here is trusted: every verdict is the checker's (`checkDecl`,
`checkProg`, `ProgScopeOKW`; shared, not copied), and every emitted program is re-parsed and re-checked before it
is written (a failure there is exit 6, a bug in `sce`).

Stages (all run, every diagnostic printed; the exit code is the first failing stage in the order
parse 1 → import/interface 3 → check 2 → live 5; usage/IO 4; internal 6):
1. imports: `import X` is looked up in the importing file's directory, then each `-I` directory.  `X.i` (the
   interface) is preferred over `X.u` for the importers' view; `X.u` supplies the blocks of the emitted program.
   Not found, an interface without an implementation (unless `--check-only`), and import cycles are errors; a
   block name defined twice (across or within units) is an error with a note on the first.  Units are processed
   dependencies first; the signatures visible to a unit are those of every unit processed before it (v1:
   transitive).  `.i`/`.u` conformance is M4's.
2. each unit: `UDiag.diagnose` (parse errors, one checker error per block, the `ret f(args)` lint).
3. the whole program: `checkProg` and `ProgScopeOKW` (`scope error: …`), each error placed on its block.  Stages 1–3 are `SceFront.elaborate`, shared with other clients of the front half.
4. the live stage (mode A, `SceLive.runSpec`; no errors before it): with `--threads`, that scenario alone; with
   `--live=N`, every scenario of the root unit; otherwise the scenarios some `live[S]` names.  Each prints its
   report on stderr; a mismatch (`--live`/the scenario's `live`, `--live-strict`, `--final`) is exit 5.  A
   `live[S]` naming no scenario is exit 5; a scenario thread with no `live` annotation is a warning.
   Then the liveness instance (M3d, `instStage`): for every `live` def of the root unit, the robust premise of
   `TermLiveL3`'s theorems (`SceProof.robustOK`, evaluated by compiled code; `--live-proof` has Lean's kernel
   decide it in the instance file, `proofText`), and for `live[S]` the kids of scenario `S` as well.  It prints
   `live def f: PROVED …` (and `live[S] def f: PROVED …` for a scenario instance) at the end, for each instance
   that holds, even if the run fails elsewhere (with `--live-proof`, only once the instance file builds, each with
   `  re-checked in Lean: F` under it); a protocol outside the premise, or a thread outside the kid shapes, is
   exit 5 (for that instance).
5. emission (no errors): the header, then the program; re-parsed, compared with `sameDecl`, re-checked.
A `.w` input is parsed (`Syntax.parseProg`), checked block by block, scope-checked and reprinted; the live stage
runs only for `--threads`.
-/
import WeakCore.SceCli
import WeakCore.SceFront
import WeakCore.SceLive
import WeakCore.UDiag
import WeakCore.TermScopeW
import WeakCore.SceProof
import WeakCore.SceCert

namespace SceRun
open CoreLang CoreTerm Syntax UnElab USyntax UDiag SceCli

/-- The result of a run with diagnostics `ds` and, if no error, the emitted `text` (or `none`: nothing to emit).
`corrupt` is a test hook (the identity in `sce`): it alters the text before the re-check, to reach exit 6.

`ok`: lines printed last, whatever the exit code (the PROVED lines). -/
def finish (o : Opts) (fs : FS) (ds : List SDiag) (text : Option (String × (String → Option String)))
    (corrupt : String → String) (report : List String := []) (ok : List String := []) : Result :=
  let err := String.join (report.map (· ++ "\n")) ++ errText fs ds
  let okLines := String.join (ok.map (· ++ "\n"))
  let okErr := err ++ okLines
  match text with
  | none => { stderr := okErr, code := codeOf ds }
  | some (t, chk) =>
    let t := corrupt t
    match chk t with
    | some reason => { stderr := err ++ SceText.internal reason ++ "\n", code := 6 }
    | none =>
      match o.out with
      | some f => { stderr := okErr, write := some (f, t), code := codeOf ds }
      | none => { stdout := t, stderr := okErr, code := codeOf ds }

/-! ## The live stage (mode A) -/

/-- The range of `n` after the keyword `kw` on the item at `(l, c)`. -/
def nameAt (src : String) (l c : Nat) (kw n : String) : Rng :=
  let g := nameRng src l c (kw ++ n)
  { g with col := g.col + kw.length, ecol := g.col + kw.length + n.length }

def scenarioSites (src : String) : List (UItem × Nat × Nat) → List (Scenario × Rng)
  | [] => []
  | (UItem.scenario sc, l, c) :: rest => (sc, nameAt src l c "scenario " sc.name) :: scenarioSites src rest
  | _ :: rest => scenarioSites src rest

def annSites (src : String) : List (UItem × Nat × Nat) → List (String × Option (Option String) × Rng)
  | [] => []
  | (UItem.decl d lv, l, c) :: rest => (d.name, lv, nameAt src l c "def " d.name) :: annSites src rest
  | _ :: rest => annSites src rest

/-- The root unit's scenarios to run (with their sites), and the annotation diagnostics: `live[S]` naming no
scenario (exit 5); a scenario thread entry without a `live` annotation (warning). -/
def rootLive (o : Opts) (over : SceLive.Spec → SceLive.Spec) (file src : String) (r : UParsed) :
    List (SceLive.Spec × Option (String × Rng)) × List SDiag :=
  let items : List (UItem × Nat × Nat) := r.unit.items.zip r.itemAt
  let scens := scenarioSites src items
  let ann := annSites src items
  let named : List String := ann.filterMap fun (_, lv, _) => match lv with | some (some s) => some s | _ => none
  let noScen : List SDiag := ann.filterMap fun (f, lv, rng) => match lv with
    | some (some s) => if scens.any (·.1.name == s) then none
        else some (mkD 5 file (SceText.liveNoScenario s) rng (some f))
    | _ => none
  let warns : List SDiag := scens.flatMap fun (sc, rng) =>
    (sc.threads.map (·.1)).eraseDups.filterMap fun g =>
      match ann.find? (·.1 == g) with
      | some (_, none, _) =>
          some { cls := 0, d := { file := file, severity := "warning", msg := SceText.liveUnannotated g, at_ := rng } }
      | _ => none
  let run := if o.threads.isSome then [] else scens.filter fun (sc, _) => o.live.isSome || named.contains sc.name
  -- `cert = N` on a scenario that does not run (item 38, §1c)
  let unused : List SDiag := scens.filterMap fun (sc, rng) =>
    match sc.cert with
    | some n => if run.any (·.1.name == sc.name) then none else
        some { cls := 0, d := { file := file, severity := "warning", msg := SceText.certUnused sc.name n, at_ := rng } }
    | none => none
  (run.map fun (sc, rng) => (over (SceLive.ofScenario sc), some (file, rng)), noScen ++ warns ++ unused)

/-- The scenarios to run and what they print.  `root`: the root unit's file, source and parse (`.u` mode).
`.error m`: an option value that does not read (exit 4).  The scenarios whose certificates the kernel re-checks
(`--live-proof`, item 38) come last. -/
def liveStage (o : Opts) (fs : FS) (prog : Prog) (units : List (String × Prog × List Span)) (env : Env)
    (root : Option (String × String × UParsed)) :
    Except String (List String × List SDiag × List SceCert.CertJob) := do
  let cx : SceLive.Ctx := { prog, units, src := srcOf fs }
  let final ← match o.final with
    | none => pure none
    | some v => match SceLive.parseFinal v with
      | some f => pure (some f)
      | none => throw (SceText.optError "--final" SceText.finalSyntax)
  let watch ← match o.watch with
    | none => pure []
    | some v => match SceLive.parseWatch v with
      | some w => pure w
      | none => throw (SceText.optError "--watch" SceText.watchSyntax)
  let over (sp : SceLive.Spec) : SceLive.Spec :=
    { sp with live := o.live.orElse fun _ => sp.live, promises := o.promises.getD sp.promises,
              depth := o.depth.getD sp.depth, crash := o.crash.orElse fun _ => sp.crash,
              final := final.orElse fun _ => sp.final, watch := if watch.isEmpty then sp.watch else watch }
  -- the `--threads` scenario
  let cli : List (SceLive.Spec × Option (String × Rng)) ← match o.threads with
    | none => pure []
    | some v => match SceLive.parseThreads env v with
      | .ok (f, argTy, args, thr) => pure [(over { name := "--threads", f, argTy, args, thr, live := none }, none)]
      | .error e => throw (if e == SceText.threadsSyntax then e else SceText.optError "--threads" e)
  -- the root unit's scenarios and annotations
  let (fileSpecs, fileDs) := match root with
    | none => ([], [])
    | some (file, src, r) => rootLive o over file src r
  let outs := (cli ++ fileSpecs).map fun (sp, site) =>
    let r := SceLive.runSpec cx sp o.liveStrict
    -- the certificate (item 38, §1c): `cert = N` takes precedence; `--live-cert` acts only on live = 0 or absent
    let budget := sp.cert.orElse fun _ => if sp.live.any (· > 0) then none else o.liveCert
    let c : SceCert.CertOut := match budget, r.ran with
      | some n, some (argTy, thr) => SceCert.certFor prog sp argTy thr n o.liveProof
      | _, _ => {}
    let rep := r.report.take 3 ++ c.lines ++ r.report.drop 3
    let report := match site, rep with
      | some (file, rng), first :: rest => s!"{file}:{rng.line}:{rng.col}: {first}" :: rest
      | _, rs => rs
    let ds := (r.errs ++ c.errs).map fun m => match site with
      | some (file, rng) => mkD 5 file m rng
      | none => { cls := 5, d := { file := "", msg := m, at_ := at1 }, bare := true }
    (report, ds, c.job.toList)
  pure (outs.flatMap (·.1), fileDs ++ outs.flatMap (·.2.1), outs.flatMap (·.2.2))

/-! ## The liveness instance (M3d) -/

/-- The root unit's `live` defs: the block, the scenario of `live[S]`, the site. -/
def liveDefs (src : String) (r : UParsed) : List (String × Option String × Rng) :=
  (annSites src (r.unit.items.zip r.itemAt)).filterMap fun (f, lv, rng) => lv.map fun s => (f, s, rng)

/-- What the instance stage found: its report, its errors, the defs whose instance holds and the scenario
instances that hold (the def, the scenario, its kids). -/
structure Inst where
  proved : List String := []
  ds     : List SDiag := []
  mains  : List String := []
  scens  : List (String × String × List TermSpawn.Kid) := []

/-- The instance stage: for every `live` def of the root unit, the robust premise of the liveness theorems
(`SceProof.robustOK`, evaluated) for the program's protocols, and for `live[S]` also for the kids of scenario `S`
(`SceLive.scenKids`, the kids the search spawns).  A protocol outside it, or a thread outside the kid shapes, is
exit 5; the def's main instance is reported regardless of its scenario. -/
def instStage (prog : Prog) (env : Env) (file src : String) (r : UParsed) : Inst :=
  let ms := TermLiveL3.protosOf prog
  let scens := scenarioSites src (r.unit.items.zip r.itemAt)
  let cx : SceLive.Ctx := { prog, units := [], src := fun _ => "" }
  (liveDefs src r).foldl (init := {}) fun acc (f, s, rng) =>
    let err (m : String) : Inst := { acc with ds := acc.ds ++ [mkD 5 file m rng (some f)] }
    match SceProof.firstBad ms with
    | some P => err (SceText.noInstance f (showProto env P))
    | none =>
      let acc : Inst := { acc with proved := acc.proved ++ [SceText.proved f], mains := acc.mains ++ [f] }
      let err (m : String) : Inst := { acc with ds := acc.ds ++ [mkD 5 file m rng (some f)] }
      match s.bind fun s => scens.find? (·.1.name == s) with
      | none => acc
      | some (sc, _) =>
        match SceLive.scenKids cx (SceLive.ofScenario sc) with
        | none => acc
        | some (_, some (g, t)) => err (SceText.noScenInstance sc.name f g (showType t))
        | some (kids, none) =>
          match SceProof.firstBad (ms ++ TermLiveL3.kidProtos kids) with
          | some P => err (SceText.noInstance f (showProto env P))
          | none => { acc with proved := acc.proved ++ [SceText.provedScen sc.name f], scens := acc.scens ++ [(f, sc.name, kids)] }

/-- The instance file of `--live-proof`: the program as Lean data (re-checked against its text), the robust
premise by `decide`, and one theorem per instance. -/
def proofText (root : String) (prog : Prog) (i : Inst) : String :=
  let lit (f : Std.Format) : String := "\n".intercalate ((toString f).splitOn "\n" |>.map ("  " ++ ·))
  let q (n : String) : String := "«" ++ n ++ "»"
  let mains := i.mains.map fun f =>
    s!"theorem {q ("live_" ++ f)} : SceProof.MainInst prog := SceProof.mainInst prog robust_main\n"
  let scens := i.scens.map fun (f, sc, kids) =>
    let k := q ("kids_" ++ f)
    s!"def {k} : List TermSpawn.Kid :=\n{lit (repr kids)}\n" ++
    s!"theorem {q ("robust_" ++ f)} : SceProof.robustOK (TermLiveL3.protosOf prog ++ TermLiveL3.kidProtos {k}) = true := by\n  decide\n" ++
    s!"theorem {q ("live_" ++ f ++ "_" ++ sc)} : SceProof.ScenInst prog {k} := SceProof.scenInst prog _ {q ("robust_" ++ f)}\n"
  let names := i.mains.map (fun f => q ("live_" ++ f)) ++ i.scens.map fun (f, sc, _) => q ("live_" ++ f ++ "_" ++ sc)
  SceText.proofHeader root ++ "\nimport SceProof\nimport SceRun\n\n" ++
  s!"def prog : CoreTerm.Prog :=\n{lit (repr (show List Decl from prog))}\n\n" ++
  s!"def text : String := {repr (showProg prog)}\n\n" ++
  "#guard SceRun.recheck text {} [] prog == none\n\n" ++
  "theorem robust_main : SceProof.robustOK (TermLiveL3.protosOf prog) = true := by\n  decide\n\n" ++
  String.join mains ++ String.join scens ++ "\n" ++ String.join (names.map (s!"#print axioms {·}\n"))

/-- `dir/foo.u` ↦ `dir/foo.live.lean`. -/
def proofFile (input : String) : String := joinP (dirOf input) (baseName input ++ ".live.lean")

/-- `dir/foo.u` ↦ `dir/foo.cert` (item 38, §3g). -/
def certDir (input : String) : String := joinP (dirOf input) (baseName input ++ ".cert")

/-- `Result.cert` for the eligible scenarios `jobs` (none: nothing is written). -/
def certOf (input : String) (prog : Prog) (jobs : List SceCert.CertJob) :
    Option (String × String × List (String × List String × List (String × String))) :=
  if jobs.isEmpty then none else
  some (certDir input, SceCert.progText (baseName input) prog,
    jobs.map fun j => (j.dir, SceCert.provedLines j, SceCert.jobFiles j))

/-- The `.w` mode. -/
def runW (o : Opts) (fs : FS) (src : String) (corrupt : String → String) : Result :=
  match parseProg src with
  | .error e => finish o fs [mkD 1 o.input e.msg (errRng e)] none corrupt
  | .ok p =>
    let lines := (src.splitOn "\n").toArray
    let defLine (n : String) : Nat :=
      (((List.range lines.size).find? fun i => (lines[i]!).startsWith ("def " ++ n)).map (· + 1)).getD 1
    let ds := p.filterMap fun d => match checkDecl p d with
      | .ok _ => none
      | .error m => some (mkD 2 o.input m (nameRng src (defLine d.name) 5 d.name) (some d.name))
    let ds := if !ds.isEmpty then ds else match scopeFail p with
      | some (b, r) => [mkD 2 o.input (SceText.scopeError r) (nameRng src (defLine b) 5 b) (if b.isEmpty then none else some b)]
      | none => ds
    if !ds.isEmpty then finish o fs ds none corrupt else
    match (if o.wantsLive then liveStage o fs p [] {} none else .ok ([], [], [])) with
    | .error m => { stderr := m ++ "\n", code := 4 }
    | .ok (report, lds, jobs) =>
    let ds := ds ++ lds
    let withCert (r : Result) : Result :=
      if o.liveProof && r.code != 6 then { r with cert := certOf o.input p jobs } else r
    withCert <|
    if ds.any isErr || o.mode == .checkOnly then finish o fs ds none corrupt report
    else
      let t := SceText.header o.input ++ "\n" ++ showProg p ++ "\n"
      finish o fs ds (some (t, fun t => recheck t {} [] p)) corrupt report

/-- The `.u` mode. -/
def runU (o : Opts) (fs : FS) (corrupt : String → String) : Result :=
  let root := baseName o.input
  let f := SceFront.elaborate o.input o.incl fs (o.mode == .checkOnly)
  let ds := f.diags
  if ds.any isErr then finish o fs ds none corrupt else
  let rootEnv := f.rootEnv
  let rootSrc := srcOf fs o.input
  let rootR := parseUnitAll rootSrc rootEnv
  -- a `live[S]` or a scenario: the live stage runs (a scenario that no `live[S]` names is only checked for warnings)
  let annotated := rootR.unit.items.any fun | .decl _ (some (some _)) => true | .scenario _ => true | _ => false
  match (if o.wantsLive || annotated then
      liveStage o fs f.prog (f.units.map fun u => (u.file, u.blocks, u.spans)) rootR.env
        (some (o.input, rootSrc, rootR))
    else .ok ([], [], [])) with
  | .error m => { stderr := m ++ "\n", code := 4 }
  | .ok (report, lds, jobs) =>
  let inst := instStage f.prog rootEnv o.input rootSrc rootR
  let ds := ds ++ lds ++ inst.ds
  -- each instance that holds gets its PROVED line at the end (decision, D3 (i)), even if the run fails
  -- elsewhere; with --live-proof, the lines wait for the instance file (`Sce.lean` builds it; nothing is written
  -- when nothing is proved)
  let proving := o.liveProof && !inst.proved.isEmpty
  let ok := if proving then [] else inst.proved
  let withProof (r : Result) : Result :=
    let r := if o.liveProof && r.code != 6 then { r with cert := certOf o.input f.prog jobs } else r
    if proving && r.code != 6 then
      { r with proof := some (proofFile o.input, proofText root f.prog inst), proved := inst.proved }
    else r
  withProof <|
  if ds.any isErr || o.mode == .checkOnly then finish o fs ds none corrupt report ok
  else
    let hdr := SceText.header o.input ++ "\n"
    match o.mode with
    | .printElab =>
        let body := "\n\n".intercalate (f.units.map fun u => showProgElab u.blocks u.spans u.env)
        finish o fs ds (some (hdr ++ body ++ "\n", fun t => recheck t {} [] f.prog)) corrupt report ok
    | .emitUnit =>
        let (own, env) := match f.units.getLast? with
          | some u => (u.blocks, u.env)
          | none => ([], {})
        finish o fs ds (some (hdr ++ showProg own env ++ "\n", fun t => recheck t env env.lib.reverse own)) corrupt report ok
    | _ => finish o fs ds (some (hdr ++ showProg f.prog ++ "\n", fun t => recheck t {} [] f.prog)) corrupt report ok

/-- The files `run args fs` may read: the input and every import candidate looked up (with `fs` so far). -/
def probes (args : List String) (fs : FS) : List String :=
  match parseArgs args with
  | .error _ => []
  | .ok o =>
    if o.help then [] else if o.isW then [o.input] else
    SceFront.probes o.input o.incl fs (o.mode == .checkOnly)

/-- `sce args`, reading files through `fs`.  `corrupt`: the test hook of `finish`. -/
def run (args : List String) (fs : FS) (corrupt : String → String := id) : Result :=
  match parseArgs args with
  | .error m => { stderr := (match m with | some m => m ++ "\n" | none => "") ++ SceText.usageError, code := 4 }
  | .ok o =>
    if o.help then { stdout := SceText.help } else
    match fs o.input with
    | .error e => { stderr := SceText.cannotRead o.input e ++ "\n", code := 4 }
    | .ok src => if o.isW then runW o fs src corrupt else runU o fs corrupt

end SceRun

#print axioms SceRun.scopeFail_none
