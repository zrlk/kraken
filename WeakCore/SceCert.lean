/-
# SceCert — liveness certificates for `sce` and cldoc

Mode A (§1c–§1e, §2): for a scenario that ran, the certificate of its start (`TermLiveCert.certOf`, at most `N`
configurations, `Promises.Knobs.all`, arm, the crash list `X`) is produced and checked by compiled evaluation
(`TermLiveCert.check`); the accepted guarantees are continuation lines of the scenario report.  The start is the
scenario start the run explored (`Doc.spawnStart` with `SceLive.kidsFor`'s kids, as `SceLive.runSpecT`).

Mode B (§3, `--live-proof`): the texts of the files under `root.cert/` (`certFiles`); `Sce.lean` writes and builds
them.  Nothing here is trusted: the PROVED lines rest on the kernel's checks in those files (`SceCertK`,
`TermLiveCertJoin`).
-/
import WeakCore.SceLive
import WeakCore.SceProof
import WeakCore.TermLiveCertGen
import WeakCore.SceCertK
import WeakCore.TermLiveCertJoin

namespace SceCert
open CoreLang CoreTerm Syntax TermRun

/-- The kernel limit (§3c, measured). -/
def kernelLimit : Nat := 1100
/-- Nodes per chunk file (§3c). -/
def chunk : Nat := 100

/-- A scenario whose certificate the kernel re-checks (§3g: eligible). -/
structure CertJob where
  /-- `Spec.name` (`--threads` for the command-line scenario): the `live[S]` of the PROVED lines -/
  name  : String
  /-- its directory under `root.cert/` -/
  dir   : String
  f     : String
  argTy : Ty
  args  : List Nat
  kids  : List TermSpawn.Kid
  depth : Nat
  crash : Option Nat
  fuel  : Nat
  /-- the final-state table's parameters (`OutcomesAt`): the thread count and the watched addresses -/
  m     : Nat
  watch : List (Nat × Nat)
  /-- the certificate has a spawn move (the spawn clause; otherwise `noSpawnB` is proved) -/
  spawn : Bool
  /-- the termination line holds (no crash thread, `noStuckB`) -/
  term  : Bool
  size  : Nat
  deriving Repr

/-- What mode A adds to a scenario: report lines (after the verdict), errors (exit 5), and the kernel job. -/
structure CertOut where
  lines : List String := []
  errs  : List String := []
  job   : Option CertJob := none
  deriving Inhabited

/-- The mode-A guarantees of an accepted certificate (§1d), unprefixed. -/
def acceptedLines (crash : Option Nat) (spawn term : Bool) : List String :=
  [SceText.certNoLivelock crash spawn, SceText.certFinals] ++ (if term then [SceText.certTerminates] else [])

/-- The certificate of a start: produced (within `N`), and the checker's verdict with its flags. -/
structure Checked where
  produced : Bool
  accepted : Bool
  spawn    : Bool
  term     : Bool
  size     : Nat

def checkStart (p : Prog) (X : List Nat) (N : Nat) (c0 : Cfg) : Checked :=
  let ct := TermLiveCert.certOf p Promises.Knobs.all .arm X [] N c0
  let produced := ct.succ.size == ct.nodes.size
  let accepted := produced && TermLiveCert.check p Promises.Knobs.all .arm X [] ct c0
  { produced, accepted, size := ct.nodes.size,
    spawn := accepted && !TermLiveCert.noSpawnB ct,
    term := accepted && X.isEmpty && TermLiveCert.noStuckB p Promises.Knobs.all .arm [] ct }

/-- The setup's result type (`SceLive.runSpecT`'s `rt`). -/
def retTyOf (p : Prog) (f : String) : Ty := ((p.find? (·.name == f)).map (·.retTy)).getD .unit

/-- Mode A for scenario `sp` (its effective values) that ran with `argTy` and the resolved threads `thr`; the
budget `N`.  The refusals in §1e's order (the kid shapes, promises, live); `liveProof`: an accepted certificate
within the kernel limit is a kernel job, a larger one gets the `certOver` line. -/
def certFor (p : Prog) (sp : SceLive.Spec) (argTy : Ty) (thr : List (String × Ty × List Nat)) (N : Nat)
    (liveProof : Bool) : CertOut :=
  let (kids, noKid) := SceLive.kidsFor (retTyOf p sp.f) thr
  if let some (g, t) := noKid then { errs := ["live: " ++ SceText.certNeedsKid g (showType t)] } else
  if sp.promises > 0 then { errs := [SceText.certNeedsPromises] } else
  if let some k := sp.live.filter (· > 0) then { errs := [SceText.certNeedsLive k] } else
  match Doc.spawnStart p sp.f argTy sp.args kids sp.depth with
  | none => {}
  | some c0 =>
    let r := checkStart p sp.crash.toList N c0
    if !r.produced then { errs := ["live: " ++ SceText.certNotProduced N] } else
    if !r.accepted then { errs := ["live: " ++ SceText.certNotAccepted] } else
    let lines := (acceptedLines sp.crash r.spawn r.term).map ("  " ++ ·)
    if !liveProof then { lines } else
    if r.size > kernelLimit then { lines := lines ++ [SceText.certOver r.size] } else
    let job : CertJob :=
      { name := sp.name, dir := (if sp.name == "--threads" then "threads" else sp.name),
        f := sp.f, argTy, args := sp.args, kids, depth := sp.depth, crash := sp.crash, fuel := N,
        m := thr.length, watch := sp.watch.map (·.2), spawn := r.spawn, term := r.term, size := r.size }
    { lines, job := some job }

/-- The PROVED lines of a job whose files built (§3a), without the `rechecked` lines. -/
def provedLines (j : CertJob) : List String :=
  [SceText.certProvedLivelock j.name j.crash j.spawn, SceText.certProvedFinals j.name] ++
    (if j.term then [SceText.certProvedTerminates j.name] else [])

/-! ## Mode B: the files under `root.cert/` (§3g) -/

def q (n : String) : String := "«" ++ n ++ "»"
def lit (f : Std.Format) : String := "\n".intercalate ((toString f).splitOn "\n" |>.map ("  " ++ ·))

/-- The module of `dir/file.lean` under the certificate root. -/
def modOf (dir file : String) : String := q dir ++ "." ++ q file

/-- `root.cert/prog.lean`: the program literal, re-checked against its text (M3d's pattern, C1). -/
def progText (root : String) (prog : Prog) : String :=
  s!"-- sce: the certificate program of {root}\nimport SceRun\n\n" ++
  s!"def prog : CoreTerm.Prog :=\n{lit (repr (show List Decl from prog))}\n\n" ++
  s!"def text : String := {repr (showProg prog)}\n\n" ++
  "#guard SceRun.recheck text {} [] prog == none\n"

def ranges (n : Nat) : List (Nat × Nat) :=
  (List.range ((n + chunk - 1) / chunk)).map fun i => (i * chunk, min chunk (n - i * chunk))

def xLit (j : CertJob) : String := s!"({repr j.crash.toList} : List Nat)"
def nodeOKFn (j : CertJob) : String :=
  s!"(TermLiveCert.Cert.nodeOK prog Promises.Knobs.all WeakMem.Arch.arm {xLit j} [] certK)"
def stuckFn : String := "(TermLiveCert.stuckOK prog Promises.Knobs.all WeakMem.Arch.arm [] certK)"
def spawnFn : String := "(TermLiveCert.spawnOK certK)"
/-- The flag ranges a job needs: `noSpawnB` without the spawn clause, `noStuckB` for the termination line. -/
def needsFlags (j : CertJob) : Bool := !j.spawn || j.term

/-- `S/start.lean`: the scenario as data, its start as a literal (`c0K`), and the start probe (§3b). -/
def startText (j : CertJob) : String :=
  s!"import {q "prog"}\nimport SceCertK\n\n" ++
  s!"def kids : List TermSpawn.Kid :=\n{lit (repr j.kids)}\n\n" ++
  s!"def argTy : CoreLang.Ty :=\n{lit (repr j.argTy)}\n\n" ++
  s!"def jobK : SceCertK.Job :=\n  \{ prog := prog, f := {repr j.f}, argTy := argTy, args := {repr j.args}, kids := kids,\n" ++
  s!"    depth := {j.depth}, X := {xLit j}, fuel := {j.fuel} }\n\n" ++
  "#sce_start\n\n" ++
  "/-- The start sce computed: the setup run, then the spawn (`Doc.spawnStart`), on the program literal. -/\n" ++
  s!"def cs : TermRun.Cfg := (Doc.spawnStart prog {repr j.f} argTy {repr j.args} kids {j.depth}).getD default\n\n" ++
  "theorem start_key : TermRun.cfgKey cs = TermRun.cfgKey c0K := by decide +kernel\n"

def certText (j : CertJob) : String :=
  s!"import {modOf j.dir "start"}\n\n#sce_cert\n"

def chunkText (j : CertJob) (a n : Nat) : String :=
  s!"import {modOf j.dir "cert"}\n\n" ++
  s!"theorem {q s!"c_{a}"} : (List.range' {a} {n}).all {nodeOKFn j} = true := by decide +kernel\n"

def flagText (j : CertJob) (a n : Nat) : String :=
  s!"import {modOf j.dir "cert"}\n\n" ++
  (if !j.spawn then
    s!"theorem {q s!"sp_{a}"} : (List.range' {a} {n}).all {spawnFn} = true := by decide +kernel\n" else "") ++
  (if j.term then
    s!"theorem {q s!"st_{a}"} : (List.range' {a} {n}).all {stuckFn} = true := by decide +kernel\n" else "")

/-- The join of the range theorems `pre_a` (of `ranges j.size`) into `name : (range' 0 size).all fn`. -/
def joinText (name pre fn : String) (rs : List (Nat × Nat)) : String :=
  let step : String × Nat × Nat → Nat × Nat → String × Nat × Nat := fun (acc, k, len) (a, n) =>
    let h := s!"j{pre}_{k + 1}"
    (acc ++ s!"  have {h} : (List.range' 0 {len + n}).all {fn} = true := TermLiveCert.all_range_join j{pre}_{k} {q s!"{pre}_{a}"}\n",
     k + 1, len + n)
  match rs with
  | [] => ""
  | (a, n) :: rest =>
    let init := s!"  have j{pre}_0 : (List.range' 0 {n}).all {fn} = true := {q s!"{pre}_{a}"}\n"
    let (body, k, _) := rest.foldl step (init, 0, n)
    s!"theorem {name} : (List.range' 0 certK.nodes.size).all {fn} = true := by\n  rw [h_size]\n" ++ body ++
      s!"  exact j{pre}_{k}\n\n"

/-- `S/main.lean`: `check` from the chunks (`check_intro`), the flags, and the statements at sce's start (§3d). -/
def mainText (j : CertJob) : String :=
  let rs := ranges j.size
  let imps := rs.map (fun (a, _) => s!"import {modOf j.dir s!"c{a}"}\n") ++
    (if needsFlags j then rs.map fun (a, _) => s!"import {modOf j.dir s!"s{a}"}\n" else [])
  let X := xLit j
  let watch := repr j.watch
  String.join imps ++ "\nopen TermLiveCert\n\n" ++
  s!"theorem h_size : certK.nodes.size = {j.size} := by decide +kernel\n" ++
  "theorem h_pos : 0 < certK.nodes.size := by decide +kernel\n" ++
  "theorem h_succ : certK.succ.size = certK.nodes.size := by decide +kernel\n" ++
  "theorem h_rank : certK.rank.size = certK.nodes.size := by decide +kernel\n" ++
  "theorem h_key : TermRun.cfgKey c0K = TermRun.cfgKey (certK.nodes[0]?.getD default) := by decide +kernel\n\n" ++
  joinText "h_nodes" "c" (nodeOKFn j) rs ++
  (if !j.spawn then joinText "h_spawn" "sp" spawnFn rs else "") ++
  (if j.term then joinText "h_stuck" "st" stuckFn rs else "") ++
  s!"theorem h_check : check prog Promises.Knobs.all WeakMem.Arch.arm {X} [] certK c0K = true :=\n" ++
  "  check_intro h_pos h_succ h_rank h_key h_nodes\n\n" ++
  (if j.spawn then
    s!"theorem {q "no_livelock"} : NoLivelockAt prog {X} kids cs := noLivelockAt_of_check h_check start_key\n"
  else
    s!"theorem {q "no_livelock"} : NoLivelockFairAt prog {X} kids cs :=\n" ++
    "  noLivelockFairAt_of_check h_check (noSpawnB_intro h_spawn) start_key\n") ++
  s!"theorem {q "final_states"} : OutcomesAt prog kids cs certK {j.m} {watch} :=\n" ++
  s!"  outcomesAt_of_check h_check start_key {j.m} {watch}\n" ++
  (if j.term then
    s!"theorem {q "terminates"} : TerminatesAt prog kids cs :=\n" ++
    "  terminatesAt_of_check h_check (noStuckB_intro h_stuck) start_key\n" else "") ++
  "\n#print axioms «no_livelock»\n#print axioms «final_states»\n" ++
  (if j.term then "#print axioms «terminates»\n" else "")

/-- A job's files (paths relative to `root.cert/`), in build order: start, cert, the range files, main. -/
def jobFiles (j : CertJob) : List (String × String) :=
  let rs := ranges j.size
  [(j.dir ++ "/start.lean", startText j), (j.dir ++ "/cert.lean", certText j)] ++
    rs.map (fun (a, n) => (j.dir ++ s!"/c{a}.lean", chunkText j a n)) ++
    (if needsFlags j then rs.map fun (a, n) => (j.dir ++ s!"/s{a}.lean", flagText j a n) else []) ++
    [(j.dir ++ "/main.lean", mainText j)]

/-! ## cldoc (`cert[=N]` on a `threads=` block, §2) -/

/-- The accepted guarantees typeset below the verdict; not produced / not accepted fail the document; a thread
outside the kid shapes is refused. -/
def docCert (p : Prog) (f : String) (argTy : Ty) (args : List Nat) (thr : List (String × Ty × List Nat))
    (N : Nat) (depth : Nat := 300) (crash : Option Nat := none) (_watch : List (String × Nat × Nat) := []) :
    Doc.Out :=
  let (kids, noKid) := SceLive.kidsFor (retTyOf p f) thr
  if let some (g, t) := noKid then Doc.fail (SceText.certNeedsKid g (showType t)) else
  match Doc.spawnStart p f argTy args kids depth with
  | none => {}
  | some c0 =>
    let r := checkStart p crash.toList N c0
    if !r.produced then Doc.fail (SceText.certNotProduced N) else
    if !r.accepted then Doc.fail SceText.certNotAccepted else
    { tex := "\n".intercalate ((acceptedLines crash r.spawn r.term).map fun l =>
        "\\par\\noindent{\\small " ++ Doc.texEsc l ++ "}") }

end SceCert
