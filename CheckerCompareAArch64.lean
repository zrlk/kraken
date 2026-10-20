/-
checkercompare_aarch64 - tool: run AArch64 litmus tests
and `.kl` programs like `krakenlitmus_aarch64`, but with the prototype
checker (`Kraken.Promising.CheckerCompare.exploreRB`: breadth-first
`certifyB` and the paper's post-state promise rule) in place of the main
`explore`.

Usage: checkercompare_aarch64 [-kinds kinds.txt] [-fuel N] [-v] [-sym]
         [-promises N] [-lse2] <test.litmus | program.kl>...

The output has `krakenlitmus_aarch64`'s format (herd's report, `Configs` with
`-v`, `Fault` lines), so a comparison script can parse both outputs alike.
Not a default target: `lake build checkercompare_aarch64`.
-/
import Kraken.Litmus.AArch64
import Kraken.Litmus.CheckerCompare

open Kraken.Litmus Kraken.Litmus.AArch64 Kraken.Promising

/-- `AArch64.runPrepared` with `exploreRB` (no witnesses). -/
def runPreparedB (t : Test) (p : Prepared) (kind : Option String) (o : ExploreOpts) (lse2 : Bool) :
    Result :=
  let r := if lse2 then
      CheckerCompare.exploreRB (I := Kraken.Promising.AArch64.isaLSE2) Arch.armv8 p.configLSE2
        (fun c => projectSt t p.layout (c.threads.map (·.st)) c.mem) o
    else CheckerCompare.exploreRB (I := Kraken.Promising.AArch64.isa) Arch.armv8 p.config (project t p.layout) o
  let norm (o : Obs) (v : Value) : Value := match o, v with
    | .reg r, .num n => p.layout.present (regType t r) (regDefault t r) ((BitVec.ofInt 64 n).setWidth 128)
    | .loc x, v => p.layout.normLoc x v
    | _, v => v
  { report := report t r.finals kind norm, ok := verdict t r.finals norm,
    configs := r.configs, boundHit := r.boundHit,
    faults := r.faults.eraseDups, witnesses := [] }

def readKinds (path : String) : IO (List (String × String)) := do
  let src ← IO.FS.readFile path
  return (src.splitOn "\n").filterMap fun l =>
    match (l.splitOn " ").filter (· ≠ "") with
    | [name, kind] => some (name, kind)
    | _ => none

structure Opts where
  kinds : Option String := none
  fuel : Nat := 64
  verbose : Bool := false
  maxPromises : Option Nat := none
  symmetric : Bool := false
  lse2 : Bool := false
  files : List String := []

def parseArgs : List String → Opts
  | "-kinds" :: k :: rest => { parseArgs rest with kinds := some k }
  | "-fuel" :: n :: rest => { parseArgs rest with fuel := n.toNat?.getD 64 }
  | "-v" :: rest => { parseArgs rest with verbose := true }
  | "-promises" :: n :: rest => { parseArgs rest with maxPromises := n.toNat? }
  | "-sym" :: rest => { parseArgs rest with symmetric := true }
  | "-lse2" :: rest => { parseArgs rest with lse2 := true }
  | f :: rest => let o := parseArgs rest; { o with files := f :: o.files }
  | [] => {}

def printResult (name : String) (verbose : Bool) (r : Result) : IO Unit := do
  IO.print r.report
  if verbose then
    IO.println s!"Configs {r.configs}{if r.boundHit then " (certification budget hit)" else ""}"
  for m in r.faults do IO.println s!"Fault {name}: {m}"
  IO.println ""

def main (args : List String) : IO UInt32 := do
  let o := parseArgs args
  let eo : ExploreOpts := { fuel := o.fuel, maxPromises := o.maxPromises, symmetric := o.symmetric }
  let kinds ← match o.kinds with
    | some p => readKinds p
    | none => pure []
  let mut status : UInt32 := 0
  for f in o.files do
    let src ← IO.FS.readFile f
    let job : Except String (String × Test × Prepared) :=
      if f.endsWith ".kl" then do
        let p ← parseProgram src
        let pr ← prepareProgram p
        pure (p.name, p.toTest, pr)
      else do
        let t ← parse src
        if t.arch != "AArch64" then throw s!"architecture {t.arch}"
        let pr ← prepare t
        pure (t.name, t, pr)
    match job with
    | .error e =>
      IO.println s!"Unsupported {f}: {e}\n"
      status := 1
    | .ok (name, t, pr) =>
      let kind := (kinds.find? (·.1 == name)).map (·.2)
      match checkMixed (runPreparedB t pr kind eo o.lse2) with
      | .error e =>
        IO.println s!"Unsupported {name}: {e}\n"
        status := 1
      | .ok r => printResult name o.verbose r
  return status
