/-
krakenlitmus_aarch64 - run herd7 AArch64 litmus tests on Kraken's Promising machine.

Usage: krakenlitmus_aarch64 [-kinds kinds.txt] [-fuel N] [-v] [-witness] [-traces]
         [-sym] [-promises N] [-i] [-lse2] <test.litmus | program.kl>...

Prints herd's report for each test (without the `Time` and `Hash` lines).
With `-v`, also prints the number of configurations explored and whether the
certification budget was hit. With `-witness`, prints a trace (thread steps,
timestamps read and written, promises) for each final state satisfying the
condition; `-traces` prints one for every final state. The exploration is
breadth first, so each trace is a shortest run. `-sym`, `-promises` and `-i`
are described in `Kraken/Litmus/README.md`. `-lse2` models FEAT_LSE2 hardware: a
16-byte-aligned `LDP`/`STP` of two `X` registers to a declared 16-byte location
is single-copy atomic. herd7 has no such option; it is off by default.
-/
import Kraken.Litmus.AArch64

open Kraken.Litmus

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
  /-- Print a witness trace for each final state satisfying the condition. -/
  witness : Bool := false
  /-- Print a witness trace for every final state. -/
  traces : Bool := false
  /-- Cap on outstanding promises per thread (incomplete exploration). -/
  maxPromises : Option Nat := none
  /-- Symmetry reduction over identical threads. -/
  symmetric : Bool := false
  /-- Interactive stepper instead of exhaustive exploration. -/
  interactive : Bool := false
  /-- FEAT_LSE2: single-copy-atomic 16-byte `LDP`/`STP` (Kraken-only, off by default). -/
  lse2 : Bool := false
  files : List String := []

def parseArgs : List String → Opts
  | "-kinds" :: k :: rest => { parseArgs rest with kinds := some k }
  | "-fuel" :: n :: rest => { parseArgs rest with fuel := n.toNat?.getD 64 }
  | "-v" :: rest => { parseArgs rest with verbose := true }
  | "-witness" :: rest => { parseArgs rest with witness := true }
  | "-traces" :: rest => { parseArgs rest with traces := true }
  | "-promises" :: n :: rest => { parseArgs rest with maxPromises := n.toNat? }
  | "-sym" :: rest => { parseArgs rest with symmetric := true }
  | "-i" :: rest => { parseArgs rest with interactive := true }
  | "-lse2" :: rest => { parseArgs rest with lse2 := true }
  | f :: rest => let o := parseArgs rest; { o with files := f :: o.files }
  | [] => {}

def main (args : List String) : IO UInt32 := do
  let o := parseArgs args
  let (kindsPath, fuel, verbose, files) := (o.kinds, o.fuel, o.verbose, o.files)
  let eo : Kraken.Promising.ExploreOpts := { fuel, maxPromises := o.maxPromises, symmetric := o.symmetric }
  let kinds ← match kindsPath with
    | some p => readKinds p
    | none => pure []
  let mut status : UInt32 := 0
  for f in files do
    let src ← IO.FS.readFile f
    if f.endsWith ".kl" then
      match parseProgram src with
      | .error e =>
        IO.println s!"Unsupported {f}: {e}\n"
        status := 1
      | .ok p =>
        let kind := (kinds.find? (·.1 == p.name)).map (·.2)
        if o.interactive then
          match AArch64.prepareProgram p with
          | .ok pr => AArch64.interact pr eo
          | .error e => IO.println s!"Unsupported {p.name}: {e}"
          continue
        match AArch64.runProgram p kind eo o.lse2 with
        | .error e =>
          IO.println s!"Unsupported {p.name}: {e}\n"
          status := 1
        | .ok r =>
          IO.print r.report
          if verbose then
            IO.println s!"Configs {r.configs}{if r.boundHit then " (certification budget hit)" else ""}"
          for m in r.faults do IO.println s!"Fault {p.name}: {m}"
          if o.witness || o.traces then
            for (st, hit, tr) in r.witnesses do
              if o.traces || hit then
                IO.println s!"\nWitness for {st.line}{if hit then "  (of interest)" else ""}:"
                IO.println tr
          IO.println ""
      continue
    match parse src with
    | .error e =>
      IO.println s!"Unsupported {f}: {e}\n"
      status := 1
    | .ok t =>
      if t.arch != "AArch64" then
        IO.println s!"Unsupported {f}: architecture {t.arch}\n"
        status := 1
      else
        let kind := (kinds.find? (·.1 == t.name)).map (·.2)
        if o.interactive then
          match AArch64.prepareAny t with
          | .ok pr => AArch64.interact pr eo
          | .error e => IO.println s!"Unsupported {t.name}: {e}"
          continue
        match AArch64.run t kind eo o.lse2 with
        | .error e =>
          IO.println s!"Unsupported {t.name}: {e}\n"
          status := 1
        | .ok r =>
          IO.print r.report
          if verbose then
            IO.println s!"Configs {r.configs}{if r.boundHit then " (certification budget hit)" else ""}"
          for m in r.faults do IO.println s!"Fault {t.name}: {m}"
          if o.witness || o.traces then
            for (st, hit, tr) in r.witnesses do
              if o.traces || hit then
                IO.println s!"\nWitness for {st.line}{if hit then "  (of interest)" else ""}:"
                IO.println tr
          IO.println ""
  return status
