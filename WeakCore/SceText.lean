/-
# SceText — every user-facing message of `sce` in one place

The texts are the exact output strings.
-/

namespace SceText

/-- The usage block (verbatim). -/
def usage : String := "sce [options] root.u          elaborate root.u and its imports to one .w (stdout, or -o FILE)
sce [options] prog.w          parse, check and reprint a .w (a checker and normaliser)
  -I DIR            a directory searched for imported .i/.u files (repeatable)
  -o FILE           write the .w to FILE
  --check-only      check (own blocks against imports' interfaces, and the whole program); emit nothing
  --print-elab      print the elaborated .w with a `-- line:col` comment on every let
  --emit-unit       print only the root unit's blocks (for inspection; not a program for scc)
  --threads={f}{argTy}{args}{thr}   run f as setup, then the threads thr exhaustively (cldoc's threads= groups, in UnElab
                    syntax: f a block, argTy a type, args [n, …], thr [(g, Ty, [n, …]), …]; a type may be _ for \"from the
                    block's signature\")
  --live=N  --final={…}  --watch={…}  --promises=N  --depth=N  --crash=i   as the cldoc options of the same names
  --live-strict     a cut search (budget reached) counts as a failure (off by default)
  --live-proof      also write root.live.lean (the liveness instance for every `live def`, see §4) and build it with Lean
  --live-cert[=N]   also produce and check a liveness certificate for every scenario run with live = 0 (promise-free
                    runs; at most N configurations, default 20000; a scenario's own cert = N takes precedence)"

/-- `sce --help` (exit 0): the usage text, a blank line, the project slogan. -/
def help : String := usage ++ "\n\nShare and enjoy!\n"

/-- The flag list: the usage block's option lines. -/
def flagList : String := "\n".intercalate ((usage.splitOn "\n").filter (·.startsWith "  "))

/-- A usage error (exit 4): the usage line and the flag list. -/
def usageError : String := "usage: sce [options] FILE.u|FILE.w\n" ++ flagList ++ "\n"

/-- The first line of every emitted program. -/
def header (root : String) : String := s!"-- sce: from {root}"

/-! ## Exit 4 -/
def cannotRead (f err : String) : String := s!"sce: cannot read {f}: {err}"
def unknownOption (o : String) : String := s!"sce: unknown option {o}"

/-! ## Exit 6 -/
def internal (reason : String) : String :=
  s!"sce: internal error (a bug in sce): the emitted program does not re-parse/re-check: {reason}"

/-! ## Exit 3 -/
def importNotFound (x : String) (dirs : List String) : String :=
  s!"cannot find import {x} (searched: {", ".intercalate dirs})"
def importCycle (cyc : List String) : String := s!"import cycle: {" -> ".intercalate cyc}"
def duplicate (x : String) : String := s!"duplicate definition of {x}"
def firstDefinedHere : String := "first defined here"

/-! ## Further messages -/
def importNoImpl (x : String) : String :=
  s!"cannot emit: import {x} has an interface ({x}.i) but no implementation ({x}.u); use --check-only to check against interfaces alone"
def cannotWrite (f err : String) : String := s!"sce: cannot write {f}: {err}"
def scopeError (reason : String) : String := s!"scope error: {reason}"
def importsHere (x y : String) : String := s!"{x} imports {y} here"

/-! ## Internal-error reasons (the `<reason>` of `internal`) -/
def rDiffers : String := "the emitted program re-parses to a different program"
def rScope (reason : String) : String := s!"the emitted program fails the scope check: {reason}"

/-! ## The live stage -/
def scopePromises (n : Nat) : String := s!"promises ≤ {n}"
def scopeFree : String := "promise-free runs only"
/-- The status line; `cut = some reasons` for a search the budgets cut. -/
def liveStatus (scope : String) (n : Nat) (cut : Option (List String)) : String :=
  s!"bounded search: {scope}, {n} configurations, " ++
    (match cut with | some rs => "CUT OFF (" ++ ", ".intercalate rs ++ ")" | none => "search complete")
def liveExpected (n m : Nat) : String := s!"live: expected {n} fair livelock(s), found {m}"
def liveStrict (reasons : List String) : String :=
  s!"live: search cut off ({", ".intercalate reasons}) and --live-strict is set"
def liveSetup (f : String) : String := s!"live: setup {f} did not complete"
def liveUnannotated (x : String) : String := s!"scenario names {x}, which has no live annotation"
def liveKind (k count : Nat) (sizes : List Nat) : String :=
  s!"livelock kind {k} (×{count}, sizes {", ".intercalate (sizes.map toString)}):"
def liveThreadAt (i : Nat) (tag place : String) : String := s!"thread {i} {tag} at {place}"

/-! ## The live stage: reports -/
/-- A thread's state in a livelock class. -/
def tagSpins : String := "[spins]"
def tagFinished : String := "[finished]"
def tagBlocked : String := "[blocked]"
/-- A thread whose term is not found in the root unit's source (the report line without its position). -/
def liveThread (i : Nat) (tag : String) : String := s!"thread {i} {tag}"
def liveStart (s f args : String) (thr : List String) : String :=
  s!"scenario {s}: scenario start: setup {f}({args}), threads {", ".intercalate thr}"
def liveVerdict (v : String) : String := s!"verdict: {v}"
def liveResults (i : Nat) (g xs : String) (rs : List String) : String :=
  s!"thread {i} {g}(…{if xs.isEmpty then "" else ", " ++ xs}): results " ++
    (if rs.isEmpty then "none" else "{" ++ ", ".intercalate rs ++ "}")
def finalsHead (k : Nat) : String := s!"final states, {k} distinct (thread results; memory):"
def liveNoBlock (s g : String) : String := s!"live: scenario {s} names no block {g}"
def liveNoScenario (s : String) : String := s!"live: live[{s}] names no scenario {s}"
def liveAffine (g t : String) : String :=
  s!"live: thread entry {g} returns an affine value ({t}); a scenario thread must return a plain value"
def liveFinal (got want : String) : String := s!"live: final outcomes {got}, expected {want}"
def liveArity (g : String) (k m : Nat) : String :=
  s!"live: {g} takes {k} literal argument(s) here, the signature needs {m}"
def threadsSyntax : String := "sce: --threads: expected {f}{argTy}{args}{thr}"
/-! ## The liveness instance -/
def proved (f : String) : String := s!"live def {f}: PROVED (under the standard obligations)"
def noInstance (f p : String) : String :=
  s!"live: live def {f}: no instance: protocol {p} is neither robust nor an epoch counter (the held branch is not proved yet)"
def noScenInstance (s f g t : String) : String :=
  s!"live: live[{s}] def {f}: no scenario instance: thread {g}'s argument type {t} is not the setup's result, a pair of it and the literals, or the literals alone"
/-! ## `--live-proof`, the scenario instance, `--check-only --live-proof` -/
/-- A scenario instance that holds. -/
def provedScen (s f : String) : String := s!"live[{s}] def {f}: PROVED (under the standard obligations)"
/-- Under each PROVED line, once `--live-proof` has built the instance file. -/
def rechecked (file : String) : String := s!"  re-checked in Lean: {file}"
/-- The instance file did not build (exit 5; no PROVED line is printed); Lean's messages follow. -/
def proofFails (file : String) : String := s!"live: --live-proof: the instance {file} does not build:"
/-- The first line of a written instance file. -/
def proofHeader (root : String) : String := s!"-- sce: the liveness instance of {root}"
/-- A usage error (exit 4): `--check-only` emits nothing, `--live-proof` a file. -/
def checkOnlyProof : String := "sce: --check-only: --live-proof emits a file"

/-- `sce: --threads: <parse error>`; "the same form for `--final` and `--watch`". -/
def optError (o e : String) : String := s!"sce: {o}: {e}"
def finalSyntax : String := "expected {[[n, …], …]}"
def watchSyntax : String := "expected {[(x, n, n), …]}"

/-! ## Liveness certificates -/
/-- The clauses of a certificate line: the crash clause with `crash = i`, the spawn clause when the certificate has a
spawn move. -/
def certClauses (crash : Option Nat) (spawn : Bool) : String :=
  (match crash with | some i => s!"; thread {i} may stop at any point" | none => "") ++
  (if spawn then "; spawned threads scheduled fairly" else "")
/-- Mode A (§1d): the compiled checker accepted the certificate; continuation lines after the verdict. -/
def certNoLivelock (crash : Option Nat) (spawn : Bool) : String :=
  "no fair livelock: certificate checked for promise-free runs (compiled evaluation" ++ certClauses crash spawn ++ ")"
def certFinals : String := "final states: exhaustive: certificate checked for promise-free runs (compiled evaluation)"
def certTerminates : String :=
  "every fair run reaches a final state: certificate checked for promise-free runs (compiled evaluation)"
/-- An unmet certificate request (§1e, §2; `sce` prefixes `live: `, cldoc does not). -/
def certNotProduced (n : Nat) : String := s!"certificate not produced (more than {n} configurations)"
def certNotAccepted : String := "certificate not accepted by the checker"
def certNeedsKid (g t : String) : String :=
  s!"cert needs every thread to be a scenario kid: thread {g}'s argument type {t} is not the setup's result, a pair of it and the literals, or the literals alone"
def certNeedsPromises : String := "live: cert needs promises = 0 (certificates cover promise-free runs)"
def certNeedsLive (k : Nat) : String := s!"live: cert needs live = 0 (this run expects {k} livelocks)"
/-- A warning (§1c): `cert = N` on a scenario that does not run. -/
def certUnused (s : String) (n : Nat) : String := s!"scenario {s} has cert = {n} but does not run"
/-- Option refusals (exit 4, §1c, §1e). -/
def certOptThreads : String := optError "--live-cert" "with --threads, needs --live=0"
def certOptPromises : String := optError "--live-cert" "needs --promises=0 (certificates cover promise-free runs)"
/-- `--live-proof` (§3a): printed at the end once scenario `s`'s certificate files have built, each with `rechecked`. -/
def certProvedLivelock (s : String) (crash : Option Nat) (spawn : Bool) : String :=
  s!"live[{s}]: no fair livelock: PROVED for promise-free runs (under the standard obligations; kernel-checked certificate; arm" ++
    certClauses crash spawn ++ ")"
def certProvedFinals (s : String) : String :=
  s!"live[{s}]: final states: exhaustive: PROVED for promise-free runs (under the standard obligations; kernel-checked certificate; arm)"
def certProvedTerminates (s : String) : String :=
  s!"live[{s}]: every fair run reaches a final state: PROVED for promise-free runs (under the standard obligations; kernel-checked certificate; arm)"
/-- Why there is no kernel line (§3b). -/
def certOver (k : Nat) : String := s!"  not re-checked in Lean: the certificate has {k} configurations (limit 1100)"
def certNoReduce : String := "  not re-checked in Lean: the scenario's start does not reduce in the kernel"
def certLimit : String :=
  "  not re-checked in Lean: the scenario's start could not be checked in the kernel (memory or time limit)"
/-- A certificate file that does not build (§3g, exit 5); Lean's messages follow. -/
def certFails (file : String) : String := s!"live: --live-proof: the certificate {file} does not build:"
/-- `main.lean` built but a theorem rests on a non-standard axiom (exit 5); Lean's
`#print axioms` lines follow. -/
def certAxioms (file : String) : String :=
  s!"live: --live-proof: the certificate {file} depends on axioms other than propext, Classical.choice, Quot.sound:"

end SceText
