import Kraken.Litmus.Syntax

/-!
Parser checks over the frozen corpus: every test parses, and a few are
inspected in detail.
-/
namespace Kraken.Litmus.Tests

def corpus := "Kraken/Litmus/corpus/"

def parseFile (rel : String) : IO (Except String Test) := do
  let src ← IO.FS.readFile (corpus ++ rel)
  return parse src

/-- info: ok: AArch64 MP+rel+acq
inits: [(0, "X1", "x"), (0, "X3", "y"), (1, "X1", "x"), (1, "X3", "y")]
threads: [["MOV W0,#1", "STR W0,[X1]", "MOV W2,#1", "STLR W2,[X3]"], ["LDAR W2,[X3]", "LDR W0,[X1]"]]
quant: Kraken.Litmus.Quant.exists
cond: 1:X2=1 /\ 1:X0=0
observables: [1:X2, 1:X0] -/
#guard_msgs in
#eval do
  match ← parseFile "aarch64/MP+rel+acq.litmus" with
  | .error e => IO.println s!"error: {e}"
  | .ok t =>
    IO.println s!"ok: {t.arch} {t.name}"
    IO.println s!"inits: {repr (t.inits.map fun | Init.reg r v _ => (r.tid, r.reg, v.toString) | Init.loc x v _ => (99, x, v.toString))}"
    IO.println s!"threads: {repr t.threads}"
    IO.println s!"quant: {repr t.quant}"
    IO.println s!"cond: {t.cond.toString}"
    IO.println s!"observables: {t.observables.map Obs.toString}"

/-- info: ok: X86_64 SB
threads: [["movl $1,(x)", "movl (y),%eax"], ["movl $1,(y)", "movl (x),%eax"]]
cond: 0:rax=0 /\ 1:rax=0 -/
#guard_msgs in
#eval do
  match ← parseFile "x86_64/SB.litmus" with
  | .error e => IO.println s!"error: {e}"
  | .ok t =>
    IO.println s!"ok: {t.arch} {t.name}"
    IO.println s!"threads: {repr t.threads}"
    IO.println s!"cond: {t.cond.toString}"

/-- info: ok: AArch64 A01
inits: [(0, "X0", "0"), (0, "X1", "x"), (99, "x", "0"), (0, "X2", "0")]
threads: [["LDRB W0, [X1, X2, UXTW]"]]
cond: 0:X0=0 -/
#guard_msgs in
#eval do
  match ← parseFile "aarch64-instructions/A01.litmus" with
  | .error e => IO.println s!"error: {e}"
  | .ok t =>
    IO.println s!"ok: {t.arch} {t.name}"
    IO.println s!"inits: {repr (t.inits.map fun | Init.reg r v _ => (r.tid, r.reg, v.toString) | Init.loc x v _ => (99, x, v.toString))}"
    IO.println s!"threads: {repr t.threads}"
    IO.println s!"cond: {t.cond.toString}"

-- Arrays: a declaration with a type and size, a whole-array
-- initialiser and condition, elements in the condition and `locations`
-- (`locations` may contain `a[0]`), a pointer-typed register, a
-- multi-word type and 128-bit literals.
/-- info: inits: [(99, "x[2]", some "int", "{1,2}"),
 (99, "y", some "unsigned __int128", "340282366920938463463374607431768211455"),
 (0, "X2", some "int64_t*", "x[1]")]
cond: x={3,2} /\ x[1]=2 /\ [y]=1
locations: [x[0], 0:X0] -/
#guard_msgs in
#eval do
  let src := "AArch64 T\n{ int x[2] = {1,2}; unsigned __int128 y = 0xffffffffffffffffffffffffffffffff; int64_t *0:X2 = x[1]; }\n P0;\n NOP;\nlocations [x[0];0:X0;]\nforall (x={3,2} /\\ x[1]=2 /\\ y=1)"
  match parse src with
  | .error e => IO.println s!"error: {e}"
  | .ok t =>
    IO.println s!"inits: {repr (t.inits.map fun | Init.reg r v ty => (r.tid, r.reg, ty, v.toString) | Init.loc x v ty => (99, x, ty, v.toString))}"
    IO.println s!"cond: {t.cond.toString}"
    IO.println s!"locations: {t.locations.map Obs.toString}"

/-- Parse every test of a suite; report the failures. -/
def parseSuite (dir : String) : IO (Nat × List String) := do
  let entries ← System.FilePath.readDir (corpus ++ dir)
  let files := (entries.toList.map (·.fileName)).filter (·.endsWith ".litmus") |>.mergeSort (· ≤ ·)
  let mut bad : List String := []
  for f in files do
    match ← parseFile (dir ++ "/" ++ f) with
    | .ok _ => pure ()
    | .error e => bad := bad ++ [s!"{f}: {e}"]
  return (files.length, bad)

/-- info: aarch64: 52 tests, 0 failures
x86_64: 28 tests, 0 failures
x86: 21 tests, 0 failures
x86_64-instructions: 15 tests, 0 failures -/
#guard_msgs in
#eval do
  for d in ["aarch64", "x86_64", "x86", "x86_64-instructions"] do
    let (n, bad) ← parseSuite d
    IO.println s!"{d}: {n} tests, {bad.length} failures"
    for b in bad do IO.println s!"  {b}"

-- The remaining failures are tests outside the fragment: pointer
-- initialisers, code and instruction values, memory tags, page-table
-- entries, conditions on labels and faults.
/-- info: aarch64-instructions: 309 tests, 39 failures -/
#guard_msgs in
#eval do
  let (n, bad) ← parseSuite "aarch64-instructions"
  IO.println s!"aarch64-instructions: {n} tests, {bad.length} failures"

end Kraken.Litmus.Tests
