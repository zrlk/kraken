/-
**wake.w's source facts at main's `spawn`, ISA-free** (for
`Spike.Lib.X64WakePreA.ClonePre`): main's term at the `spawn` and its
`ThreadId`'s label, restated from `Spike.Lib.WakePreA.spawnTerm` and
`Spike.Lib.WakeT1.mainTidLbl`, whose modules reach `Kraken.AArch64.Syntax`
(which cannot be imported next to `Kraken.X64.Syntax`). This module imports
neither ISA; `Spike/Test/WakeSrcDefsEq.lean` (A64 side only) checks both
against the originals by `rfl`.

- `spawnTerm`: main's term at the `spawn`.
- `mainTidLbl`: the main thread's own `ThreadId`'s label.
-/
import WeakCore.TermRun

namespace Spike.Lib.X64WakeSrcDefs

/-- **main's term at the `spawn`** (wake.w's `main` after `z`, `o`, `c`,
`p`): `let t = spawn worker p in tail waitLoop c`. -/
def spawnTerm : CoreTerm.Expr :=
  .let_ "t"
    (.spawn "worker" (.var "p")
      (.prod (.ptr .pub .int) .tid) [])
    (.tail "waitLoop" [] (.var "c") [])

/-- **The main thread's own `ThreadId`'s label** in a start of label stripe `cap`. -/
def mainTidLbl (cap : Nat) : WeakMem.AllocLabel := TermRun.freshLabel 0 (max cap 1) 0 0

end Spike.Lib.X64WakeSrcDefs
