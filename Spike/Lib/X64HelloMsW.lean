/-
**hello.w on x86-64: the worker's memory side with `print`'s byte step** (`msWH`, the worker side's twin of
`X64HelloMs.msH` at `X64HelloByteOutP.helloMsW`; the twin of `Spike/Lib/HelloMsW.lean`).

`msWH L G SR w` is `msH L G SR w` with `bo := ByteOutP helloSrc (SR w).lbl` and
`we := WeAb abi (WriteAb.Ab lab)` (`X64HelloByteOutP.helloMsW` at the spawn record's placement and the write
abort's phase from `print`'s refused `write`, `X64WriteAb.Ab`; every other field `msH`'s).

- `msWH`: the memory side at record `w`.

**Where this differs from AArch64** (forced by the x86-64 shape): the memory side is over `X64.isa` and its
runtime layout `X64.Rt.RuntimeLayout`, the abort phase is `Spike.Lib.X64.WriteAb.Ab` (AArch64: `isaLSE2`,
`A64.Rt.RuntimeLayout`, `Spike.Lib.A64.WriteAb.Ab`). A64's `msWH_bo`, `msWH_we`, `msWH_K`, `msWH_G`, the `withBW`
lifts `OutL.withBW`, `OutT.withBW`, `OutTS.withBW`, `SegTCS.withBW`, and `segTCS_msWH`, `hseg_msWH` are dead in the
hello proof and are not twinned; `msWH` is an `abbrev`, so this module has no axioms check.
-/
import Spike.Lib.X64HelloByteOutP
import Spike.Lib.X64WriteAb

namespace Spike.Lib.X64HelloMsW

open Kraken.Promising Kraken.Promising.X64
open Scc.Sem
open Spike.Lib
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {ι : Type} (L : RuntimeLayout) (G : ι → Loc → Val → Prop) (SR : ι → Inv2Core.SpawnRec)

/-- **The worker's memory side at record `w`**: `msH L G SR w` with `print`'s byte step at the record's
placement and the write abort's phase as the abort justification. -/
abbrev msWH (w : ι) : MemSide isa :=
  X64HelloByteOutP.helloMsW L (G w) (SR w).lbl (SR w).lsize
    (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels L.exe).label)

end Spike.Lib.X64HelloMsW
