/-
**hello.w on x86-64: the worker segment's fragment at depth** (the twin of
`Spike/Lib/A64HelloThrTCS.lean`): `SH exe endPc Z` over
`Spike/Lib/SegS.lean`'s `FragS`: off the transfer sites for hello (`NNH`,
`Spike/Lib/X64HelloNN.lean`), `Z` at the frames, on no frame `SysSafe`.

- `SH`, `nnzS`: a flat `NNZ` pair at depth `0` is in `SH`.

## Differences from the AArch64 version

- `SH` is over the x86-64 `isa` and wake's x86-64 `SysSafe`
  (`Spike/Lib/X64WakeNN.lean`).
- A64's `HThrHead.seg_thrHeadS`, `Child.seg_thrWorkerS`,
  `Child.seg_childStubS` (dead) are not twinned.
-/
import Spike.Lib.X64HelloNN
import Spike.Lib.SegS

namespace Spike.Lib.X64.Flow.Worker.Hello

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker

/-- **The worker segment's fragment**: off the transfer sites for hello,
`Z` at the frames, on no frame `SysSafe`. -/
abbrev SH (exe : _root_.Executable) (endPc : Int64) (Z : FragS isa) : FragS isa :=
  fun s c fs => NNH exe endPc s ∧ Z s c fs ∧ (fs = [] → SysSafe s)

/-- A flat `NNZ` pair at depth `0` is in `SH`. -/
theorem nnzS {exe : _root_.Executable} {endPc : Int64} {Z : FragS isa} {s : State} {c : Ctl}
    (h : NNZ exe endPc (fun s c => Z s c []) s c) : SH exe endPc Z s c [] :=
  ⟨h.1.toH, h.2, fun _ => h.1.2.2.2⟩

end Spike.Lib.X64.Flow.Worker.Hello

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.nnzS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.nnzS
