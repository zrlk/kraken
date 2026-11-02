/-
**The frame condition of `print`'s call landing at the call node, on x86-64** (the twin of the live part of
`Spike/Lib/A64HelloPrintTCS.lean`): the fact `X64HelloPrintTCSX`'s call of hello's `scc_rt_print` hands to
each of its callee obligations (the `write`, the nodes, the abort path, the return landing), the
`hcallee` fact of `Spike/Lib/X64HelloCallTCSX.lean`'s `call_ndTCSX` with the frame and the entry dropped.

- `PrintF.CallFC`: every memory of the callee's frame condition comes from a caller's state at the call
  node, keeping its cells outside the callee's region.

**Where this differs from AArch64** (forced by the x86-64 shape): the callee's region is seen from the frame
base `nC.o.sp - 8` (x86-64's `call` pushes the return address at `nC.o.sp`; AArch64: `nC.o.sp`), and reaches
72 bytes below it and 16 above (`print`'s region `[-40, 16)` and the abort dispatcher's 32 bytes below
`print`'s abort exit at `-40`; AArch64: `[-96, 0)`). A64's `SegTCS.seq_or`, `seg_printCalleeS` and
`printF_callTCS` are dead in the hello proof (their `SegTCSX` forms are `X64HelloPrintTCSX`'s) and are not
twinned.
-/
import Spike.Lib.X64Call

namespace Spike.Lib.X64.Flow.Worker.PrintF

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64

/-- **The callee's frame condition lands at the call node** `nC` in the caller's region `R`: every memory of
`F` comes from a caller's state at `nC` (`Abs`, `nC.J`), keeping its cells outside the callee's region at the
frame base `nC.o.sp - 8`, from 72 bytes below it to 16 above (`CKept`; `call_ndTCSX`'s `hcallee` fact, the
frame and the entry dropped). -/
abbrev CallFC (R : Region) (nC : ND) (F : MachineData → Prop) : Prop :=
  ∀ m, F m → ∃ mC σC c, Abs R nC.o mC σC ∧ nC.J σC c ∧ CKept R (nC.o.sp - 8) (-72) 16 mC m

end Spike.Lib.X64.Flow.Worker.PrintF

/-- info: 'Spike.Lib.X64.Flow.Worker.PrintF.CallFC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.PrintF.CallFC
