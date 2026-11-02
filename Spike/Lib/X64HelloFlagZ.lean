/-
**The flag fragment of hello.w's worker segment** (x86-64; the twin of `Spike/Lib/A64HelloFlagZ.lean`):
`FlagF cS`, every control a frame run of hello's source reaches accesses no untagged locative but the flag
`cS` (`X64WakeMappedRow.LabPtr`). The child's segment carries it as an extra fragment, discharged per node by
`SegRP.ZObl (FlagF cS)`.

- `FlagF cS`: every control a frame run reaches from here accesses no untagged locative but `cS`.

## Differences from the AArch64 version

- Only `FlagF` is twinned; `FlagF.run`, `FlagF.ptr`, `ZF`, `ZObl.flag` and `flag_of_pend` are not.
-/
import Spike.Lib.X64HelloWorkerSegRP
import Spike.Lib.X64WakeMappedRow

namespace Spike.Lib.X64.Flow.Worker.Hello.FlagZ

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Spike.Lib
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64WakeMappedRow (LabPtr)

/-- **The flag, closed under frame runs**: at every control a frame run of
hello's source reaches from `(c, fs)`, every untagged locative accessed is
`cS`. -/
def FlagF (cS : WeakMem.Address) : FragS isa := fun _ c fs =>
  ∀ c₁ fs₁, FrameRun helloSrc (c, fs) (c₁, fs₁) → ∀ sa, LabPtr c₁ sa → sa = cS

end Spike.Lib.X64.Flow.Worker.Hello.FlagZ

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.FlagZ.FlagF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.FlagZ.FlagF
