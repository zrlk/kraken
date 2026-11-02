/-
**hello.w on x86-64: `wc_worker`'s invariant at `.entry`** (the twin of
`Spike/Lib/A64HelloWorkerSeg.lean`): after the stack-checked prologue
(`Wk.wcPro`, frame 80) the six words are in the frame's cells `-16 … -56`
(`-8 … -48(%rbp)`), the caller's `%rbp` and the return address in the
frame record `-8`/`0`; the tail's exit (`HelloTail.E`,
`Spike/Lib/X64HelloWkTail.lean`) is wake's (`Wake.WkTailW.E`).

- `wkJ`: the invariant at `.entry`: the six words, the caller's `%rbp`
  `rbp0` at `-8`, the return address `ra` at `0`, the thread pointer `tp`,
  `%rbp` at the saved `%rbp` (`sp - 8`, `sp` the entry `%rsp`);
- `tailE_eq`: `HelloTail.E … .ret = Wake.WkTailW.E … .ret`.

## Differences from the AArch64 version

- The words sit at `-16 … -56` (`%rbp`-relative spills, the frame record
  `%rbp`/return address at `-8`/`0`); A64: `-96 … -56`, `x29`/`x30` at
  `-16`/`-8`. The words `c`, `j` (`w4`, `w5`) are at `-48`/`-56`, where the
  tail reads them (`HelloTail.JI`).
- `wkJ` carries the entry `%rsp` `sp` (`%rbp = sp - 8`), the ghost of the
  tail's nodes (`HelloTail.N … sp`, as wake's `WkTailW.N`); the thread
  pointer is `fsBase` (A64: `TPIDR_EL0`).
- A64's `seg_wcWorkerH`, `seg_wcWorkerHA` (dead) are not twinned.
-/
import Spike.Lib.X64HelloWorker
import Spike.Lib.X64HelloChild
import Spike.Lib.X64HelloWkTail
import Spike.Lib.X64WakeWorker

namespace Spike.Lib.X64.Flow.Worker.Hello.Wk

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)

/-- **`wc_worker`'s invariant at `.entry`**: the source at `c0`, the six
words in the cells `-16 … -56`, the caller's `%rbp` and the return address
at `-8`/`0`, the thread pointer `tp`, `%rbp` at the saved `%rbp` (`sp` the
entry `%rsp`). -/
def wkJ (c0 : Ctl) (w : Words) (rbp0 ra tp sp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.slot (-16) = w.w0 ∧ σ.slot (-24) = w.w1 ∧ σ.slot (-32) = w.w2 ∧ σ.slot (-40) = w.w3 ∧
    σ.slot (-48) = w.w4 ∧ σ.slot (-56) = w.w5 ∧ σ.slot (-8) = rbp0 ∧ σ.slot 0 = ra ∧
    σ.regs.fsBase.toBitVec = tp ∧ σ.regs.rbp.toBitVec = sp - 8#64

/-- **The hello copy's exit is wake's.** -/
theorem tailE_eq (c2 : Ctl) (rbp0 ra tp : BitVec 64) :
    HelloTail.E c2 rbp0 ra tp .ret = Wake.WkTailW.E c2 rbp0 ra tp .ret := rfl

end Spike.Lib.X64.Flow.Worker.Hello.Wk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Wk.tailE_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Wk.tailE_eq
