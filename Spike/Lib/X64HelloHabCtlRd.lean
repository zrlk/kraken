/-
**The control facts at `wc_rodata`'s heap abort** (x86-64; the twin of
`Spike/Lib/A64HelloHabCtlRd.lean`, at `X64.Flow.HelloRd.rX .abort`): every
source control of the allocator's full exit in `wc_rodata` below its call
invariant `J1`, at the frames `fs`, runs well, is placed, and meets the heap
abort's obligation (`HeapAbortOblA`) on the arena's cells and counter.

- `HabCtlRdH`: the premise (`HabCtlH` with the wake node replaced by
  `rX ms lab L0 R J1 .abort`).
- `HabCtlRdH.hctl`: its unfolding (by definition).

Where x86-64 differs from AArch64: x86-64's `HelloRd.rX` also takes the
region `R` (its `.x13` exit reads `%rbp` against `R`), so `HabCtlRdH` takes
`R` as well; the `.abort` node does not read it. The memory side is over
`isa` (x86-64), the abstract state `Spike.Lib.X64.AS`, and `RunWf` /
`PlacedSE` are the x86-64 consumer's (`Spike.Lib.X64.WakeWf`,
`Spike.Lib.X64ConsumerS`).
-/
import Spike.Lib.X64HelloRodata
import Spike.Lib.X64WakeWf

namespace Spike.Lib.X64.HelloPh.HabCtlRd

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Arena HeapAbortOblA Region)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.WakeWf (RunWf)

/-- **The controls' facts at `wc_rodata`'s heap abort** (`HelloRd.rX .abort`; `HabCtlH`'s twin):
every source control of the node runs well at the frames `fs`, its frames are placed, and the heap abort's
obligation holds. -/
def HabCtlRdH (ms : MemSide isa) (lab : String → Int64) (p : Prog) (Λ : Scc.Sem.Layout) (L0 : Lbl)
    (R : Region) (ar : Arena) (fs : List TermRun.Frame) (J1 : Spike.Lib.X64.AS → Ctl → Prop) : Prop :=
  ∀ σ c0, (Spike.Lib.X64.Flow.HelloRd.rX ms lab L0 R J1 .abort).J σ c0 →
    ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE Λ L0 s c0 fs) ∧
      HeapAbortOblA ar.cells ar.ctr c0

/-- **`HabCtlRdH` unfolded.** -/
theorem HabCtlRdH.hctl {ms : MemSide isa} {lab : String → Int64} {p : Prog} {Λ : Scc.Sem.Layout}
    {L0 : Lbl} {R : Region} {ar : Arena} {fs : List TermRun.Frame} {J1 : Spike.Lib.X64.AS → Ctl → Prop}
    (h : HabCtlRdH ms lab p Λ L0 R ar fs J1) :
    ∀ σ c0, (Spike.Lib.X64.Flow.HelloRd.rX ms lab L0 R J1 .abort).J σ c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0 :=
  h

end Spike.Lib.X64.HelloPh.HabCtlRd

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH.hctl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH.hctl
