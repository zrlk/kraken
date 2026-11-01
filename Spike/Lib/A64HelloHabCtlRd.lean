/-
**The control facts at `wc_rodata`'s heap abort** (AArch64; `HabCtl.HabCtlH`'s twin at `HelloRd.rX .abort`): every
source control of the allocator's
full exit in `wc_rodata` below its call invariant `J1`, at the frames `fs`, runs well, is placed, and meets the
heap abort's obligation (`HeapAbortOblA`) on the arena's cells and counter.

- `HabCtlRdH`: the premise (`HabCtlH` with `wXH ms lab J1 .abort` replaced by `rX ms lab L0 J1 .abort`).
- `HabCtlRdH.hctl`: its unfolding (by definition).

At the root (H0R/H0U, replacing `hCrd`) the instance is, for every `σC`,
`HabCtlRdH ((MSF) [FR]) (Ly).lab helloSrc (Ly).Λ (LB) (AR) [FR] (J1 σC)`.
-/
import Spike.Lib.A64HelloHabCtl
import Spike.Lib.A64HelloRodata

namespace Spike.Lib.A64.HelloPh.HabCtlRd

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Arena HeapAbortOblA)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.WakeWf (RunWf)

/-- **The controls' facts at `wc_rodata`'s heap abort** (`HelloRd.rX .abort`; `HabCtlH`'s twin):
every source control of the node runs well at the frames `fs`, its frames are placed, and the heap abort's
obligation holds. -/
def HabCtlRdH (ms : MemSide isaLSE2) (lab : String → Int64) (p : Prog) (Λ : Scc.Sem.Layout) (L0 : Lbl)
    (ar : Arena) (fs : List TermRun.Frame) (J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop) : Prop :=
  ∀ σ c0, (Spike.Lib.A64.Flow.HelloRd.rX ms lab L0 J1 .abort).J σ c0 →
    ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE Λ L0 s c0 fs) ∧
      HeapAbortOblA ar.cells ar.ctr c0

/-- **`HabCtlRdH` unfolded.** -/
theorem HabCtlRdH.hctl {ms : MemSide isaLSE2} {lab : String → Int64} {p : Prog} {Λ : Scc.Sem.Layout}
    {L0 : Lbl} {ar : Arena} {fs : List TermRun.Frame} {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    (h : HabCtlRdH ms lab p Λ L0 ar fs J1) :
    ∀ σ c0, (Spike.Lib.A64.Flow.HelloRd.rX ms lab L0 J1 .abort).J σ c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0 :=
  h

end Spike.Lib.A64.HelloPh.HabCtlRd

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlRd.HabCtlRdH.hctl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlRd.HabCtlRdH.hctl
