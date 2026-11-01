/-
**The control facts at hello's heap abort** (AArch64; the named form of `HAbStub.wc_heapAbStubKH`'s `hctl`, wake's
`HAbStubK.hctl_c0W`): at the
allocator's full exit `HelloWc.wXH .abort` below `wc_main`'s entry invariant, the source control is not a
returned term at the frames `[]` and runs well (`RunWf`), is placed at every state (`PlacedSE`), and meets the
heap abort's obligation (`HeapAbortOblA`) on the arena's cells and counter.

- `HabCtlH`: the premise, at any memory side, labels, program, layout, start labels, arena, frames and node
  invariant.
- `HabCtlH.hctl`: it is `wc_heapAbStubKH`'s `hctl` (by definition).

At the root (`StartH0C.hello_hab_closed`) the instance is, for every `v m0 σC σ1`,
`HabCtlH ((MSF) []) (Ly).lab helloSrc (Ly).Λ (L0T (Ly).Λ) (WakeOD.arW hpw i) []
  (wcJ0 (mWC (Ly).lab σC (Jr1 v m0 σC)).J σ1)`.
-/
import Spike.Lib.A64HelloHAbStub

namespace Spike.Lib.A64.HelloPh.HabCtl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Arena HeapAbortOblA)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.Flow.HelloWc (wXH)

/-- **The control facts at `wXH .abort`** (row `5h-S-habctl`): every control `c0` of the allocator's full exit
below the node invariant `J1`, at the frames `fs`, is not a returned term when `fs = []`, runs well in `p`, is
placed at every state in `Λ` at `L0`, and meets `HeapAbortOblA` on `ar`'s cells and counter. -/
def HabCtlH (ms : MemSide isaLSE2) (lab : String → Int64) (p : Prog) (Λ : Scc.Sem.Layout) (L0 : Lbl)
    (ar : Arena) (fs : List TermRun.Frame) (J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop) : Prop :=
  ∀ σ c0, (wXH ms lab J1 .abort).J σ c0 →
    ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE Λ L0 s c0 fs) ∧
      HeapAbortOblA ar.cells ar.ctr c0

/-- **`HabCtlH` is `wc_heapAbStubKH`'s `hctl`.** -/
theorem HabCtlH.hctl {ms : MemSide isaLSE2} {lab : String → Int64} {p : Prog} {Λ : Scc.Sem.Layout} {L0 : Lbl}
    {ar : Arena} {fs : List TermRun.Frame} {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    (h : HabCtlH ms lab p Λ L0 ar fs J1) :
    ∀ σ c0, (wXH ms lab J1 .abort).J σ c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0 :=
  h

end Spike.Lib.A64.HelloPh.HabCtl

/-- info: 'Spike.Lib.A64.HelloPh.HabCtl.HabCtlH.hctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtl.HabCtlH.hctl
