/-
**wake.w on AArch64, the pre-spawn relation with a source invariant**: `Pre1T.inv`, any `Pre1T … R1` strengthened by an
invariant `V` that holds at the load's source start and is kept along
`Pre1T.step`'s source runs, as a `Pre1T` at `fun d s => R1 d s ∧ V d s`
(same pattern as `Spike.Lib.WakeNoObs.Pre1T.noObs`).

Used for `hlt0` at main's spawn: `V` is the strict view bound of main's
source thread below the memory size (`Spike.Lib.SpawnViewLt.SpawnVLt`),
whose per-step preservation lemmas come from `SpawnViewLt`'s side.
-/
import Spike.Lib.WakePreTi

namespace Spike.Lib.WakePreInv

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeT1 Spike.Lib.WakeA64 Spike.Lib.WakePre
open Spike.Lib.WakePreTi

namespace Pre1T

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
  {R1 : Cfg → TermRun.Cfg → Prop} {Ab Ac : State → Prop}

/-- **`Pre1T` with an invariant `V`**: from `R1`'s obligations, `V` at the
load's source start (`hinit`) and along each one-slot step's source run
(`hstep`, which may use `R1` on both sides), the obligations at
`R1 ∧ V`. -/
theorem inv (O : Pre1T arch Λ B asm E R1 Ab Ac) (V : Cfg → TermRun.Cfg → Prop)
    (hinit : ∀ d s0, (target (kernel 1) E).load asm Λ = some d → (wakeS arch).init s0 → R1 d s0 → V d s0)
    (hstep : ∀ tid d es d' s s', R1 d s → V d s → d.1.threads.size = d.2.slots.size →
      (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' →
      (wakeS arch).Run s (obs es) s' → R1 d' s' → V d' s') :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ V d s) Ab Ac where
  init d hd := by
    obtain ⟨s0, hi, hR⟩ := O.init d hd
    exact ⟨s0, hi, hR, hinit d s0 hd hi hR⟩
  step tid d es d' s h hn hs := by
    obtain ⟨s', hr, hR', hn'⟩ := O.step tid d es d' s h.1 hn hs
    exact ⟨s', hr, ⟨hR', hstep tid d es d' s s' h.1 h.2 hn hs hr hR'⟩, hn'⟩
  progress d s h hn hc := O.progress d s h.1 hn hc
  progressClone d u s h hu hpl hn hc := O.progressClone d u s h.1 hu hpl hn hc
  abort tr d s tid es d' k hr h hn hti hs hk := O.abort tr d s tid es d' k hr h.1 hn hti hs hk
  wit d s h hn := O.wit d s h.1 hn
  held d s h hn := O.held d s h.1 hn
  ti0 := O.ti0
  tiStep tid d es d' s pre h hn hs hti := O.tiStep tid d es d' s pre h.1 hn hs hti

/-- **`Pre1T.inv` at a source-only invariant**: `V` true at every source
start and kept by every source run. -/
theorem invSrc (O : Pre1T arch Λ B asm E R1 Ab Ac) (V : TermRun.Cfg → Prop)
    (hinit : ∀ s0, (wakeS arch).init s0 → V s0)
    (hrun : ∀ s tr s', (wakeS arch).Run s tr s' → V s → V s') :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ V s) Ab Ac :=
  inv O (fun _ s => V s) (fun _ s0 _ hi _ => hinit s0 hi)
    (fun _ _ _ _ s s' _ hV _ _ hr _ => hrun s _ s' hr hV)

end Pre1T

/-- info: 'Spike.Lib.WakePreInv.Pre1T.inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Pre1T.inv

/-- info: 'Spike.Lib.WakePreInv.Pre1T.invSrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Pre1T.invSrc

end Spike.Lib.WakePreInv
