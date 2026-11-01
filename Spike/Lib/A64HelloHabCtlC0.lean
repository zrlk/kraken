/-
**`HabCtlH` at `wc_main`'s heap abort below `c0H`** (AArch64;
`5h-S-habctl-L1`; the twin of wake's `HAbStubK.hctl_c0W`): below `wc_main`'s entry invariant
`wcJ0 (mWC lab σC Jr).J σ1` whose caller controls are main's box allocation `c0H w0 w1 w2 mw` (`hJr`), the
allocator's full exit holds the counter at a count `o` crossing the cells (`Jfull`; one `int`, two units `hu`),
so its control is `c0H` holding `o`: not a returned term, it runs well (`WakeSrcCtl.new_ctl`), it is placed where
`c0H` is (`hpl0`), and it meets the heap abort's obligation (`HeapAbortOblA`).

Generic in the placement `L0`, the memory side, the arena and `Jr`: level 0 at `L0T`, level 1 at
`upd (L0T Λ) l b` (`StartH0CL.hello_hab_closedL`; `hpl0` there is row `L1-c0pl`).

- `habCtlH_c0H`: the instance.
- `habCtlH_jr1L`: at level 1's `Land.Jr1LH hpw i0 l b` (`hJr := fun _ _ h => h.1`).
-/
import Spike.Lib.A64HelloHabCtl
import Spike.Lib.A64HelloMain
import Spike.Lib.HelloMainPreSrc
import Spike.Lib.A64WakeSrcCtl
import Spike.Lib.A64WakeWcWf
import Spike.Lib.HelloSrc
import Spike.Lib.A64HelloLand1

namespace Spike.Lib.A64.HelloPh.HabCtlC0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Arena HeapAbortOblA)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcJ0)
open Spike.Lib.A64.HelloPh.HabCtl (HabCtlH)
open Spike.Lib.HelloMainPreSrc (c0H c0H_term boxTermH)
open Spike.Lib.HelloSrc (helloSrc)

/-- **`HabCtlH` below `c0H`** (`hctl_c0W`'s twin): at `wXH .abort` below `wc_main`'s entry invariant whose caller
controls are `c0H w0 w1 w2 mw` (`hJr`), given the memory side's counter, cells and units (`hctr`, `hcells`, `hu`)
and `c0H`'s placement at `L0` (`hpl0`). -/
theorem habCtlH_c0H {ms : Spike.Lib.MemSide isaLSE2} {lab : String → Int64} {Λ : Scc.Sem.Layout} {L0 : Lbl}
    {ar : Arena} {σC σ1 : Spike.Lib.A64.Flow.AS} {Jr : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {w0 w1 w2 mw : TermRun.Word}
    (hJr : ∀ σ c, Jr σ c → c = c0H w0 w1 w2 mw) (hctr : ms.ctr = ar.ctr) (hcells : ms.cells = ar.cells)
    (hu : ms.units 1 .int = 2) (hpl0 : ∀ s, PlacedSE Λ L0 s (c0H w0 w1 w2 mw) []) :
    HabCtlH ms lab helloSrc Λ L0 ar [] (wcJ0 (mWC lab σC Jr).J σ1) := by
  rintro σ c0 ⟨-, -, q, hfull, σe, -, σx, hJ, -⟩
  have hq : q.1.c0 = c0H w0 w1 w2 mw := hJr σx _ hJ
  have hctl := Spike.Lib.WakeSrcCtl.new_ctl (p := helloSrc) (c0H_term w0 w1 w2 mw)
  obtain ⟨T, ht⟩ := q.2.term; rw [hq, c0H_term] at ht
  obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
  have hev := q.2.ev; rw [hq, ← (Op.new.inj ha).1] at hev
  have hz : TermRun.evalAt (c0H w0 w1 w2 mw).env (.var "z") = some (.int, [TermRun.cst (.num 0)]) := rfl
  have hτ : q.1.τ = .int := by rw [hz] at hev; exact (Prod.mk.inj (Option.some.inj hev)).1.symm
  rcases hfull with ⟨-, hn⟩ | ⟨o, rfl, -, hlt⟩
  · rw [q.2.one] at hn; exact absurd hn (by decide)
  rw [q.2.one, hτ, hu] at hlt; rw [hq]
  refine ⟨⟨fun _ => hctl.1, Spike.Lib.A64.WakePh.WcWf.RunWf.hold hctl.2⟩,
    fun s => Spike.Lib.A64.WakePh.WcWf.PlacedSE.hold.2 (hpl0 s), fun old h => ?_⟩
  obtain ⟨hle, hw⟩ := h (.inr ⟨"o", .var "z", boxTermH, _, rfl⟩)
  have he := hw _ (by rw [← hctr]; rfl)
  have ho : o.toNat = old := by simpa [TermRun.cst, Promises.TVal.mk0] using he
  exact .inr ⟨"o", .var "z", _, .int, TermRun.cst (.num 0), ⟨_, rfl⟩, rfl, rfl, hle, by rw [← hcells]; omega⟩

/-- **`HabCtlH` at level 1** (row `5h-S-habctl-L1`): below `Land.Jr1LH hpw i0 l b` (its control is `c0H` at
rodata's slice words and main's id `mwH`), at any placement `L0` where that `c0H` is placed. -/
theorem habCtlH_jr1L {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat) {l : WeakMem.AllocLabel} {b : Nat}
    {ms : Spike.Lib.MemSide isaLSE2} {lab : String → Int64} {Λ : Scc.Sem.Layout} {L0 : Lbl} {ar : Arena}
    {σC σ1 : Spike.Lib.A64.Flow.AS} (hctr : ms.ctr = ar.ctr) (hcells : ms.cells = ar.cells)
    (hu : ms.units 1 .int = 2)
    (hpl0 : ∀ s, PlacedSE Λ L0 s (c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13))
      Spike.Lib.A64.HelloPh.Land.mwH) []) :
    HabCtlH ms lab helloSrc Λ L0 ar [] (wcJ0 (mWC lab σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1) :=
  habCtlH_c0H (fun _ _ h => h.1) hctr hcells hu hpl0

end Spike.Lib.A64.HelloPh.HabCtlC0

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlC0.habCtlH_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlC0.habCtlH_c0H

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlC0.habCtlH_jr1L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlC0.habCtlH_jr1L
