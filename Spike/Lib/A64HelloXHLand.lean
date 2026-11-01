/-
**`XH` at the two landings off the spawned child's nodes** (AArch64; rows 5j-wit-W, 5j-wit-E-call): the `XH` parts
of `SegRP.ZXObl`, so `XH`'s `PlacedSE` holds at `print`'s return landing and at `wc_worker`'s return landing.

- `print`'s return landing (`hXR`): the source at a `print` control `c'` (`PrW`, so a model term or closed:
  `PrW.ext`) with the frame `uFrame` (`callI_inv`) placed: `print`'s frame condition keeps wc_worker's cells `-64`,
  `-56` (`UFrameKeep.framesPlaced_of_hFC`, the call's landing fact `CallFC`), where `c` and `j` are placed at the
  call (`UFramePl.uPlH_of`, its words from the call node's `wkJ` slots and the packet's `hv`, `hvu`).
- `wc_worker`'s return landing (`hXE`): the source at `cS2`'s `ret ()` (closed) at no frame.

- `wkC_slot64`, `wkC_slot56`: the call block keeps wc_worker's cells `-64`, `-56`.
- `uPl_call`: `uFrame` placed in wc_worker's slots at every state of the call node.
- `wcXObl_XH`: `WcXObl (XH Λ lbl)` in every `wc_worker` region, from `hv`, `hvu`; `zXObl_XH`: `ZXObl (XH Λ lbl)`.
-/
import Spike.Lib.A64HelloWorkerSegRPX
import Spike.Lib.A64HelloXH
import Spike.Lib.A64HelloUFrameKeep
import Spike.Lib.Hello1Runs

namespace Spike.Lib.A64.HelloPh.XHLand

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib (Ctl LocalRunS FragS Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.Flow.Worker (Body.wCall Body.wkC)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (workerCallH workerRestH envP wcP)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW callI_inv)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (cS2)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (WcXObl ZXObl)
open Spike.Lib.A64.HelloPh.XH (XH)

/-- The call block keeps wc_worker's cell `-64`. -/
theorem wkC_slot64 (lab : Label → Int64) (σ : Spike.Lib.A64.Flow.AS) : (Body.wkC lab σ).slot (-64) = σ.slot (-64) := by
  rw [Spike.Lib.A64.Flow.Worker.Body.wkC_eq, Spike.Lib.A64.Flow.Worker.Body.wkE_run]; rfl

/-- The call block keeps wc_worker's cell `-56`. -/
theorem wkC_slot56 (lab : Label → Int64) (σ : Spike.Lib.A64.Flow.AS) : (Body.wkC lab σ).slot (-56) = σ.slot (-56) := by
  rw [Spike.Lib.A64.Flow.Worker.Body.wkC_eq, Spike.Lib.A64.Flow.Worker.Body.wkE_run]; rfl

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64}

/-- **`uFrame` placed in wc_worker's slots at every state of the call node** (`uPlH_of` at the call's abstract
state; its slots `-64`, `-56` hold the packet's words `w.w4`, `w.w5`, which `w3`, `w4` represent). -/
theorem uPl_call {R : Region} (hlo : R.lo ≤ -64) (hhi : -48 ≤ R.hi) {w : Words} {x29 ra tp : BitVec 64}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    ∀ σC c mC, Spike.Lib.A64.Flow.Abs R
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)).o mC σC →
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)).J σC c → ∀ sC : State, sC.st.1 = mC →
      FramesPlacedInI Λ lbl sC [⟨"u", workerRestH, envP w0 w1 w2 w3 w4, [], .unit⟩]
        (Spike.Lib.A64.HelloPh.UFrameKeep.WkSlotsK sC) := by
  rintro σC c mC hA ⟨⟨σ0, c0, hJ0, rfl⟩, -⟩ sC rfl
  obtain ⟨-, -, -, -, -, h64, h56, -⟩ := hJ0
  refine Spike.Lib.A64.HelloPh.UFramePl.uPlH_of (Λ := Λ) hlo hhi hA ?_ ?_
  · rw [wkC_slot64, h64]; exact hv
  · rw [wkC_slot56, h56]; exact hvu

/-- **`WcXObl (XH Λ lbl)`** in a `wc_worker` region reaching `-64 .. -48`: at `print`'s return landing, `PlacedSE`
from `PrW.ext` and `uFrame` kept (`framesPlaced_of_hFC`); at `wc_worker`'s return landing, from `cS2`'s closed
`ret ()`. The other two conjuncts of `XH` are at no frame (`print`'s landing) or not at the call (`cS2`). -/
theorem wcXObl_XH {R' : Region} {F' : MachineData → Prop} (hlo : R'.lo ≤ -64) (hhi : -48 ≤ R'.hi)
    {x29 ra : BitVec 64} {w : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    WcXObl (XH Λ lbl) exe endPc R' F' x29 ra w tp w0 w1 w2 w3 w4 n m where
  hXR fr R'' F'' _ _ _ _ _ _ hFC σC c cE _ hCT s c' hAt := by
    obtain ⟨-, -, -, -, σx, -, hD, ⟨-, -, hP⟩, -⟩ := hAt
    obtain ⟨-, rfl⟩ := callI_inv (by
      obtain ⟨-, rfl, -⟩ := ‹(Body.wCall _ _ _).J σC c›
      exact hCT)
    obtain ⟨σ', c'', -, hfp⟩ := Spike.Lib.A64.HelloPh.UFrameKeep.framesPlaced_of_hFC (Λ := Λ) (lbl := lbl)
      (frs := fun _ _ => [⟨"u", workerRestH, envP w0 w1 w2 w3 w4, [], .unit⟩])
      (by show (-96 : Int) % 8 = 0; decide)
      (by show R'.lo ≤ -96 + 32; omega) (by show (-96 : Int) + 48 ≤ R'.hi; omega) hFC
      (uPl_call (exe := exe) hlo hhi hv hvu) s hD
    exact ⟨PlacedSE.of_ext hP.ext hfp, fun h => absurd h (List.cons_ne_nil _ _)⟩
  hXE s c h := by
    obtain ⟨y, -, -, -, -, σx, -, -, hJ⟩ := h
    cases y
    obtain ⟨rfl, -⟩ := hJ
    refine ⟨PlacedSE.of_ext (.inr rfl) Spike.Lib.A64.Flow.Hello1.SFactsN.framesPlaced_nil,
      fun _ c' hr ht => ?_⟩
    cases hr with
    | refl => simp [cS2, workerCallH] at ht
    | step hs _ => exact (Spike.Lib.Hello1Runs.localStepS_not_ret hs .unit rfl).elim

/-- **`ZXObl (XH Λ lbl)`** from the packet's `hv`, `hvu` (every `wc_worker` region reaches `-192 .. 0`). -/
theorem zXObl_XH {R : Region} {F : MachineData → Prop} {w : Words} {tp : BitVec 64}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    ZXObl (XH Λ lbl) exe endPc R F w tp w0 w1 w2 w3 w4 n m where
  hwcX _ _ _ _ hlo hhi _ _ _ _ _ := wcXObl_XH (by omega) (by omega) hv hvu

end Spike.Lib.A64.HelloPh.XHLand

/-- info: 'Spike.Lib.A64.HelloPh.XHLand.wcXObl_XH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XHLand.wcXObl_XH

/-- info: 'Spike.Lib.A64.HelloPh.XHLand.zXObl_XH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XHLand.zXObl_XH
