/-
**`XH` at the two landings off the spawned child's nodes** (x86-64; the twin of `Spike/Lib/A64HelloXHLand.lean`):
the `XH` parts of `SegRP.ZXObl`, so `XH`'s `PlacedSE` holds at `print`'s return landing and at `wc_worker`'s
return landing.

- `print`'s return landing (`hXR`): the source at a `print` control `c'` (`PrW`, so a model term or closed:
  `PrW.ext`) with the frame `uFrame` (`callI_inv`) placed: `print`'s frame condition keeps wc_worker's cells `-56`,
  `-48` (`framesPlaced_of_callFC`, the call's landing fact `CallFC`), where `j` and `c` are placed at the call
  (`UFramePl.uPlH_of`, its words from the call node's `wkJ` cells and the packet's `hv`, `hvu`).
- `wc_worker`'s return landing (`hXE`): the source at `cS2`'s `ret ()` (closed) at no frame.

- `wkSlots_outC`, `framesPlaced_of_callFC`: the worker's slots lie outside the callee's region of `CallFC`, so
  frames placed in them at the call stay placed at every machine of `print`'s frame condition.
- `uPl_call`: `uFrame` placed in wc_worker's slots at every state of the call node.
- `wcXObl_XH`: `WcXObl (XH Λ lbl)` in every `wc_worker` region, from `hv`, `hvu`; `zXObl_XH`: `ZXObl (XH Λ lbl)`.

## Differences from the AArch64 version

- `CallFC` keeps the caller's cells outside the callee's region at the frame base `nC.o.sp - 8`, from 72 below
  to 16 above (AArch64: at `nC.o.sp`, up to `0`), which `UFrameKeep.framesPlaced_of_hFC` does not take; its
  counterpart here is `framesPlaced_of_callFC` (with `wkSlots_outC` for `UFrameKeep.wkSlots_out`), new.
- The packet's words `3`, `4` are at the cells `-48`, `-56` (AArch64 `-64`, `-56`); the call block keeps them by
  `Body.wkC_slot` and `Body.wkSl_keep` (AArch64 `wkC_slot64`, `wkC_slot56`, which are not twinned).
- The region bounds are `R'.lo ≤ -56`, `-40 ≤ R'.hi` (AArch64 `-64`, `-48`).
-/
import Spike.Lib.X64HelloWorkerSegRPX
import Spike.Lib.X64HelloXH
import Spike.Lib.X64HelloUFrameKeep
import Spike.Lib.X64Hello1SFactsN
import Spike.Lib.Hello1Runs

namespace Spike.Lib.X64.HelloPh.XHLand

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib (Ctl LocalRunS FragS Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (ND CKept)
open Spike.Lib.X64.Flow.Worker (Body.wCall Body.wkC)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (workerCallH workerRestH envP wcP)
open Spike.Lib.X64HelloWorkerCallSrc (PrW KcW callI_inv)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.X64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (cS2)
open Spike.Lib.X64.Flow.Worker.Hello.SegRP (WcXObl ZXObl)
open Spike.Lib.X64.HelloPh.XH (XH)
open Spike.Lib.X64.HelloPh.UFrameKeep (WkSlotsK)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64}

/-- **The two slots are caller cells outside `CallFC`'s callee region**: with `%rsp = R.addr kc` at the call
state, the words `%rsp + 40` and `%rsp + 48` are `R.addr k` at `k = kc + 40`, `kc + 48`, above the callee's region
`R.callee (kc - 8) (-72) 16` (its top at `kc + 8`). -/
theorem wkSlots_outC {R : Region} {kc : Int} {sC : State} (hsp : sC.st.1.regs.get64 .rsp = R.addr kc)
    (hk8 : kc % 8 = 0) (hlo : R.lo ≤ kc + 40) (hhi : kc + 56 ≤ R.hi) :
    ∀ a, WkSlotsK sC a →
      ∃ k, R.Off k ∧ ¬ (R.callee (kc - 8) (-72) 16).Off (k - (kc - 8)) ∧ a = (R.addr k).toNat := by
  rintro a (rfl | rfl)
  · refine ⟨kc + 40, ⟨by omega, by omega, by omega⟩, fun h => ?_, by rw [hsp, Region.addr_add]; rfl⟩
    simp only [Region.callee, Region.Off] at h
    omega
  · refine ⟨kc + 48, ⟨by omega, by omega, by omega⟩, fun h => ?_, by rw [hsp, Region.addr_add]; rfl⟩
    simp only [Region.callee, Region.Off] at h
    omega

/-- **The frames placed at every machine of a callee's frame condition landing at the call** (`CallFC`): each
machine of `F'` has the call's machine `mC` (`Abs R nC.o mC σC`, `nC.J σC c`) with the caller's cells outside the
callee's region as in `mC`; `hU` places `frs σC c` in the worker's slots at any state of machine `mC`. -/
theorem framesPlaced_of_callFC {R : Region} {nC : ND} {F' : MachineData → Prop}
    {frs : Spike.Lib.X64.AS → Ctl → List TermRun.Frame}
    (hk8 : nC.o.sp % 8 = 0) (hlo : R.lo ≤ nC.o.sp + 40) (hhi : nC.o.sp + 56 ≤ R.hi)
    (hFC : Spike.Lib.X64.Flow.Worker.PrintF.CallFC R nC F')
    (hU : ∀ σC c mC, Spike.Lib.X64.Abs R nC.o mC σC → nC.J σC c → ∀ sC : State, sC.st.1 = mC →
      FramesPlacedInI Λ lbl sC (frs σC c) (WkSlotsK sC)) :
    ∀ s : State, F' s.st.1 → ∃ σC c, nC.J σC c ∧ FramesPlaced Λ lbl s (frs σC c) := by
  intro s hs
  obtain ⟨mC, σC, c, hA, hJ, hk⟩ := hFC _ hs
  let sC : State := { s with st := (mC, s.st.2) }
  have hsp : sC.st.1.regs.get64 .rsp = R.addr nC.o.sp := by
    show mC.regs.get64 .rsp = _
    rw [hA.regs]
    exact hA.so .rsp nC.o.sp (by simp [Spike.Lib.X64.SO.get])
  exact ⟨σC, c, hJ, ((hU σC c mC hA hJ sC rfl).of_cKept (s' := s) hk
    (wkSlots_outC hsp hk8 hlo hhi)).toFramesPlaced⟩

/-- **`uFrame` placed in wc_worker's slots at every state of the call node** (`uPlH_of` at the call's abstract
state; its cells `-48`, `-56` hold the packet's words `w.w4`, `w.w5`, which `w3`, `w4` represent). -/
theorem uPl_call {R : Region} (hlo : R.lo ≤ -56) (hhi : -40 ≤ R.hi) {w : Words} {rbp ra tp : BitVec 64}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    ∀ σC c mC, Spike.Lib.X64.Abs R
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R.addr 0))
        (KcW w0 w1 w2 w3 w4 n m)).o mC σC →
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R.addr 0))
        (KcW w0 w1 w2 w3 w4 n m)).J σC c → ∀ sC : State, sC.st.1 = mC →
      FramesPlacedInI Λ lbl sC [⟨"u", workerRestH, envP w0 w1 w2 w3 w4, [], .unit⟩] (WkSlotsK sC) := by
  rintro σC c mC hA ⟨⟨σ0, c0, fl, hJ0, rfl⟩, -⟩ sC rfl
  obtain ⟨-, -, -, -, -, h48, h56, -⟩ := hJ0
  obtain ⟨-, -, k48, k56⟩ := Spike.Lib.X64.Flow.Worker.Body.wkSl_keep (_root_.Executable.labels exe).label σ0
  refine Spike.Lib.X64.HelloPh.UFramePl.uPlH_of (Λ := Λ) hlo hhi hA ?_ ?_
  · rw [Spike.Lib.X64.Flow.Worker.Body.wkC_slot, k48, h48]; exact hv
  · rw [Spike.Lib.X64.Flow.Worker.Body.wkC_slot, k56, h56]; exact hvu

/-- **`WcXObl (XH Λ lbl)`** in a `wc_worker` region reaching `-56 .. -40`: at `print`'s return landing, `PlacedSE`
from `PrW.ext` and `uFrame` kept (`framesPlaced_of_callFC`); at `wc_worker`'s return landing, from `cS2`'s closed
`ret ()`. The other conjunct of `XH` is at no frame (`print`'s landing) or not at the call (`cS2`). -/
theorem wcXObl_XH {R' : Region} {F' : MachineData → Prop} (hlo : R'.lo ≤ -56) (hhi : -40 ≤ R'.hi)
    {rbp ra : BitVec 64} {w : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    WcXObl (XH Λ lbl) exe endPc R' F' rbp ra w tp w0 w1 w2 w3 w4 n m where
  hXR fr R'' F'' _ _ _ _ _ hFC σC c cE hJC hCT s c' hAt := by
    obtain ⟨-, -, -, -, σx, -, hD, ⟨⟨-, hP⟩, -⟩⟩ := hAt
    obtain ⟨-, rfl⟩ := callI_inv (by
      obtain ⟨-, rfl, -⟩ := hJC
      exact hCT)
    obtain ⟨σ', c'', -, hfp⟩ := framesPlaced_of_callFC (Λ := Λ) (lbl := lbl)
      (frs := fun _ _ => [⟨"u", workerRestH, envP w0 w1 w2 w3 w4, [], .unit⟩])
      (by show (-96 : Int) % 8 = 0; decide)
      (by show R'.lo ≤ -96 + 40; omega) (by show (-96 : Int) + 56 ≤ R'.hi; omega) hFC
      (uPl_call (exe := exe) hlo hhi hv hvu) s hD
    exact ⟨PlacedSE.of_ext hP.ext hfp, fun h => absurd h (List.cons_ne_nil _ _)⟩
  hXE s c h := by
    obtain ⟨y, -, -, -, -, σx, -, -, hJ⟩ := h
    cases y
    obtain ⟨rfl, -⟩ := hJ
    refine ⟨PlacedSE.of_ext (.inr rfl) Spike.Lib.X64.Flow.Hello1.SFactsN.framesPlaced_nil,
      fun _ c' hr ht => ?_⟩
    cases hr with
    | refl => simp [cS2, workerCallH] at ht
    | step hs _ => exact (Spike.Lib.Hello1Runs.localStepS_not_ret hs .unit rfl).elim

/-- **`ZXObl (XH Λ lbl)`** from the packet's `hv`, `hvu` (every `wc_worker` region reaches `-176 .. 8`). -/
theorem zXObl_XH {R : Region} {F : MachineData → Prop} {w : Words} {tp : BitVec 64}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    ZXObl (XH Λ lbl) exe endPc R F w tp w0 w1 w2 w3 w4 n m where
  hwcX _ _ _ hlo hhi _ _ _ _ _ := wcXObl_XH (by omega) (by omega) hv hvu

end Spike.Lib.X64.HelloPh.XHLand

/-- info: 'Spike.Lib.X64.HelloPh.XHLand.framesPlaced_of_callFC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.XHLand.framesPlaced_of_callFC

/-- info: 'Spike.Lib.X64.HelloPh.XHLand.wcXObl_XH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.XHLand.wcXObl_XH

/-- info: 'Spike.Lib.X64.HelloPh.XHLand.zXObl_XH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.XHLand.zXObl_XH
