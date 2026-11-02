/-
**hello.w's `print` and its abort path placed** (x86-64; the twin of `Spike/Lib/A64HelloPlacedZPr.lean`): the
`hZP` / `hZA` fields of `SegRP.WcObl` at `PlacedSE`. Every state of `print`'s nodes and of its abort path runs at
a `PrW` control (a model term or closed, `PrW.ext`) on the one suspended frame `uFrame` (`callI_inv`), so
`PlacedSE.of_ext` places it once `uFrame` is placed. `uFrame` is placed in `wc_worker`'s slots of `c` and `j`
(cells `-48`, `-56`) at the call node (`XHLand.uPl_call`), and kept at every state of the call's frame condition
(`XHLand.framesPlaced_of_callFC` at `PrintF.CallFC`); a block's states stay in the frame condition (`FStable`).

- `blk_ofSt`, `nodeW_ofSt`, `ofEqS`, `abortObl_ofSt`: node obligations of a fragment holding at the node's controls
  on every state of the frame condition.
- `framesPlaced_pr`: `uFrame` placed at every state of a frame condition knowing the call.
- `zP_placed`, `zA_placed`: `WcObl`'s `hZP` and `hZA` at `PlacedSE`.

## Differences from the AArch64 version

- `framesPlaced_pr` is `X64HelloXHLand`'s `framesPlaced_of_callFC` and `uPl_call` (AArch64: `UFrameKeep`'s
  `framesPlaced_of_hFC` and `UFramePl.uPlH_of` inline): x86-64's `CallFC` keeps the caller's cells at the frame
  base `nC.o.sp - 8`, from 72 below to 16 above.
- The slots are the cells `-48`, `-56` (AArch64 `-64`, `-56`), so the region bounds are `R'.lo ≤ -56`,
  `-40 ≤ R'.hi` (AArch64 `-64`, `-48`).
- `WcObl`'s `hZP` / `hZA` regions have no alignment premise and their bounds are x86-64's (`-40` / `-24`, `16`);
  `print`'s nodes take the call's offset `-96` (`PrintF.cN … (-96)`).
- The abort path's obligation has x86-64's nodes (`AbortObl`: `sys` for AArch64's `svc`, no `sn1b`).
-/
import Spike.Lib.X64HelloPlacedZEnv
import Spike.Lib.X64HelloFlagObl
import Spike.Lib.X64HelloXHLand

namespace Spike.Lib.X64.Flow.Worker.Hello.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (wcP)
open Spike.Lib.X64HelloWorkerCallSrc (PrW KcW callI_inv)
open Spike.Lib.X64HelloW1 (uFrame)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.X64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.X64.Flow.Worker.Hello.FlagObl (cN_P)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (FramesPlaced PlacedSE)

/-! ## Node obligations on the frame condition's states -/

section Gen

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {X : Frag isa}

/-- **A block node inside a fragment holding at its controls on the frame condition's states** (a block's
states are in a stable frame condition). -/
theorem blk_ofSt {n : ND} {blk : List (Directive × Nat)} (hFS : FStable R F)
    (h : ∀ σ c, n.J σ c → ∀ s : State, F s.st.1 → X s c) : NodeZA X exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ hs hJ _ _ _ _ hD => ⟨h σ c hJ _ (hFS _ _ hs hD), fun _ h => h⟩

/-- **A node inside a fragment holding at its controls on the frame condition's states.** -/
theorem nodeW_ofSt {n : ND} (h : ∀ σ c, n.J σ c → ∀ s : State, F s.st.1 → X s c) :
    NodeW X (fun _ _ => False) exe endPc R F n :=
  fun s c hA => ⟨by obtain ⟨-, -, -, -, σ, -, hF, hJ⟩ := hA; exact h σ c hJ s hF, fun _ h => h⟩

/-- A fragment at `c0` on the frame condition's states is one at every control equal to it. -/
theorem ofEqS {c c0 : Ctl} (h : ∀ s : State, F s.st.1 → X s c0) (e : c = c0) : ∀ s : State, F s.st.1 → X s c :=
  e ▸ h

/-- **The abort path inside a fragment holding at its control on the frame condition's states.** -/
theorem abortObl_ofSt {c0 : Ctl} (hFS : FStable R F) (h : ∀ s : State, F s.st.1 → X s c0) :
    AbortObl X exe endPc R F c0 where
  de := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ.1
  dt1 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ.1
  dj1 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ.1
  dt2 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ.1
  dj2 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ.1
  dt3 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ.1
  dj3 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ.1
  dt4 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ.1
  dg4 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ
  se := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ
  sn1 := nodeW_ofSt fun _ _ hJ => ofEqS h hJ
  sn2 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ
  sys := nodeW_ofSt fun _ _ hJ => ofEqS h hJ.1
  sn5 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ
  sex := nodeW_ofSt fun _ _ hJ => ofEqS h hJ.1

end Gen

/-! ## `uFrame` placed inside `print` -/

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {w : Words}
  {rbp ra tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}

/-- **`uFrame` placed at every state of a frame condition knowing the call**: the call node's cells `-48`, `-56`
(`wkJ`'s `w.w4`, `w.w5`, kept by the call block) represent `c`'s and `j`'s words at the call (`uPl_call`), and
the frame condition keeps them (`framesPlaced_of_callFC`). -/
theorem framesPlaced_pr {R' : Region} {F'' : MachineData → Prop} (hlo : R'.lo ≤ -56) (hhi : -40 ≤ R'.hi)
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat)
    (hFC : PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label
      (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0)) (KcW w0 w1 w2 w3 w4 n m)) F'')
    {s : State} (hs : F'' s.st.1) : FramesPlaced Λ lbl s [uFrame w0 w1 w2 w3 w4] := by
  obtain ⟨-, -, -, h⟩ := Spike.Lib.X64.HelloPh.XHLand.framesPlaced_of_callFC (Λ := Λ) (lbl := lbl)
    (frs := fun _ _ => [uFrame w0 w1 w2 w3 w4]) (show (-96 : Int) % 8 = 0 by decide)
    (show R'.lo ≤ -96 + 40 by omega) (show -96 + 56 ≤ R'.hi by omega) hFC
    (Spike.Lib.X64.HelloPh.XHLand.uPl_call (exe := exe) hlo hhi hv hvu) s hs
  exact h

/-- **`WcObl.hZP` at `PlacedSE`**: `print`'s nodes at `PrW` controls (`cN_P`) on `uFrame` (`callI_inv`), placed
on the frame condition's states (`framesPlaced_pr`). -/
theorem zP_placed {R' : Region} {F' : MachineData → Prop} (hlo : R'.lo ≤ -56) (hhi : -40 ≤ R'.hi)
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    ∀ fr (R'' : Region) (F'' : MachineData → Prop), R''.OK → R''.lo ≤ -40 → 16 ≤ R''.hi →
      FStable R'' F'' → (∀ m, F'' m → F' m) →
      PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label
        (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0)) (KcW w0 w1 w2 w3 w4 n m)) F'' → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
        (KcW w0 w1 w2 w3 w4 n m)).J σC c → CallToI helloSrc c cE fr →
      ∀ i, NodeZA (fun s c => PlacedSE Λ lbl s c [fr]) exe endPc R'' F''
        (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m) (fun _ => PrW w0 w2 n m) (-96)
          σC i) (PrintF.FA.blkN i) := by
  intro fr _ _ _ _ _ hFS _ hFC σC c cE hJ hci i
  obtain rfl := hJ.2.1
  obtain ⟨-, rfl⟩ := callI_inv hci
  exact blk_ofSt hFS fun _ _ hJ' s hs =>
    let ⟨_, hP⟩ := cN_P hJ'
    placedSE_prW hP (framesPlaced_pr hlo hhi hv hvu hFC hs)

/-- **`WcObl.hZA` at `PlacedSE`**: the abort path at a `PrW` control on `uFrame`, placed on the frame
condition's states. -/
theorem zA_placed {R' : Region} {F' : MachineData → Prop} (hlo : R'.lo ≤ -56) (hhi : -40 ≤ R'.hi)
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    ∀ fr (RA : Region) (FA : MachineData → Prop), RA.OK → RA.lo ≤ -24 → 16 ≤ RA.hi →
      FStable RA FA → (∀ m, FA m → F' m) →
      PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label
        (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0)) (KcW w0 w1 w2 w3 w4 n m)) FA → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
        (KcW w0 w1 w2 w3 w4 n m)).J σC c →
      CallToI helloSrc c cE fr → ∀ k c', PrW w0 w2 n m k c' →
        AbortObl (fun s c => PlacedSE Λ lbl s c [fr]) exe endPc RA FA c' := by
  intro fr _ _ _ _ _ hFS _ hFC σC c cE hJ hci k c' hP
  obtain rfl := hJ.2.1
  obtain ⟨-, rfl⟩ := callI_inv hci
  exact abortObl_ofSt hFS fun s hs => placedSE_prW hP (framesPlaced_pr hlo hhi hv hvu hFC hs)

end Spike.Lib.X64.Flow.Worker.Hello.PlacedZ

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.framesPlaced_pr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.framesPlaced_pr

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zP_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zP_placed

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zA_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zA_placed
