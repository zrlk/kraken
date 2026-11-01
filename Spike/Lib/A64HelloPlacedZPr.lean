/-
**hello.w's `print` and its abort path placed** (the `hZP` / `hZA` fields of
`SegRP.WcObl` at `PlacedSE`): every state of `print`'s nodes and of its abort path runs at a `PrW` control (a
model term or closed, `PrW.ext`) on the one suspended frame `uFrame` (`callI_inv`), so `PlacedSE.of_ext` places
it once `uFrame` is placed. `uFrame` is placed in `wc_worker`'s slots of `c` and `j` (cells `-64`, `-56`) at the
call node (`UFramePl.uPlH_of`, the call node's slots `wkJ`'s, kept by the call block `Body.wkSl_keep`), and kept
at every state of the call's frame condition (`UFrameKeep.framesPlaced_of_hFC` at `PrintF.CallFC`); a block's
states stay in the frame condition (`FStable`).

- `blk_ofSt`, `nodeW_ofSt`, `abortObl_ofSt`: node obligations of a fragment holding at the node's controls on
  every state of the frame condition.
- `framesPlaced_pr`: `uFrame` placed at every state of a frame condition knowing the call.
- `zP_placed`, `zA_placed`: `WcObl`'s `hZP` and `hZA` at `PlacedSE`.
-/
import Spike.Lib.A64HelloPlacedZEnv
import Spike.Lib.A64HelloFlagObl
import Spike.Lib.A64HelloUFramePl
import Spike.Lib.A64HelloUFrameKeep

namespace Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (wcP)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW callI_inv)
open Spike.Lib.HelloW1 (uFrame)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.A64.Flow.Worker.Hello.FlagObl (cN_P)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (FramesPlaced PlacedSE)

/-! ## Node obligations on the frame condition's states -/

section Gen

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {X : Frag isaLSE2}

/-- **A block node inside a fragment holding at its controls on the frame condition's states** (a block's
states are in a stable frame condition). -/
theorem blk_ofSt {n : ND} {blk : List Directive} (hFS : FStable R F)
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
  sn1b := nodeW_ofSt fun _ _ hJ => ofEqS h hJ
  sn2 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ
  svc := nodeW_ofSt fun _ _ hJ => ofEqS h hJ.1
  sn5 := blk_ofSt hFS fun _ _ hJ => ofEqS h hJ
  sex := nodeW_ofSt fun _ _ hJ => ofEqS h hJ.1

end Gen

/-! ## `uFrame` placed inside `print` -/

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {w : Words} {x29 ra tp : BitVec 64}
  {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}

/-- **`uFrame` placed at every state of a frame condition knowing the call**: the call node's slots `-64`, `-56`
(`wkJ`'s `w.w4`, `w.w5`, kept by the call block) represent `c`'s and `j`'s words at the call (`uPlH_of`), and
the frame condition keeps them (`framesPlaced_of_hFC`). -/
theorem framesPlaced_pr {R' : Region} {F'' : MachineData → Prop} (hlo : R'.lo ≤ -64) (hhi : -48 ≤ R'.hi)
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat)
    (hFC : PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
      (KcW w0 w1 w2 w3 w4 n m)) F'')
    {s : State} (hs : F'' s.st.1) : FramesPlaced Λ lbl s [uFrame w0 w1 w2 w3 w4] := by
  have key := Spike.Lib.A64.HelloPh.UFrameKeep.framesPlaced_of_hFC (Λ := Λ) (lbl := lbl)
    (frs := fun _ _ => [uFrame w0 w1 w2 w3 w4]) (lo' := -96) (show (-96 : Int) % 8 = 0 by decide)
    (show R'.lo ≤ -96 + 32 by omega) (show -96 + 48 ≤ R'.hi by omega) hFC ?_ s hs
  · obtain ⟨-, -, -, h⟩ := key
    exact h
  · rintro σC c mC hA ⟨⟨σ0, c0, hJ0, rfl⟩, -⟩ sC rfl
    obtain ⟨-, -, -, -, -, h64, h56, -⟩ := hJ0
    obtain ⟨-, -, k64, k56⟩ := Body.wkSl_keep σ0
    refine Spike.Lib.A64.HelloPh.UFramePl.uPlH_of hlo hhi hA ?_ ?_
    · rw [Body.wkC_eq, Body.wkSl_eq, k64, h64]; exact hv
    · rw [Body.wkC_eq, Body.wkSl_eq, k56, h56]; exact hvu

/-- **`WcObl.hZP` at `PlacedSE`**: `print`'s nodes at `PrW` controls (`cN_P`) on `uFrame` (`callI_inv`), placed
on the frame condition's states (`framesPlaced_pr`). -/
theorem zP_placed {R' : Region} {F' : MachineData → Prop} (hlo : R'.lo ≤ -64) (hhi : -48 ≤ R'.hi)
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    ∀ fr (R'' : Region) (F'' : MachineData → Prop), R''.OK → R''.base.toNat % 16 = 0 → R''.lo ≤ -48 →
      0 ≤ R''.hi → FStable R'' F'' → (∀ m, F'' m → F' m) →
      PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)) F'' → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)).J σC c → CallToI helloSrc c cE fr →
      ∀ i, NodeZA (fun s c => PlacedSE Λ lbl s c [fr]) exe endPc R'' F''
        (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m) (fun _ => PrW w0 w2 n m) σC i)
        (PrintF.FA.blkN i) := by
  intro fr _ _ _ _ _ _ hFS _ hFC σC c cE hJ hci i
  obtain rfl := hJ.2.1
  obtain ⟨-, rfl⟩ := callI_inv hci
  exact blk_ofSt hFS fun _ _ hJ' s hs =>
    let ⟨_, hP⟩ := cN_P hJ'
    placedSE_prW hP (framesPlaced_pr hlo hhi hv hvu hFC hs)

/-- **`WcObl.hZA` at `PlacedSE`**: the abort path at a `PrW` control on `uFrame`, placed on the frame
condition's states. -/
theorem zA_placed {R' : Region} {F' : MachineData → Prop} (hlo : R'.lo ≤ -64) (hhi : -48 ≤ R'.hi)
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    ∀ fr (RA : Region) (FA : MachineData → Prop), RA.OK → RA.base.toNat % 16 = 0 → RA.lo ≤ -48 →
      0 ≤ RA.hi → FStable RA FA → (∀ m, FA m → F' m) →
      PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)) FA → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)).J σC c →
      CallToI helloSrc c cE fr → ∀ k c', PrW w0 w2 n m k c' →
        AbortObl (fun s c => PlacedSE Λ lbl s c [fr]) exe endPc RA FA c' := by
  intro fr _ _ _ _ _ _ hFS _ hFC σC c cE hJ hci k c' hP
  obtain rfl := hJ.2.1
  obtain ⟨-, rfl⟩ := callI_inv hci
  exact abortObl_ofSt hFS fun s hs => placedSE_prW hP (framesPlaced_pr hlo hhi hv hvu hFC hs)

end Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.framesPlaced_pr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.framesPlaced_pr

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zP_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zP_placed

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zA_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zA_placed
