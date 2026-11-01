/-
**hello.w's worker frame kept inside `print`** (AArch64; row 5j-wit-W class 3, part (2)): at every
state `print` reaches from the worker's call of it, the worker's frame `uFrame` (the continuation `workerRestH`,
free variables `c` and `j`) is still placed. Its places are wc_worker's cells `-64` and `-56`
(`A64HelloUFramePl.wkSlots`: at the call state, `sp` at the call node's `-96`, the words `sp + 32` and `sp + 40`).
`print`'s region is `R.callee kc lo' 0`, below the call's `sp`, so the cells stay outside it and the call's
frame condition keeps them (`CKept`).

- `WkSlotsK`: the slot set `wkSlots`, unfolded (definitionally `wkSlots sC`; stated here so that this file
  does not depend on `hello-er`).
- `wkSlots_out`: the two slots are `R.addr k` for cells `k = kc + 32`, `kc + 40` of `R` outside the callee's
  region, given `sp = R.addr kc` at the call state.
- `framesPlacedInI_kept`, `framesPlaced_kept`: frames placed in those slots at the call state `sC` stay placed at
  any state `s` whose machine keeps the caller's cells outside the callee's region (`FramesPlacedInI.of_cKept`).
- `framesPlaced_of_hFC`: at every state of a frame condition `F'` that knows the call (`hFC` shape: the
  call's machine `mC`, `Abs R nC.o mC σC`, `nC.J σC c`, the cells outside `R.callee nC.o.sp lo' 0` as in
  `mC`), the frames `frs σC c` are placed, given part (1) (`hU`, `uPlH_of`) at the call state.
-/
import Spike.Lib.A64FramesPlacedI

namespace Spike.Lib.A64.HelloPh.UFrameKeep

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Region Ctl)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (FramesPlaced FramesPlacedInI)
open Spike.Lib.A64.Flow (ND CKept)

/-- **wc_worker's slots of `c` and `j`** at the call state `s` (`sp` at the call node's `-96`): the words
`sp + 32`, `sp + 40` (cells `-64`, `-56`); `UFramePl.wkSlots`, unfolded. -/
abbrev WkSlotsK (s : State) (a : Nat) : Prop :=
  a = (s.st.1.regs.SP.toBitVec + 32#64).toNat ∨ a = (s.st.1.regs.SP.toBitVec + 40#64).toNat

/-- **The two slots are caller cells outside the callee's region**: with `sp = R.addr kc` at the call state, the
words `sp + 32` and `sp + 40` are `R.addr k` at `k = kc + 32`, `kc + 40`, cells of `R` above the callee's region
`R.callee kc lo' 0`. -/
theorem wkSlots_out {R : Region} {kc lo' : Int} {sC : State} (hsp : sC.st.1.regs.SP.toBitVec = R.addr kc)
    (hk8 : kc % 8 = 0) (hlo : R.lo ≤ kc + 32) (hhi : kc + 48 ≤ R.hi) :
    ∀ a, WkSlotsK sC a → ∃ k, R.Off k ∧ ¬ (R.callee kc lo' 0).Off (k - kc) ∧ a = (R.addr k).toNat := by
  rintro a (rfl | rfl)
  · refine ⟨kc + 32, ⟨by omega, by omega, by omega⟩, fun h => ?_, by rw [hsp, Region.addr_add]; rfl⟩
    simp only [Region.callee, Region.Off] at h
    omega
  · refine ⟨kc + 40, ⟨by omega, by omega, by omega⟩, fun h => ?_, by rw [hsp, Region.addr_add]; rfl⟩
    simp only [Region.callee, Region.Off] at h
    omega

variable {Λ : Scc.Sem.Layout} {lbl : Lbl}

/-- **Frames placed in the worker's slots stay placed** at any state whose machine keeps the caller's cells
outside the callee's region (`CKept`; `FramesPlacedInI.of_cKept` with `wkSlots_out`). -/
theorem framesPlacedInI_kept {R : Region} {kc lo' : Int} {sC s : State} {fs : List TermRun.Frame}
    (hsp : sC.st.1.regs.SP.toBitVec = R.addr kc) (hk8 : kc % 8 = 0) (hlo : R.lo ≤ kc + 32) (hhi : kc + 48 ≤ R.hi)
    (h : FramesPlacedInI Λ lbl sC fs (WkSlotsK sC)) (hk : CKept R kc lo' 0 sC.st.1 s.st.1) :
    FramesPlacedInI Λ lbl s fs (WkSlotsK sC) :=
  h.of_cKept hk (wkSlots_out hsp hk8 hlo hhi)

/-- **`framesPlacedInI_kept` as `FramesPlaced`** (the form `PlacedSE.of_ext` asks). -/
theorem framesPlaced_kept {R : Region} {kc lo' : Int} {sC s : State} {fs : List TermRun.Frame}
    (hsp : sC.st.1.regs.SP.toBitVec = R.addr kc) (hk8 : kc % 8 = 0) (hlo : R.lo ≤ kc + 32) (hhi : kc + 48 ≤ R.hi)
    (h : FramesPlacedInI Λ lbl sC fs (WkSlotsK sC)) (hk : CKept R kc lo' 0 sC.st.1 s.st.1) :
    FramesPlaced Λ lbl s fs :=
  (framesPlacedInI_kept hsp hk8 hlo hhi h hk).toFramesPlaced

/-- **The frames placed at every state of a frame condition that knows the call** (`hFC` shape): each
machine `m` of `F'` has the call's machine `mC` (`Abs R nC.o mC σC`, `nC.J σC c`) with the caller's cells outside
`R.callee nC.o.sp lo' 0` as in `mC`; part (1) (`hU`) places `frs σC c` in the worker's slots at any state of
machine `mC`. The call's `sp` is `Abs`'s (`SORel.sp`). -/
theorem framesPlaced_of_hFC {R : Region} {nC : ND} {lo' : Int} {F' : MachineData → Prop}
    {frs : Spike.Lib.A64.Flow.AS → Ctl → List TermRun.Frame}
    (hk8 : nC.o.sp % 8 = 0) (hlo : R.lo ≤ nC.o.sp + 32) (hhi : nC.o.sp + 48 ≤ R.hi)
    (hFC : ∀ m, F' m → ∃ mC σC c, Spike.Lib.A64.Flow.Abs R nC.o mC σC ∧ nC.J σC c ∧ CKept R nC.o.sp lo' 0 mC m)
    (hU : ∀ σC c mC, Spike.Lib.A64.Flow.Abs R nC.o mC σC → nC.J σC c → ∀ sC : State, sC.st.1 = mC →
      FramesPlacedInI Λ lbl sC (frs σC c) (WkSlotsK sC)) :
    ∀ s : State, F' s.st.1 → ∃ σC c, nC.J σC c ∧ FramesPlaced Λ lbl s (frs σC c) := by
  intro s hs
  obtain ⟨mC, σC, c, hA, hJ, hk⟩ := hFC _ hs
  let sC : State := { s with st := (mC, s.st.2) }
  have hsp : sC.st.1.regs.SP.toBitVec = R.addr nC.o.sp := by
    show mC.regs.SP.toBitVec = _
    rw [hA.regs]
    exact hA.so.sp
  exact ⟨σC, c, hJ, framesPlaced_kept hsp hk8 hlo hhi (hU σC c mC hA hJ sC rfl) hk⟩

/-- Inhabitation: the geometry at the worker's call (`kc = -96`, `print`'s `lo' = -96`) in a region holding
`-192 .. 0`, and the transfer at no frame, at any two states the call keeps. -/
example (R : Region) (hR : R.lo = -192 ∧ R.hi = 0) (sC s : State) (hsp : sC.st.1.regs.SP.toBitVec = R.addr (-96))
    (hk : CKept R (-96) (-96) 0 sC.st.1 s.st.1) :
    (∀ a, WkSlotsK sC a → ∃ k, R.Off k ∧ ¬ (R.callee (-96) (-96) 0).Off (k - (-96)) ∧ a = (R.addr k).toNat) ∧
      FramesPlaced Λ lbl s [] :=
  ⟨wkSlots_out hsp (by decide) (by omega) (by omega),
    framesPlaced_kept hsp (by decide) (by omega) (by omega) (FramesPlacedInI.nil _) hk⟩

end Spike.Lib.A64.HelloPh.UFrameKeep

/-- info: 'Spike.Lib.A64.HelloPh.UFrameKeep.wkSlots_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.UFrameKeep.wkSlots_out

/-- info: 'Spike.Lib.A64.HelloPh.UFrameKeep.framesPlacedInI_kept' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.UFrameKeep.framesPlacedInI_kept

/-- info: 'Spike.Lib.A64.HelloPh.UFrameKeep.framesPlaced_kept' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.UFrameKeep.framesPlaced_kept

/-- info: 'Spike.Lib.A64.HelloPh.UFrameKeep.framesPlaced_of_hFC' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.UFrameKeep.framesPlaced_of_hFC
