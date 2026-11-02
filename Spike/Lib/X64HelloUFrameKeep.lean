/-
**hello.w's worker frame kept inside `print`** (x86-64; the twin of `Spike/Lib/A64HelloUFrameKeep.lean`): at every
state `print` reaches from the worker's call of it, the worker's frame (the continuation `workerRestH`, free
variables `c` and `j`) is still placed. Its places are `wc_worker`'s cells `-40(%rbp)` (`c`, the published cell)
and `-48(%rbp)` (`j`, the parent's `ThreadId`), read after `.Lwc_worker.x17`. At the call state (the return
address pushed, `%rsp = %rbp - 88`: the frame's 80 bytes and the return address), they are the words `%rsp + 48`
and `%rsp + 40` (the region's cells `-48`, `-56` with `%rbp` at `-8`, `X64HelloWorkerBody`). `print`'s region is
`R.callee kc lo' 0`, below the call's `%rsp`, so the cells stay outside it and the call's frame condition keeps
them (`CKept`).

- `WkSlotsK`: the two slots, `%rsp + 40` and `%rsp + 48` at the call state.
- `wkSlots_out`: the two slots are `R.addr k` for cells `k = kc + 40`, `kc + 48` of `R` outside the callee's
  region, given `%rsp = R.addr kc` at the call state.
- `framesPlacedInI_kept`, `framesPlaced_kept`: frames placed in those slots at the call state stay placed at any
  state whose machine keeps the caller's cells outside the callee's region (`FramesPlacedInI.of_cKept`).
- `framesPlaced_of_hFC`: at every state of a frame condition that knows the call, the frames are placed, given
  their placement at the call state (`hU`).

Unlike AArch64, the stack pointer is `regs.get64 .rsp` (AArch64's `regs.SP`), it equals `R.addr o.sp` by `Abs`'s
`so` at `.rsp` (`SO.get`), the call state's `%rsp` is below the pushed return address (`X64Call.at_enter`), and
the two words are read through `%rbp` (`-40`, `-48`), at `%rsp + 48`, `%rsp + 40` (AArch64: `sp + 40`, `sp + 32`,
no return address on the stack).
-/
import Spike.Lib.X64FramesPlacedI

namespace Spike.Lib.X64.HelloPh.UFrameKeep

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Region Ctl)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (FramesPlaced FramesPlacedInI)
open Spike.Lib.X64 (ND CKept)

/-- **wc_worker's slots of `j` and `c`** at the call state `s` (`%rsp = %rbp - 88`, the return address pushed):
the words `%rsp + 40`, `%rsp + 48` (cells `-48(%rbp)`, `-40(%rbp)`). -/
abbrev WkSlotsK (s : State) (a : Nat) : Prop :=
  a = (s.st.1.regs.get64 .rsp + 40#64).toNat ∨ a = (s.st.1.regs.get64 .rsp + 48#64).toNat

/-- **The two slots are caller cells outside the callee's region**: with `%rsp = R.addr kc` at the call state,
the words `%rsp + 40` and `%rsp + 48` are `R.addr k` at `k = kc + 40`, `kc + 48`, cells of `R` above the callee's
region `R.callee kc lo' 0`. -/
theorem wkSlots_out {R : Region} {kc lo' : Int} {sC : State} (hsp : sC.st.1.regs.get64 .rsp = R.addr kc)
    (hk8 : kc % 8 = 0) (hlo : R.lo ≤ kc + 40) (hhi : kc + 56 ≤ R.hi) :
    ∀ a, WkSlotsK sC a → ∃ k, R.Off k ∧ ¬ (R.callee kc lo' 0).Off (k - kc) ∧ a = (R.addr k).toNat := by
  rintro a (rfl | rfl)
  · refine ⟨kc + 40, ⟨by omega, by omega, by omega⟩, fun h => ?_, by rw [hsp, Region.addr_add]; rfl⟩
    simp only [Region.callee, Region.Off] at h
    omega
  · refine ⟨kc + 48, ⟨by omega, by omega, by omega⟩, fun h => ?_, by rw [hsp, Region.addr_add]; rfl⟩
    simp only [Region.callee, Region.Off] at h
    omega

variable {Λ : Scc.Sem.Layout} {lbl : Lbl}

/-- **Frames placed in the worker's slots stay placed** at any state whose machine keeps the caller's cells
outside the callee's region (`CKept`; `FramesPlacedInI.of_cKept` with `wkSlots_out`). -/
theorem framesPlacedInI_kept {R : Region} {kc lo' : Int} {sC s : State} {fs : List TermRun.Frame}
    (hsp : sC.st.1.regs.get64 .rsp = R.addr kc) (hk8 : kc % 8 = 0) (hlo : R.lo ≤ kc + 40) (hhi : kc + 56 ≤ R.hi)
    (h : FramesPlacedInI Λ lbl sC fs (WkSlotsK sC)) (hk : CKept R kc lo' 0 sC.st.1 s.st.1) :
    FramesPlacedInI Λ lbl s fs (WkSlotsK sC) :=
  h.of_cKept hk (wkSlots_out hsp hk8 hlo hhi)

/-- **`framesPlacedInI_kept` as `FramesPlaced`**. -/
theorem framesPlaced_kept {R : Region} {kc lo' : Int} {sC s : State} {fs : List TermRun.Frame}
    (hsp : sC.st.1.regs.get64 .rsp = R.addr kc) (hk8 : kc % 8 = 0) (hlo : R.lo ≤ kc + 40) (hhi : kc + 56 ≤ R.hi)
    (h : FramesPlacedInI Λ lbl sC fs (WkSlotsK sC)) (hk : CKept R kc lo' 0 sC.st.1 s.st.1) :
    FramesPlaced Λ lbl s fs :=
  (framesPlacedInI_kept hsp hk8 hlo hhi h hk).toFramesPlaced

/-- **The frames placed at every state of a frame condition that knows the call**: each machine `m` of `F'` has
the call's machine `mC` (`Abs R nC.o mC σC`, `nC.J σC c`) with the caller's cells outside `R.callee nC.o.sp lo' 0`
as in `mC`; `hU` places `frs σC c` in the worker's slots at any state of machine `mC`. The call's `%rsp` is
`Abs`'s (`so` at `.rsp`). -/
theorem framesPlaced_of_hFC {R : Region} {nC : ND} {lo' : Int} {F' : MachineData → Prop}
    {frs : Spike.Lib.X64.AS → Ctl → List TermRun.Frame}
    (hk8 : nC.o.sp % 8 = 0) (hlo : R.lo ≤ nC.o.sp + 40) (hhi : nC.o.sp + 56 ≤ R.hi)
    (hFC : ∀ m, F' m → ∃ mC σC c, Spike.Lib.X64.Abs R nC.o mC σC ∧ nC.J σC c ∧ CKept R nC.o.sp lo' 0 mC m)
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
  exact ⟨σC, c, hJ, framesPlaced_kept hsp hk8 hlo hhi (hU σC c mC hA hJ sC rfl) hk⟩

/-- Inhabitation: the geometry at the worker's call (`kc = -96`: the return address cell `0`, `%rbp` at `-8`, the
frame's 80 bytes and the pushed return address below it; `print`'s region from `-96`) in a region holding
`-192 .. 0`, and the transfer at no frame. -/
example (R : Region) (hR : R.lo = -192 ∧ R.hi = 0) (sC s : State) (hsp : sC.st.1.regs.get64 .rsp = R.addr (-96))
    (hk : CKept R (-96) (-96) 0 sC.st.1 s.st.1) :
    (∀ a, WkSlotsK sC a → ∃ k, R.Off k ∧ ¬ (R.callee (-96) (-96) 0).Off (k - (-96)) ∧ a = (R.addr k).toNat) ∧
      FramesPlaced Λ lbl s [] :=
  ⟨wkSlots_out hsp (by decide) (by omega) (by omega),
    framesPlaced_kept hsp (by decide) (by omega) (by omega) (FramesPlacedInI.nil _) hk⟩

end Spike.Lib.X64.HelloPh.UFrameKeep

/-- info: 'Spike.Lib.X64.HelloPh.UFrameKeep.wkSlots_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.UFrameKeep.wkSlots_out

/--
info: 'Spike.Lib.X64.HelloPh.UFrameKeep.framesPlaced_kept' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.UFrameKeep.framesPlaced_kept

/--
info: 'Spike.Lib.X64.HelloPh.UFrameKeep.framesPlaced_of_hFC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.UFrameKeep.framesPlaced_of_hFC
