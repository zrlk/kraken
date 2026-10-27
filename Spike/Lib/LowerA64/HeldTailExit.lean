/-
**The `exit_group` tail of `scc_rt_main` at a held pair** (AArch64): the
per-state inputs `HeldS` of `blkW_heldTail`/`nodeW_heldTail`
(`Spike/Lib/LowerA64/HeldTail.lean`) at the tail's block `exitTail` and its
`svc #0` (`ExitW`, the shape of `exitTail_segWSF`'s `hW`).

The tail's store `str x0, [sp, #k]` is a covered (private, in-region)
stack store: an abstract step (`exec_ai`), so no `WrAt` (`blkW_noWr'`); the
`svc`'s tree is a fault (`exec_svc`), so no `WrAt` either. The block is off
a system call (`blkW_noSys'`), and at the `svc` `x8 = 94` (`exitNx`), so
neither is an output `write` (`notWrite1_of_abs`).

- `nodeW_noWr_svc`: an `svc #0` writes nothing;
- `exitW_noWr`: the tail's states write nothing (`hnw`);
- `exitW_heldS`: the tail's states inside `HeldS` from the abort phase's
  facts and the callee's `ret` placed outright (`Ret0`).
-/
import Spike.Lib.LowerA64.HeldTail
import Spike.Lib.LowerA64.LaneW2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At svcDir exitTail exitTail_ok exitNx ExitW)
open Spike.Lib.A64 (CodeAt)

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **An `svc #0` writes nothing**: its tree is a fault (`exec_svc`). -/
theorem nodeW_noWr_svc {n : ND} (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir]) :
    NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  have hcell : CellAt s svcDir 4 := (hc s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  refine ⟨fun L hL => ?_, fun _ h => h⟩
  rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [exec_svc hcell] at h <;> cases h

/-- **The `exit_group` tail's states write nothing** (`hnw` of `HeldS`):
the block's stack store is covered (`blkW_noWr'`, `exitTail_ok`), the
`svc` faults (`nodeW_noWr_svc`). -/
theorem exitW_noWr {n : ND} {k : Int64} (hR : R.OK) (hal : R.base.toNat % 16 = 0) {lo hi : Int}
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : Spike.Lib.offOk lo hi (n.o.sp + k.toInt) = true)
    (h16 : n.o.sp % 16 = 0) (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (exitTail k))
    (hcs : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (n.pc + 4 + 4 + 4) [svcDir]) :
    ExitW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n k :=
  ⟨blkW_noWr' hc (exitTail_ok hk h16) hR hal hlo hhi, nodeW_noWr_svc (n := exitNx n) hcs⟩

/-- **The `exit_group` tail's states inside `HeldS`** (the `hP` of
`blkW_heldTail` at `w0` and of `nodeW_heldTail` at `w1`): from the abort
phase's facts (`hab`) and the callee's `ret` placed outright (`hr`) at the
tail's states; no write by `exitW_noWr`, no output `write` off a system
call in the block and at `x8 = 94` at the `svc`. -/
theorem exitW_heldS {μ : Marks} {Ab : State → Prop} {lbl : Lbl} {n : ND} {k : Int64} (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hk : Spike.Lib.offOk lo hi (n.o.sp + k.toInt) = true) (h16 : n.o.sp % 16 = 0)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (exitTail k))
    (hcs : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (n.pc + 4 + 4 + 4) [svcDir])
    (hab : ExitW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n k)
    (hr : ExitW (Ret0 lbl) (fun _ _ => False) exe endPc R F n k) :
    ExitW (HeldS μ Ab lbl) (fun _ _ => False) exe endPc R F n k := by
  have hW := exitW_noWr (F := F) hR hal hlo hhi hk h16 hc hcs
  have hS : BlkW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n (exitTail k) :=
    blkW_noSys' hc (exitTail_ok hk h16)
  refine ⟨fun s σ c he hn hd hpc hA hF hJ j hj m hA' hD => ?_, fun s c hA => ?_⟩
  · have h1 := (hab.w0 s σ c he hn hd hpc hA hF hJ j hj m hA' hD).1
    have h2 := (hr.w0 s σ c he hn hd hpc hA hF hJ j hj m hA' hD).1
    have h3 := (hW.w0 s σ c he hn hd hpc hA hF hJ j hj m hA' hD).1
    have h4 := (hS s σ c he hn hd hpc hA hF hJ j hj m hA' hD).1
    exact ⟨⟨h1, h2, h3, fun hs => absurd hs (by rw [h4]; decide)⟩, fun _ h => h⟩
  · obtain ⟨-, -, -, -, σ, hAb, -, h94, -⟩ := id hA
    exact ⟨⟨(hab.w1 s c hA).1, (hr.w1 s c hA).1, (hW.w1 s c hA).1, fun _ => notWrite1_of_abs hAb h94⟩,
      fun _ h => h⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.nodeW_noWr_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_noWr_svc

/-- info: 'Spike.Lib.LowerA64.exitW_noWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exitW_noWr

/-- info: 'Spike.Lib.LowerA64.exitW_heldS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exitW_heldS

end Spike.Lib.LowerA64
