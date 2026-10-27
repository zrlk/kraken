/-
**The `exit_group` tail of `scc_rt_main` at a held pair** (x86-64): the
per-state inputs `HeldS` of `blkW_heldTail`/`nodeW_heldTail`
(`Spike/Lib/LowerX64/HeldTail.lean`) at the tail's block `xExit` and its
`syscall` (`XExitW`, the shape of `xExitTail_segWSF`'s `hW0`/`hW1`).

The tail's store `movq %rax, k(%rbp)` is a covered (private, in-region)
stack store: an abstract step (`exec_ai`), so no `WrAt` (`blkW_noWr'`); the
`syscall`'s tree is a fault (`exec_syscall`), so no `WrAt` either. The
block is off a system call (`blkW_noSys'`), and at the `syscall` `%rax = 231`
(`xExitNx`), so neither is an output `write` (`notWrite1_of_abs`).

- `nodeW_noWr_syscall`: a `syscall` writes nothing;
- `xExitW_noWr`: the tail's states write nothing (`hnw`);
- `xExitW_heldS`: the tail's states inside `HeldS` from the abort phase's
  facts and the callee's `ret` placed outright (`Ret0`).
-/
import Spike.Lib.LowerX64.HeldTail
import Spike.Lib.LowerX64.W2Body

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At CodeAt)
open Spike.Lib.X64.Flow (xExit xExit_ok xExitNx XExitW)

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A `syscall` writes nothing**: its tree is a fault (`exec_syscall`). -/
theorem nodeW_noWr_syscall {n : ND} {z : Nat}
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)]) :
    NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  have hcell : CellAt s (op64 .syscall) z := (hc s hs hn).cell0 rfl rfl hpc
  refine ⟨fun L hL => ?_, fun _ h => h⟩
  rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [exec_syscall hcell] at h <;> cases h

/-- **The `exit_group` tail's states write nothing** (`hnw` of `HeldS`):
the block's stack store is covered (`blkW_noWr'`, `xExit_ok`), the
`syscall` faults (`nodeW_noWr_syscall`). -/
theorem xExitW_noWr {n : ND} {sp b : Int} {k : Int64} {z0 z1 z2 z3 : Nat} (hno : n.o = ⟨sp, [(.rbp, b)]⟩)
    (hR : R.OK) {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : Spike.Lib.offOk lo hi (b + k.toInt) = true)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (xExit k z0 z1 z2))
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2) [(op64 .syscall, z3)]) :
    XExitW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n sp b k z0 z1 z2 :=
  ⟨blkW_noWr' hc0 (hno ▸ xExit_ok k z0 z1 z2 hk) hR hlo hhi, nodeW_noWr_syscall (n := xExitNx n sp b z0 z1 z2) hc1⟩

/-- **The `exit_group` tail's states inside `HeldS`** (the `hP` of
`blkW_heldTail` at `w0` and of `nodeW_heldTail` at `w1`): from the abort
phase's facts (`hab`) and the callee's `ret` placed outright (`hr`) at the
tail's states; no write by `xExitW_noWr`, no output `write` off a system
call in the block and at `%rax = 231` at the `syscall`. -/
theorem xExitW_heldS {μ : Marks} {Ab : State → Prop} {lbl : Lbl} {n : ND} {sp b : Int} {k : Int64}
    {z0 z1 z2 z3 : Nat} (hno : n.o = ⟨sp, [(.rbp, b)]⟩) (hR : R.OK) {lo hi : Int} (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) (hk : Spike.Lib.offOk lo hi (b + k.toInt) = true)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (xExit k z0 z1 z2))
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2) [(op64 .syscall, z3)])
    (hab : XExitW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n sp b k z0 z1 z2)
    (hr : XExitW (Ret0 lbl) (fun _ _ => False) exe endPc R F n sp b k z0 z1 z2) :
    XExitW (HeldS μ Ab lbl) (fun _ _ => False) exe endPc R F n sp b k z0 z1 z2 := by
  have hW := xExitW_noWr (F := F) hno hR hlo hhi hk hc0 hc1
  have hS : BlkW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n (xExit k z0 z1 z2) :=
    blkW_noSys' hc0 (hno ▸ xExit_ok k z0 z1 z2 hk)
  refine ⟨fun s σ c he hn hd hpc hA hF hJ j hj m hA' hD => ?_, fun s c hA => ?_⟩
  · have h1 := (hab.w0 s σ c he hn hd hpc hA hF hJ j hj m hA' hD).1
    have h2 := (hr.w0 s σ c he hn hd hpc hA hF hJ j hj m hA' hD).1
    have h3 := (hW.w0 s σ c he hn hd hpc hA hF hJ j hj m hA' hD).1
    have h4 := (hS s σ c he hn hd hpc hA hF hJ j hj m hA' hD).1
    exact ⟨⟨h1, h2, h3, fun hs => absurd hs (by rw [h4]; decide)⟩, fun _ h => h⟩
  · obtain ⟨-, -, -, -, σ, hAb, -, h231, -⟩ := id hA
    exact ⟨⟨(hab.w1 s c hA).1, (hr.w1 s c hA).1, (hW.w1 s c hA).1, fun _ => notWrite1_of_abs hAb h231⟩,
      fun _ h => h⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.nodeW_noWr_syscall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_noWr_syscall

/-- info: 'Spike.Lib.LowerX64.xExitW_noWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms xExitW_noWr

/-- info: 'Spike.Lib.LowerX64.xExitW_heldS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms xExitW_heldS

end Spike.Lib.LowerX64
