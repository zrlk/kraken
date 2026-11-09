/-
**wake.w on x86-64: main back from a refused `clone`** (the spawn's refusal
half; the twin of `Spike/Lib/A64WakeRefuse.lean`): main at the clone's
`syscall` (`.Lwc_main.x3 + 46`, `wcNS` in its frame), once the kernel
returns a refusal `r` (`ThreadsAb.CloneRef`: `-EAGAIN` or `-ENOMEM`;
`abi.ret` writes `%rax`, `%rcx`, `%r11` and moves past the `syscall`), is at
the refusal path's first node `SpawnFail.fN … .ts`
(`Spike/Lib/X64WakeSpawnFail.lean`).

- `refuse_at`: the returned state is in `At` of `fN .ts`, the frame
  condition its memory outside the region (`DFrame`), main's slots `-16`
  and `-8` (`MS`) kept.
- `refuse_atF`: the same under a frame condition `F` of the memory alone
  (`abi.ret` keeps the memory).

**Unlike AArch64**: the entry is the clone's node `wcNS` itself (its frame
words `FrW` carry both slots `MS` reads: the cell at `-16`, main's word at
`-8`), not the parent's node `JS` with a separate slot premise `hm`; the
returned registers are `retRegs64`'s (`syscallStep`, as
`Parent.parent_at`), so the abstraction's offsets go through `syscallSO`.
-/
import Spike.Lib.X64WakeSpawnFail
import Spike.Lib.X64WakeParentAt

namespace Spike.Lib.X64.WakePh.SpawnFail

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (oW x21L svcB wcNS)
open Spike.Lib.X64.ThreadsAb (CloneRef)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {cP : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {s : State} {r : BitVec 64}

/-- `abi.ret`'s state: the registers `retRegs64`'s, the pc past the
`syscall`, the memory kept. -/
theorem ret_eq : abi.ret s r =
    { s with st := (({ s.st.1 with regs := retRegs64 s r } : MachineData), nextPc s) } := rfl

/-- **Main back from a refused clone is at `fN .ts`**: main at the clone's
`syscall` (`hcode`) in region `R` at `wcNS` gives, once the kernel returns
the refusal `r`, a state in `At` of `fN … .ts` for the frame condition its
memory outside the region. -/
theorem refuse_at
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label x21L + 46) svcB)
    (hat : At exe endPc R F (wcNS (_root_.Executable.labels exe).label cP t k cA m fr) s cP) (hr : CloneRef r) :
    At exe endPc R (DFrame R (abi.ret s r).st.1) (fN (_root_.Executable.labels exe).label cP cA m .ts)
      (abi.ret s r) cP := by
  obtain ⟨he, hn, hd, hpc, σ, hA, -, hJ⟩ := hat
  change s.st.2 = _ at hpc
  have hcell : CellAt s (op64 .syscall) 2 := (hcode s he hn).cell0 rfl rfl hpc
  have hnext := nextPc_of_cellAt hcell
  rw [ret_eq]
  refine ⟨he, hn, hd, ?_, ⟨syscallStep (nextPc s) r σ, ⟨?_, hA.zmms, hA.status, ?_, hA.slot⟩,
    DFrame.refl _ _, ?_⟩⟩
  · show nextPc s = _
    rw [hnext, hpc]
    show (_root_.Executable.labels exe).label x21L + 46 + Int64.ofNat 2 =
      (_root_.Executable.labels exe).label x21L + 48
    rw [Int64.add_assoc]; rfl
  · show retRegs64 s r = syscallRegs (nextPc s) (rflags σ.status) r σ.regs
    simp only [retRegs64, syscallRegs, hA.regs, hA.status]
  · exact syscallSO_rel hA.so (nextPc s) (rflags σ.status) r
  · obtain ⟨⟨⟨hc, -, -, h16, h8, -⟩, -⟩, -⟩ := hJ
    have hX : (UInt64.ofNat r.toNat).toBitVec = r := by show BitVec.ofNat 64 r.toNat = r; simp
    refine ⟨hc, ?_, h16, h8⟩
    show CloneRef (UInt64.ofNat r.toNat).toBitVec
    rw [hX]; exact hr

/-- **`refuse_at` under a frame condition of the memory alone**: `abi.ret`
keeps the memory, so `F` (holding of the state at the clone, `hat`) holds
after it. -/
theorem refuse_atF (hF : ∀ m m', m.dmem = m'.dmem → F m → F m')
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label x21L + 46) svcB)
    (hat : At exe endPc R F (wcNS (_root_.Executable.labels exe).label cP t k cA m fr) s cP) (hr : CloneRef r) :
    At exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .ts) (abi.ret s r) cP := by
  have hat0 := hat
  obtain ⟨-, -, -, -, -, -, hF0, -⟩ := hat0
  obtain ⟨he, hn, hd, hpc, σ, hA, -, hJ⟩ := refuse_at hcode hat hr
  exact ⟨he, hn, hd, hpc, σ, hA, hF s.st.1 _ rfl hF0, hJ⟩

end Spike.Lib.X64.WakePh.SpawnFail

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.refuse_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.refuse_at

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.refuse_atF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.refuse_atF
