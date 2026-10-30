/-
**wake.w on AArch64: main back from a refused `clone`** (the spawn's refusal half): main at the clone's `svc` (`cloneAt pfxM`, `JS`
in its frame), once the kernel returns a refusal `r` (`ThreadsAb.CloneRef`:
`-EAGAIN` or `-ENOMEM`; `abi.ret` writes `x0` and moves past the `svc`), is
at the refusal path's first node `SpawnFail.fN pfxM … .cb`
(`Spike/Lib/A64WakeSpawnFail.lean`).

- `refuse_at`: the returned state is in `At` of `fN .cb`, the frame condition
  its memory outside the region (`DFrame`), main's slots `-72` (`JS`'s) and
  `-80` (`hm`) kept.
- `refuse_atF`: the same under a frame condition `F` of the memory alone
  (`abi.ret` keeps the memory).
-/
import Spike.Lib.A64WakeSpawnFail
import Spike.Lib.A64WakeParentAt

namespace Spike.Lib.A64.Flow.Worker.Wake.SpawnFail

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Child (svcB pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (JS oP)
open Spike.Lib.WakePreA (cloneAt)
open Spike.Lib.A64.ThreadsAb (CloneRef)

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {cP : Ctl} {A x29 ra tp mT : BitVec 64} {s : State} {r : BitVec 64}

/-- `abi.ret`'s state: `x0` the returned word, the pc past the `svc`, the
memory kept. -/
theorem ret_eq : abi.ret s r =
    { s with st := ({ s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat r.toNat } }, nextPc s) } := rfl

/-- **Main back from a refused clone is at `fN .cb`**: main at the clone's
`svc` (`hcode`) in region `R` at offsets `oP` with `JS` gives, once the
kernel returns the refusal `r`, a state in `At` of `fN pfxM … .cb` for the
frame condition its memory outside the region. -/
theorem refuse_at
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (cloneAt pfxM exe) svcB)
    (hat : At exe endPc R F ⟨cloneAt pfxM exe, oP, JS cP A x29 ra tp⟩ s cP) (hr : CloneRef r)
    (hm : ∀ σ, Abs R oP s.st.1 σ → σ.slot (-80) = mT) :
    At exe endPc R (DFrame R (abi.ret s r).st.1) (fN pfxM (_root_.Executable.labels exe).label cP A mT .cb)
      (abi.ret s r) cP := by
  obtain ⟨he, hn, hd, hpc, σ, hA, -, hJ⟩ := hat
  change s.st.2 = cloneAt pfxM exe at hpc
  obtain ⟨d0, hd0⟩ : ∃ d, svcB[0]? = some d := ⟨_, rfl⟩
  have hcell : CellAt s d0 4 := by
    have := hcode s he hn 0 d0 hd0
    rw [ofNat4_zero, ← hpc] at this
    exact this
  have hnext := nextPc_of_cellAt hcell
  have hX0 : (UInt64.ofNat r.toNat).toBitVec = r := by
    show BitVec.ofNat 64 r.toNat = r
    simp
  rw [ret_eq]
  refine ⟨he, hn, hd, ?_, ⟨{ σ with regs := { σ.regs with X0 := UInt64.ofNat r.toNat } }, ⟨?_, hA.status, ?_, ?_⟩,
    DFrame.refl _ _, ?_⟩⟩
  · show nextPc s = _
    rw [hnext, hpc]; rfl
  · show { s.st.1.regs with X0 := UInt64.ofNat r.toNat } = { σ.regs with X0 := UInt64.ofNat r.toNat }
    rw [hA.regs]
  · intro rr k hk
    cases rr with
    | SP => exact hA.so .SP k hk
    | reg xr => simp [SO.get, fN, oP, lk] at hk
  · exact hA.slot
  · exact ⟨hJ.1, by simp only [hX0]; exact hr, hJ.2.1, hm σ hA⟩

/-- **`refuse_at` under a frame condition of the memory alone**: `abi.ret`
keeps the memory, so `F` (holding of the state at the clone, `hat`) holds
after it. -/
theorem refuse_atF (hF : ∀ m m', m.dmem = m'.dmem → F m → F m')
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (cloneAt pfxM exe) svcB)
    (hat : At exe endPc R F ⟨cloneAt pfxM exe, oP, JS cP A x29 ra tp⟩ s cP) (hr : CloneRef r)
    (hm : ∀ σ, Abs R oP s.st.1 σ → σ.slot (-80) = mT) :
    At exe endPc R F (fN pfxM (_root_.Executable.labels exe).label cP A mT .cb) (abi.ret s r) cP := by
  have hat0 := hat
  obtain ⟨-, -, -, -, -, -, hF0, -⟩ := hat0
  obtain ⟨he, hn, hd, hpc, σ, hA, -, hJ⟩ := refuse_at hcode hat hr hm
  exact ⟨he, hn, hd, hpc, σ, hA, hF s.st.1 _ rfl hF0, hJ⟩

end Spike.Lib.A64.Flow.Worker.Wake.SpawnFail

/--
info: 'Spike.Lib.A64.Flow.Worker.Wake.SpawnFail.refuse_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Wake.SpawnFail.refuse_at

/--
info: 'Spike.Lib.A64.Flow.Worker.Wake.SpawnFail.refuse_atF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Wake.SpawnFail.refuse_atF
