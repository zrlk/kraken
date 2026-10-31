/-
**wake.w's worker never at the program's end** (x86-64): a pc at the bytes
of wake.w's cells decided by `abChk` (the same check as `X64WakeAbOffL`'s)
is not `endOf exe wakeCells kp`, the pc at which a thread halts
(`isa.exec` is `none` there), and at a `syscall` off the end the
instruction runs (it faults): `hhalt1` of `WakeAssembly.wake_obligations`
for a side whose states run `exe` off the end.

- `endOff_at`: `label l + k0 + k`, decided by `abChk l k0 len`, `k < len`,
  is not the program's end (the bytes before it are fewer than the cells').
- `EndOff exe kp`: the pc is not the program's end.
- `exec_isSome_atSyscall`, `hhalt1_of`: at a `syscall` off the end the
  instruction runs; for a family of states off the end.

x86-64 twin of `Spike/Lib/A64WakeEndOff.lean` (namespace
`Spike.Lib.X64.Flow.Worker.Wake.EndOff`). **Where this differs from
AArch64**: as `X64WakeAbOffW`, only the ISA-level half is twinned. The
per-node half (`nodeZ_end`, `pro_end`, `head_end`, `wk_end`, `unpk_end`,
`tail_end`, `thrZ_end`, `cZ_end`, `wakeZE`, `childThrZE`, `cZE`) needs the
x86-64 `NodeZ`/`ThrZ`, the worker's node families and `wakePass`, not
twinned on this branch; it belongs with them, from `endOff_at`. So
`hhalt1_of` takes its states running `exe` at `endPc` off the end directly
(A64: inside `NNZ exe endPc (wakeZE exe kp)`). Pcs are bytes (`label l +
k0 + k`, A64 `label l + 4k0 + 4k`), decided by `X64RunsOff.runsNeChk`'s
bounds (A64: the label's index and its run); the end is `endOf exe
wakeCells kp`'s byte sum (A64 the address of the cell past `wakeProg`). The
system call is `syscall` (`Scc.Sem.X64.atSyscall`, A64 `svc`).
-/
import Spike.Lib.X64WakeAbOffL
import Spike.Lib.X64SvcFault

namespace Spike.Lib.X64.Flow.Worker.Wake.EndOff

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.RunsOff (labOff runsNeChk label_labOff base_add_lt)
open Spike.Lib.X64.Flow.Worker.Wake.AbOffAt (abChk)
open SccCode (wakeCells)

/-- **The pc is not the program's end.** -/
def EndOff (exe : _root_.Executable) (kp : Nat) : Frag isa := fun s _ => s.st.2 ≠ endOf exe wakeCells kp

section Inst

variable {exe : _root_.Executable} [hv : Kraken.Executable.ValidLayout exe] {kp : Nat}
  (hp : Lays exe wakeCells kp)
include hp

/-- **Off the end at a decided pc**: the byte `k0 + k` after `l`, `k < len`,
with `abChk l k0 len`. -/
theorem endOff_at {l : Label} {k0 len : Nat} (hchk : abChk l k0 len = true) {q : Int64} {k : Nat}
    (hk : k < len) (hs : q = (_root_.Executable.labels exe).label l + Int64.ofNat k0 + Int64.ofNat k) :
    q ≠ endOf exe wakeCells kp := by
  simp only [abChk, runsNeChk, Bool.and_eq_true, List.all_eq_true] at hchk
  have hr := hchk.2 _ List.mem_cons_self
  split at hr
  next a ha =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    have hra := hr.1
    rw [hs, Int64.add_assoc, ← Int64.ofNat_add, (label_labOff hp ha).1, endOf]
    have hB := base_add_lt hp
    intro heq
    have h4 := congrArg Int64.toBitVec heq
    simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat', BitVec.add_assoc] at h4
    have h5 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp h4)
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h5
    rw [Nat.mod_eq_of_lt (a := _ + a) (by omega), Nat.mod_eq_of_lt (a := k0 + k) (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h5
    omega
  next => simp at hr

end Inst

/-! ## `hhalt1` -/

/-- **At a `syscall` off the end the instruction runs** (it faults). -/
theorem exec_isSome_atSyscall {s : State} (hv : Kraken.Executable.ValidLayout s.exe)
    (ha : Scc.Sem.X64.atSyscall s = true) (hne : s.st.2 ≠ s.endPc) : (isa.exec s).isSome := by
  obtain ⟨aw, w, sz, rest, hc⟩ := Spike.Lib.X64.SvcFault.syscall_codeAt ha
  have hne' : (s.st.2 == s.endPc) = false := by simpa using hne
  have hcell : CellAt s (.instr (.regular aw w .syscall)) sz := ⟨hv, hne', rest, hc⟩
  change (X64.exec s).isSome
  rw [exec_of_cellAt hcell]
  simp [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, MachineData.pendingSyscall]

/-- **`hhalt1`** for a family of states running `exe` at `endPc`, the
program's end, off the end. -/
theorem hhalt1_of {ι κ : Type} {Wi : ι → State → κ → Prop} {exe : _root_.Executable}
    [hv : Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} (hend : endPc = endOf exe wakeCells kp)
    {cOf : κ → Ctl}
    (hW : ∀ w s c, Wi w s c → s.exe = exe ∧ s.endPc = endPc ∧ EndOff exe kp s (cOf c)) :
    ∀ w s c, Wi w s c → Scc.Sem.X64.abi.atSys s = true → (isa.exec s).isSome := by
  intro w s c h ha
  obtain ⟨he, hn, hz⟩ := hW w s c h
  exact exec_isSome_atSyscall (he ▸ hv) ha (by rw [hn, hend]; exact hz)

end Spike.Lib.X64.Flow.Worker.Wake.EndOff

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.EndOff.endOff_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.EndOff.endOff_at

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.EndOff.hhalt1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.EndOff.hhalt1_of
