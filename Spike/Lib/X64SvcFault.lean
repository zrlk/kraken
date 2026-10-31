/-
**At a system call, x86-64's instruction faults** (the twin of
`Spike/Lib/A64SvcFault.lean`, for `WCompat.sysExec`, option A): a thread
state at a `syscall` (`Scc.Sem.X64.atSyscall`, the x86-64 kernel's
`atSys`) whose instruction runs (`isa.exec s = some t`) runs into a fault,
the pending-system-call message (`Lower.X64.exec_syscall`).

`exec` returning a tree gives the pc short of the end address;
`atSyscall` gives the directive at the pc, hence the cell `codeAt` finds
there. The parser builds `syscall` at `W64`, but `atSyscall` matches any
address and operation size, so `exec_atSyscall` reads the fault off
Kraken's step at any widths (`exec_of_cellAt`; `exec_syscall` is the `W64`
case).
The layout is valid (`ValidLayout`, a hypothesis).

- `syscall_codeAt`: at a `syscall`, `codeAt` at the pc starts with the
  `syscall` cell.
- `exec_atSyscall`: at a `syscall`, a running instruction faults.
- `sysExec_of_exe`: `WCompat.sysExec` for any family of fragments whose
  states run a validly laid out executable `exe`.
-/
import Kraken.Promising.Lower.EventsX64Sys
import Scc.Sem.TargetX64

namespace Spike.Lib.X64.SvcFault

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64

/-- **At a `syscall`, the cells at the pc start with it**: `State.directive`
is the head of `codeAt`. -/
theorem syscall_codeAt {s : State} (ha : Scc.Sem.X64.atSyscall s = true) :
    ∃ aw w sz rest, Kraken.Executable.codeAt s.exe s.st.2 = (.instr (.regular aw w .syscall), sz) :: rest := by
  unfold Scc.Sem.X64.atSyscall at ha
  split at ha
  · rename_i aw w hd
    have hdc : s.directive = ((Kraken.Executable.codeAt s.exe s.st.2).head?.map (·.1)) := by
      unfold State.directive Kraken.Executable.codeAt
      congr 2
    rw [hdc] at hd
    cases hc : Kraken.Executable.codeAt s.exe s.st.2 with
    | nil => rw [hc] at hd; cases hd
    | cons c rest =>
      rw [hc] at hd
      obtain ⟨d, sz⟩ := c
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hd
      exact ⟨aw, w, sz, rest, by rw [hd]⟩
  · cases ha

/-- **At a `syscall`, a running instruction faults** (`WCompat.sysExec`'s
fact): Kraken's step at the cell `syscall_codeAt` finds. -/
theorem exec_atSyscall {s : State} {t : EvTree State} (hv : Kraken.Executable.ValidLayout s.exe)
    (ha : Scc.Sem.X64.atSyscall s = true) (he : isa.exec s = some t) : ∃ m, t = .fault m := by
  obtain ⟨aw, w, sz, rest, hc⟩ := syscall_codeAt ha
  have hne : (s.st.2 == s.endPc) = false := by
    cases h : s.st.2 == s.endPc
    · rfl
    · simp [isa, X64.exec, h] at he
  have hcell : CellAt s (.instr (.regular aw w .syscall)) sz := ⟨hv, hne, rest, hc⟩
  change X64.exec s = some t at he
  rw [exec_of_cellAt hcell] at he
  simp [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, MachineData.pendingSyscall] at he
  exact ⟨_, he.symm⟩

/-- **`WCompat.sysExec`** for any family `Wi` of fragments (any control
type `κ`) whose states run `exe`, validly laid out: at a system call of the
x86-64 kernel model (`Scc.Sem.X64.abi.atSys`, `atSyscall`), a running
instruction faults. -/
theorem sysExec_of_exe {ι κ : Type} {Wi : ι → isa.State → κ → Prop} {exe : _root_.Executable}
    [hv : Kraken.Executable.ValidLayout exe] (hW : ∀ w s c, Wi w s c → s.exe = exe) :
    ∀ w s c t, Wi w s c → Scc.Sem.X64.abi.atSys s = true → isa.exec s = some t → ∃ m, t = .fault m :=
  fun w s c _ h ha he => exec_atSyscall (hW w s c h ▸ hv) ha he

/-- info: 'Spike.Lib.X64.SvcFault.syscall_codeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms syscall_codeAt

/-- info: 'Spike.Lib.X64.SvcFault.exec_atSyscall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exec_atSyscall

/-- info: 'Spike.Lib.X64.SvcFault.sysExec_of_exe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sysExec_of_exe

end Spike.Lib.X64.SvcFault
