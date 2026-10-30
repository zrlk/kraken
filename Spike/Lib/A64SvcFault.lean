/-
**At a system call, `isaLSE2`'s instruction faults** (`WCompat.sysExec`, option A): a thread state at an `svc` (`Scc.Sem.A64.atSvc`,
the AArch64 kernel's `atSys`) whose instruction runs (`isaLSE2.exec s = some t`)
runs into a fault, the pending-system-call message (`Lower.A64.exec_svc`).

`exec` returning a tree gives the pc short of the end address; `atSvc` gives
the directive at the pc, hence the cell `codeAt` finds there. `SVC` is an
`Operation .W64` only, so `atSvc`'s any-width pattern is the `W64` cell
`exec_svc` reads. The layout is valid (`ValidLayout`, a hypothesis: the
labels in front of the cell occupy no bytes).

- `svc_codeAt`: at an `svc`, `codeAt` at the pc starts with the `svc` cell.
- `exec_atSvc`: at an `svc`, a running instruction faults.
- `sysExec_of_exe`: `WCompat.sysExec` for any family of fragments whose
  states run a validly laid out executable `exe`.
-/
import Kraken.Promising.Lower.EventsA64Sys
import Scc.Sem.TargetA64

namespace Spike.Lib.A64.SvcFault

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

/-- **At an `svc`, the cells at the pc start with it**: `State.directive` is
the head of `codeAt`. -/
theorem svc_codeAt {s : State} (ha : Scc.Sem.A64.atSvc s = true) :
    ∃ imm sz rest, Kraken.Executable.codeAt s.exe s.st.2 = (.instr ⟨.W64, .SVC imm⟩, sz) :: rest := by
  unfold Scc.Sem.A64.atSvc at ha
  split at ha
  · rename_i imm hd
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
      exact ⟨imm, sz, rest, by rw [hd]⟩
  · cases ha

/-- **At an `svc`, a running instruction faults** (`WCompat.sysExec`'s
fact): `exec_svc` at the cell `svc_codeAt` finds. -/
theorem exec_atSvc {s : State} {t : EvTree State} (hv : Kraken.Executable.ValidLayout s.exe)
    (ha : Scc.Sem.A64.atSvc s = true) (he : isaLSE2.exec s = some t) : ∃ m, t = .fault m := by
  obtain ⟨imm, sz, rest, hc⟩ := svc_codeAt ha
  have hne : (s.st.2 == s.endPc) = false := by
    cases h : s.st.2 == s.endPc
    · rfl
    · simp [isaLSE2, execLSE2, h] at he
  rw [exec_svc (sz := sz) ⟨hv, hne, rest, hc⟩] at he
  exact ⟨_, (Option.some.inj he).symm⟩

/-- **`WCompat.sysExec`** (`Spike.Lib.WakeW1.WCompat`, option A) for any
family `Wi` of fragments (any control type `κ`) whose states run `exe`, validly laid out: at a
system call of the AArch64 kernel model (`Scc.Sem.A64.abi.atSys`, `atSvc`),
a running instruction faults. -/
theorem sysExec_of_exe {ι κ : Type} {Wi : ι → isaLSE2.State → κ → Prop} {exe : _root_.Executable}
    [hv : Kraken.Executable.ValidLayout exe] (hW : ∀ w s c, Wi w s c → s.exe = exe) :
    ∀ w s c t, Wi w s c → Scc.Sem.A64.abi.atSys s = true → isaLSE2.exec s = some t → ∃ m, t = .fault m :=
  fun w s c _ h ha he => exec_atSvc (hW w s c h ▸ hv) ha he

end Spike.Lib.A64.SvcFault
