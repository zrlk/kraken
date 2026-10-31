/-
**wake.w on x86-64: the thread pointer (`%fs` base) through the spawn**
(the fs-base half of the TP interface; the ISA-specific pieces of
`Spike/Lib/A64WakeWcMain.lean`'s `tpG`/`tp_of_at`, whose `wc_main`-specific
rest is the `Wc*` retarget). On x86-64 no instruction writes `fsBase`
(`Spike.Lib.X64.KeepTP`); only the kernel does: `arch_prctl(158, 4098)` at
the start (`Spike.Lib.X64.Flow.WakeHtp`) and `clone` with `CLONE_SETTLS`
(`%r8`) for the child.

- `tpG t W`: `W` at the states with `fsBase = t`.
- `tp_of_at`: a state at a node whose invariant fixes `fsBase` has it.
- `parent_tp`: the parent keeps its `fsBase` across the `clone`.
- `child_tp`: the child's `fsBase` is the `clone`'s `tls`.
-/
import Spike.Lib.X64Handover
import Spike.Lib.X64KeepTP
import Spike.Lib.X64Cfg

namespace Spike.Lib.X64.WakeTP

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.KeepTP (TP)

/-- **`W` at the states with `fsBase = t`** (A64's `WakeWc.tpG`). -/
abbrev tpG (t : UInt64) (W : Frag isa) : Frag isa := fun s c => TP t s → W s c

/-- **A state at a node whose invariant fixes the thread pointer has it.** -/
theorem tp_of_at {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {t : UInt64} (ht : ∀ σ c, n.J σ c → σ.regs.fsBase = t) {s : State} {c : Ctl}
    (h : At exe endPc R F n s c) : TP t s := by
  obtain ⟨-, -, -, -, σ, hA, -, hJ⟩ := h
  show s.st.1.regs.fsBase = t
  rw [hA.regs]; exact ht σ c hJ

/-- **The parent keeps its thread pointer across the `clone`** (the
`syscall` writes `%rax`, `%rcx`, `%r11` only; the handover changes private
memory only). -/
theorem parent_tp {x : Kernel.KState} {tid : Nat} {t : Thread isa} {stack : Nat} {r : BitVec 64} {tp : UInt64}
    (h : TP tp t.st) : TP tp (Kernel.retThread abi (parentPre abi x tid t stack) r).st := by
  obtain ⟨m, hc, -⟩ := Spike.Lib.X64Handover.parent_st (x := x) (tid := tid) (t := t) (stack := stack) (r := r)
  rw [hc]
  exact h

/-- **The child's thread pointer is the `clone`'s `tls`** (`CLONE_SETTLS`). -/
theorem child_tp {x : Kernel.KState} {tid : Nat} {t : Thread isa} {stack tls : Nat} :
    TP (UInt64.ofNat tls) (childAfter abi x tid t stack tls).st := by
  obtain ⟨m, hc, -⟩ := Spike.Lib.X64Handover.child_st (x := x) (tid := tid) (t := t) (stack := stack) (tls := tls)
  rw [hc]

/-- info: 'Spike.Lib.X64.WakeTP.tp_of_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tp_of_at

/-- info: 'Spike.Lib.X64.WakeTP.parent_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parent_tp

/-- info: 'Spike.Lib.X64.WakeTP.child_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms child_tp

end Spike.Lib.X64.WakeTP
