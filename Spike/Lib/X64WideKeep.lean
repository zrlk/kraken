/-
**The fragment and the executable are kept along the worker's rows**
(x86-64; twin of `Spike/Lib/A64WideKeep.lean`): the state
predicate `WideX exe s` (`Scc.Cert.WideX64.WideSt s`, `s.exe = exe`) is kept by
every instruction (`ExecKeeps`, from `WideX64.exec_leaf`) and by the kernel
model `Scc.Sem.X64.abi` (`KernKeeps`: a system call's returns and
`arch_prctl`'s thread pointer change the machine state only).

- `WideX`: the kept predicate.
- `wideX_exec`, `wideX_kern`: the two closure premises of `SegT.conjS`.
- `wideX_closed`: a segment to the empty fragment from `P` states in
  `WideX exe` gives a closed invariant inside `WideX exe`.
- `wideX_threadAt`: the canonical thread of `wideIn` code cells is `WideX` of
  its own executable (`WideX64.wideSt_threadAt`).

**Unlike AArch64**: the canonical thread is built from code cells
(`Scc.Sem.X64.threadAt E base cells syms`), so `wideX_threadAt` takes
`wideIn (cells.map (·.1))`.
-/
import Spike.Lib.SegThrS
import Scc.Cert.Rt.WideX64

namespace Spike.Lib.X64.WideKeep

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Cert.WideX64 (WideSt)

/-- **The fragment, at the executable `exe`.** -/
def WideX (exe : _root_.Executable) (s : State) : Prop := WideSt s ∧ s.exe = exe

/-- Every instruction keeps `WideX exe`: its leaves keep the executable and
the declarations. -/
theorem wideX_exec (exe : _root_.Executable) : ExecKeeps isa (WideX exe) := by
  intro s t s' hs he hl
  obtain ⟨hx, hd⟩ := Scc.Cert.WideX64.exec_leaf he hl
  exact ⟨⟨hd ▸ hs.1.1, hx ▸ hs.1.2⟩, hx.trans hs.2⟩

/-- The kernel model `Scc.Sem.X64.abi` keeps `WideX exe`. -/
theorem wideX_kern {ms : MemSide isa} (hK : ms.K = some Scc.Sem.X64.abi) (exe : _root_.Executable) :
    KernKeeps ms (WideX exe) := by
  intro K hk s hs
  rw [hK, Option.some.injEq] at hk
  subst hk
  refine ⟨fun call s' hm => ?_, fun r => hs⟩
  unfold Scc.Sem.Kernel.certSuccs at hm
  split at hm
  · simp only [List.mem_singleton] at hm
    subst hm
    exact hs
  · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hm
    exact hs

/-- **The closed invariant inside `WideX exe`** of a segment to the empty
fragment under the kernel model `Scc.Sem.X64.abi`. -/
theorem wideX_closed {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    (hK : ms.K = some Scc.Sem.X64.abi) {exe : _root_.Executable} {P : Frag isa}
    (h : SegT p lbl ms P (fun _ _ => False)) :
    ∃ inv : Frag isa, (∀ s c, P s c → WideX exe s → inv s c) ∧ (∀ s c, inv s c → WideX exe s) ∧
      ∀ s c, inv s c → OutT p lbl ms inv s c :=
  closedS_of_segT h (wideX_exec exe) (wideX_kern hK exe)

/-- The canonical thread of `wideIn` code cells is `WideX` of its own
executable. -/
theorem wideX_threadAt {cells : List (Directive × Nat)}
    (hw : Scc.Cert.WideX64.wideIn (cells.map (·.1)) = true) (E : Scc.Sem.Entry)
    (base : Nat) (syms : List (String × Nat)) :
    WideX (Scc.Sem.X64.threadAt E base cells syms).exe (Scc.Sem.X64.threadAt E base cells syms) :=
  ⟨Scc.Cert.WideX64.wideSt_threadAt hw E base syms, rfl⟩

end Spike.Lib.X64.WideKeep
