/-
**The fragment and the executable are kept along the worker's rows**
(`WCompat.wide` via `SegT.conjS`): on AArch64, the state
predicate `WideX exe s` (`Scc.Cert.WideA64.WideSt s`, `s.exe = exe`) is kept by
every instruction (`ExecKeeps`, from `execLSE2_leaf`) and by the kernel
model `Scc.Sem.A64.abi` (`KernKeeps`: a system call's returns and
`arch_prctl`'s thread pointer change the machine state only).

- `WideX`: the kept predicate.
- `wideX_exec`, `wideX_kern`: the two closure premises of `SegT.conjS`.
- `wideX_closed`: a segment to the empty fragment from `P` states in
  `WideX exe` gives a closed invariant inside `WideX exe` (`WSide.closed` with
  `WCompat.wide`, and `s.exe = exe` for `A64.SvcFault.sysExec_of_exe`).
- `wideX_threadAt`: the canonical thread of a `wideIn` program is `WideX` of
  its own executable (`wake_wide`).
-/
import Spike.Lib.SegThrS
import Scc.Cert.Rt.WideA64

namespace Spike.Lib.A64.WideKeep

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.WideA64 (WideSt)

/-- **The fragment, at the executable `exe`.** -/
def WideX (exe : _root_.Executable) (s : State) : Prop := WideSt s ∧ s.exe = exe

/-- Every instruction keeps `WideX exe`: its leaves keep the executable and
the declarations. -/
theorem wideX_exec (exe : _root_.Executable) : ExecKeeps isaLSE2 (WideX exe) := by
  intro s t s' hs he hl
  obtain ⟨hx, hd⟩ := Scc.Cert.WideA64.execLSE2_leaf he hl
  exact ⟨⟨hd ▸ hs.1.1, hx ▸ hs.1.2⟩, hx.trans hs.2⟩

/-- The kernel model `Scc.Sem.A64.abi` keeps `WideX exe`. -/
theorem wideX_kern {ms : MemSide isaLSE2} (hK : ms.K = some Scc.Sem.A64.abi) (exe : _root_.Executable) :
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
fragment under the kernel model `Scc.Sem.A64.abi`. -/
theorem wideX_closed {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    (hK : ms.K = some Scc.Sem.A64.abi) {exe : _root_.Executable} {P : Frag isaLSE2}
    (h : SegT p lbl ms P (fun _ _ => False)) :
    ∃ inv : Frag isaLSE2, (∀ s c, P s c → WideX exe s → inv s c) ∧ (∀ s c, inv s c → WideX exe s) ∧
      ∀ s c, inv s c → OutT p lbl ms inv s c :=
  closedS_of_segT h (wideX_exec exe) (wideX_kern hK exe)

/-- The canonical thread of a `wideIn` program is `WideX` of its own
executable. -/
theorem wideX_threadAt {prog : Program} (hw : Scc.Cert.WideA64.wideIn prog = true) (E : Scc.Sem.Entry)
    (base : Nat) (syms : List (String × Nat)) :
    WideX (Scc.Sem.A64.threadAt E base prog syms).exe (Scc.Sem.A64.threadAt E base prog syms) :=
  ⟨Scc.Cert.WideA64.wideSt_threadAt hw E base syms, rfl⟩

end Spike.Lib.A64.WideKeep
