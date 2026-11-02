/-
**The child segment's slice-count premise at main's clone on x86-64** (the twin of
`Spike/Lib/A64HelloChildLim.lean`; premises of the child's segment, `ChildPrem`). At the clone
(`X64HelloPreA.ClonePreH`) the child's words are main's `%r12, %rbx, %r13, %r14, %r15, %r9`; `%r13` is the
slice's word count, `2` (`SlRep`: the packet's slice `[b, 2, 13]`), so its byte count fits `wc_worker`'s signed
bound.

- `r13_clone`: main's `%r13` at the clone is `2`.
- `hm_clone`: `ChildPrem.hm` at the clone's words (`w.w2 = %r13`).

## Differences from the AArch64 version

- The word count is in `%r13` (A64's `x11`), so `x11_clone` is `r13_clone`; it reads the count through the
  projection `ClonePreH.src` (A64 destructures `ClonePreH` by position).
- No label prefix `pfx` (x86-64's `ClonePreH` has none).
-/
import Spike.Lib.X64HelloClonePreH

namespace Spike.Lib.X64HelloPreA

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib.X64WakeA64 (Cfg)

variable {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}

/-- **main's `%r13` at the clone is the slice's word count `2`** (`SlRep`). -/
theorem r13_clone (h : ClonePreH Λ r0 r1 X lbl t s) {th : Thread isa} (hth : t.1.threads = #[th]) :
    (th.st.st.1.regs.get64 .r13).toNat = 2 := by
  obtain ⟨th', _, _, _, _, hth', -, -, -, hsl, -, -⟩ := h.src
  have e : th = th' := by
    rw [hth] at hth'
    exact List.singleton_inj.mp (congrArg Array.toList hth')
  obtain ⟨-, -, -, -, h2, -⟩ := hsl
  rw [e]; exact h2

/-- **`ChildPrem.hm` at the clone's words**: the slice's byte count `8 · %r13 = 16` is below `2 ^ 63`. -/
theorem hm_clone (h : ClonePreH Λ r0 r1 X lbl t s) {th : Thread isa} (hth : t.1.threads = #[th]) :
    (th.st.st.1.regs.get64 .r13).toNat * 8 < 2 ^ 63 := by
  rw [r13_clone h hth]; decide

end Spike.Lib.X64HelloPreA

/-- info: 'Spike.Lib.X64HelloPreA.r13_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.r13_clone

/-- info: 'Spike.Lib.X64HelloPreA.hm_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.hm_clone
