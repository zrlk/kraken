/-
**The child segment's slice-count premise at main's clone** (AArch64, rows B8-seg-hm; premises of
`Hello.SegR.seg_childR` / `ChildPrem`). At the clone (`HelloPreA.ClonePreH`) the child's words are main's
`x9 .. x14`; `x11` is the slice's word count, `2` (`SlRep`: the packet's slice `[b, 2, 13]`), so its byte count
fits `wc_worker`'s signed bound.

- `x11_clone`: main's `x11` at the clone is `2`.
- `hm_clone`: `ChildPrem.hm` at the clone's words (`w.w2 = x11`).
-/
import Spike.Lib.A64HelloClonePreH

namespace Spike.Lib.HelloPreA

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem
open Spike.Lib.WakeA64

variable {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}

/-- **main's `x11` at the clone is the slice's word count `2`** (`SlRep`). -/
theorem x11_clone (h : ClonePreH pfx Λ r0 r1 X lbl t s) {th : Thread isaLSE2} (hth : t.1.threads = #[th]) :
    th.st.st.1.regs.X11.toBitVec.toNat = 2 := by
  obtain ⟨th', _, _, _, _, _, _, _, sl2, _, _, _, hth', -, -, -, -, -, -, -, -, -, h11,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsl, -, -, -⟩ := h
  obtain rfl : th = th' := by
    rw [hth] at hth'
    exact List.singleton_inj.mp (congrArg Array.toList hth')
  obtain ⟨-, -, -, -, rfl, -⟩ := hsl
  exact h11

/-- **`ChildPrem.hm` at the clone's words** (row B8-seg-hm): the slice's byte count `8 · x11 = 16` is below
`2 ^ 63`. -/
theorem hm_clone (h : ClonePreH pfx Λ r0 r1 X lbl t s) {th : Thread isaLSE2} (hth : t.1.threads = #[th]) :
    th.st.st.1.regs.X11.toBitVec.toNat * 8 < 2 ^ 63 := by
  rw [x11_clone h hth]; decide

end Spike.Lib.HelloPreA

/-- info: 'Spike.Lib.HelloPreA.x11_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.x11_clone

/-- info: 'Spike.Lib.HelloPreA.hm_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.hm_clone
