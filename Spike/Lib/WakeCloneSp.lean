/-
**main's stack pointer at its `clone` is deep in its stack range** (AArch64,
wake.w): with `sp` 128 bytes below `r0`'s top (`scc_rt_start` sets `sp` to
`r0`'s top, `scc_rt_main` takes 48 bytes and `wc_main` 80) and `r0` the
16 KiB take, `[sp - 16, sp + 96)` is in `r0`: 16 bytes below `wc_main`'s
frame (the wait loop's and the park's frames) and `scc_rt_main`'s spill
cell above it.

- `sp_in_r0`: the arithmetic.
- `clone_sp_in_r0`: from `ClonePre.spTop`'s shape (`∃ th`, one thread, the
  two equations), the bounds main's rows after the spawn need.
-/
import Spike.Lib.WakeA64

namespace Spike.Lib.WakeCloneSp

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem
open Spike.Lib.WakeA64

/-- **The arithmetic**: 128 below the top of a 16 KiB range leaves 16 below
and 96 above in the range. -/
theorem sp_in_r0 {r0 : Range} {sp : Nat} (htop : sp + 128 = r0.lo + r0.size) (hsz : r0.size = 16384) :
    r0.lo + 16 ≤ sp ∧ sp + 96 ≤ r0.lo + r0.size := by
  omega

/-- **main's frame and its neighbours are in `r0`** at the clone, from
`ClonePre.spTop`'s conclusion. -/
theorem clone_sp_in_r0 {r0 : Range} {t : Cfg}
    (h : ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧ th.st.st.1.regs.SP.toNat + 128 = r0.lo + r0.size ∧
      r0.size = 16384) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧ r0.lo + 16 ≤ th.st.st.1.regs.SP.toNat ∧
      th.st.st.1.regs.SP.toNat + 96 ≤ r0.lo + r0.size := by
  obtain ⟨th, ht, htop, hsz⟩ := h
  exact ⟨th, ht, sp_in_r0 htop hsz⟩

end Spike.Lib.WakeCloneSp
