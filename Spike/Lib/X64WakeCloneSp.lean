/-
**main's stack pointer at its `clone` is deep in its stack range** (x86-64,
wake.w): with `%rsp` 128 bytes below `r0`'s top (`X64WakePreA.ClonePre.spTop`,
the x86-64 frame accounting; `wc_main`'s frame is 80 bytes) and `r0` the
16 KiB take, `[sp - 16, sp + 96)` is in `r0`: 16 bytes below `wc_main`'s
frame (the wait loop's and the park's frames) and `scc_rt_main`'s spill
cell above it.

- `sp_in_r0`: the arithmetic.
- `clone_sp_in_r0`: from `ClonePre.spTop`'s shape (`∃ th`, one thread, the
  two equations), the bounds main's rows after the spawn need.

x86-64 twin of `Spike/Lib/WakeCloneSp.lean` (same names, namespaces with the
`X64` prefix).
-/
import Spike.Lib.X64WakeA64

namespace Spike.Lib.X64WakeCloneSp

open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib.X64WakeA64

/-- **The arithmetic**: 128 below the top of a 16 KiB range leaves 16 below
and 96 above in the range. -/
theorem sp_in_r0 {r0 : Range} {sp : Nat} (htop : sp + 128 = r0.lo + r0.size) (hsz : r0.size = 16384) :
    r0.lo + 16 ≤ sp ∧ sp + 96 ≤ r0.lo + r0.size := by
  omega

/-- **main's frame and its neighbours are in `r0`** at the clone, from
`ClonePre.spTop`'s conclusion. -/
theorem clone_sp_in_r0 {r0 : Range} {t : Cfg}
    (h : ∃ th : Thread isa, t.1.threads = #[th] ∧ (th.st.st.1.regs.get64 .rsp).toNat + 128 = r0.lo + r0.size ∧
      r0.size = 16384) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧ r0.lo + 16 ≤ (th.st.st.1.regs.get64 .rsp).toNat ∧
      (th.st.st.1.regs.get64 .rsp).toNat + 96 ≤ r0.lo + r0.size := by
  obtain ⟨th, ht, htop, hsz⟩ := h
  exact ⟨th, ht, sp_in_r0 htop hsz⟩

/-- info: 'Spike.Lib.X64WakeCloneSp.clone_sp_in_r0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clone_sp_in_r0

end Spike.Lib.X64WakeCloneSp
