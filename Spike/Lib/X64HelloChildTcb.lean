/-
**The stacks' bound at a runtime layout on x86-64** (the twin of `Spike/Lib/A64HelloChildTcb.lean`): at a runtime
layout whose second take `r1Of` is inside the stack pool, the two takes' area does not wrap (the `hbd` premise of
`Rt.PreChild.preChild_hlim`; the second TCB's limit-word premises are `X64HelloChildTls`).

- `hbd_of`: `(stacksA L.lab).toNat + 32768 < 2 ^ 64`.

## Differences from the AArch64 version

- The layout is the x86-64 runtime's (`Spike/Lib/Rt/X64Layout.lean`, same fields: `stacks_sub`, `pool_fit`,
  `lab_stacks`); the proof is the original's.
- A64's `tcb_hlim`, `childHlim_tcb` (dead) are not twinned.
-/
import Spike.Lib.Rt.X64RtPreChild
import Spike.Lib.Rt.X64Layout

namespace Spike.Lib.X64.HelloChildTcb

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib.X64.Flow.Ret0 (stacksA)
open Spike.Lib.X64.Rt.PreChild (r1Of)

/-- **The stacks do not wrap** at a runtime layout whose second take is inside the stack pool. -/
theorem hbd_of (L : Spike.Lib.X64.Rt.RuntimeLayout) (hsub : (r1Of L.lab).Sub L.Λ.stackPool) :
    (stacksA L.lab).toNat + 32768 < 2 ^ 64 := by
  have hs := L.stacks_sub
  have hf := L.pool_fit
  have hlabS : stacksA L.lab = L.stacksA := L.lab_stacks
  obtain ⟨-, h2⟩ := hsub
  obtain ⟨-, h4⟩ := hs
  simp only [r1Of, hlabS, BitVec.toNat_add, BitVec.toNat_ofNat] at h2
  simp only at h4
  rw [hlabS]
  omega

end Spike.Lib.X64.HelloChildTcb

/-- info: 'Spike.Lib.X64.HelloChildTcb.hbd_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloChildTcb.hbd_of
