/-
**The x64 pilot's generic partial-wp helpers.** ISA: x64
(`Kraken.X64.EnvCallsPartial`); statements about the
env-level partial wp of laid-out code, no machine.

The x64 pilot proved three program-independent helpers inside its `main` file
(`Lower/PilotX64Main.lean`, namespace `PilotX`, left where they are). They
are restated here, with the same statements, in `MachineWP` beside
`PartialWpEnv` (so dot notation `h.seg` / `h.append_false` works):

- **`MachineWP.PartialWpEnv.append_false`**: a fragment that never falls
  through is unaffected by the text behind it.
- **`MachineWP.PartialWpEnv.seg`**: a straight `vcgen` segment from an exact
  state, then the rest at every environment state above in the fence order
  (`SharedEnv.FenceMonoX`).
- **`MachineWP.ja_not_taken`**: `ja` after `cmp y, x` is not taken when
  `x ≤ y` (unsigned).

A file opening both `MachineWP` and `Kraken.Promising.Lower.PilotX` sees two
candidates for these names; PilotX's files do not import this one.
-/
import Kraken.X64.EnvCallsPartial
import Kraken.Promising.SLR.EnvG.X64VCGen

open Std.WP Kraken

namespace MachineWP

/-- **A fragment that never falls through is unaffected by the text behind
it** (the x64 pilot's `PartialWpEnv.append_false`). -/
theorem PartialWpEnv.append_false [CodeEnv] {env : SharedEnv} {q p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {s : MachineData} {g : env.State}
    (h : PartialWpEnv env q (fun _ _ => False) E s g) : PartialWpEnv env (q ++ p) Q E s g := by
  intro pc hpl
  obtain ⟨h1, -, -⟩ := Executable.sits_append cenv q p pc hpl
  exact (h pc h1).mono fun _ hx => hx.elim (fun ⟨_, hf⟩ => hf.elim) .inr

/-- **A straight segment, then the rest** (the x64 pilot's `PartialWpEnv.seg`): a
`vcgen` triple of the segment from the exact state `s` (no shared access),
its fall-through states `R` continuing with the rest at every environment
state above `g` in the fence order, its exits `X` exiting with `E` there. -/
theorem PartialWpEnv.seg [CodeEnv] {env : SharedEnv} [env.FenceMonoX] {q p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} {s : MachineData}
    {g : env.State} {R : MachineData → Prop} {X : Int64 → MachineData → Prop}
    (h : ⦃ fun s' => s' = s ⦄ q ⦃ fun _ => R; X ⦄)
    (hk : ∀ s' g', R s' → SharedEnv.FenceMonoX.le g g' → PartialWpEnv env p Q E s' g')
    (hx : ∀ a s' g', X a s' → SharedEnv.FenceMonoX.le g g' → E a s' g') : PartialWpEnv env (q ++ p) Q E s g := by
  refine PartialWpEnv.of_wpEnv fun pc hpl => ?_
  have hI : env.FenceInv (SharedEnv.FenceMonoX.le g) := fun k g' h => SharedEnv.FenceMonoX.fenceInv g k g' h
  exact eventually_weaken _ _ _ _ (fun _ hx' => hx'.imp (fun ⟨ha, hq, hi⟩ => ⟨ha, hk _ _ hq hi⟩)
    (fun ⟨he, hi⟩ => hx _ _ _ he hi))
    (Executable.wpEnv_of_wp hI (h.le_wp s rfl) g (SharedEnv.FenceMonoX.refl g) pc hpl)

/-- **`ja` after `cmp y, x` is not taken when `x ≤ y`** (the x64 pilot's
`ja_not_taken`). -/
theorem ja_not_taken {x y : BitVec 64} (h : x ≤ y) (af of : Bool) :
    CondCode.a.interp (StatusFlags.from_result (x - y)
      { cf := (x - y).unsigned != x.unsigned - y.unsigned, af := af, of := of }) = false := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned]
  rcases Nat.lt_or_eq_of_le (BitVec.le_def.mp h) with hlt | heq
  · have := x.isLt
    have := y.isLt
    simp [BitVec.toNat_sub]
    omega
  · obtain rfl := BitVec.eq_of_toNat_eq heq
    simp

end MachineWP

#print axioms MachineWP.PartialWpEnv.append_false
#print axioms MachineWP.PartialWpEnv.seg
#print axioms MachineWP.ja_not_taken
