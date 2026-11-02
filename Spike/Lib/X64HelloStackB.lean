/-
**hello's stack-bound checks** (x86-64; the twin of `Spike/Lib/A64HelloStackB.lean`'s live part): the region
depths and bands the thread and main segments ask for, checked against the 16 KiB stacks they run on.

- `bandTiH_of`: the band `BandTiH` (`wc_main`'s frame at the call, `-144 … -136`) from `BoxPureH`'s `R.base + 96`
  the first stack's top (as `H2Rt.bandSp3H_of`).
- `childB_r1Of`: the handed stack's top below `2 ^ 64`, 16-aligned, and at least the thread worker's 264 bytes, at
  the runtime's second stack `r1Of` (16384 bytes), from its place in the pool.

No absolute address appears in a statement here.

## Differences from the AArch64 version

- `BandTiH` is `wc_main`'s `%rsp` past the `call` and the callee's `pushq` (`R.addr (-136)`, `R.addr (-144)`;
  AArch64 `[-192, -144]`), and its region's base is `96` below the first stack's top (AArch64 `80`), as
  `X64HelloRootHPD`.
- The thread worker's re-based region reaches `-264` (`X64HelloWorkerSegP`'s `ChildD.ok`; AArch64 `-272`), so
  `childB_r1Of`'s size bound is `264`.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `helloD_mainB`, `wcR_loH`.
-/
import Spike.Lib.X64HelloWcSp4W
import Spike.Lib.Rt.X64RtPreChild

namespace Spike.Lib.X64.HelloPh.StackB

open Spike.Lib (Region)
open Spike.Lib.X64.Rt (RuntimeLayout)

/-- **The band `[-144, -136]` of a region 96 below the first stack's top on the pool** (`BandTiH`; the twin of
`H2Rt.bandSp3H_of`). -/
theorem bandTiH_of {L : RuntimeLayout} {R : Region} (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) :
    Spike.Lib.X64.HelloPh.WcSp4W.BandTiH L R := by
  intro k h1 h2
  have hB := R.base.isLt
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Spike.Lib.Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hk : ((R.addr k).toNat : Int) = R.base.toNat + k := by
    rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
      Int.emod_eq_of_lt (by omega) (by omega)]
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  omega

/-- **The handed stack's bounds at the runtime's second stack** (at `r1 := r1Of L.lab`): in the pool (`hsub`), so
its top fits; 16-aligned, as the first stack's base; 16384 bytes, at least the thread worker's `264`. -/
theorem childB_r1Of (L : RuntimeLayout) (hsub : (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).Sub L.Λ.stackPool) :
    (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).lo + (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).size < 2 ^ 64 ∧
      ((Spike.Lib.X64.Rt.PreChild.r1Of L.lab).lo + (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).size) % 16 = 0 ∧
      264 ≤ (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).size := by
  have hf := L.pool_fit
  have hal := L.stacks_al
  obtain ⟨-, h2⟩ := hsub
  refine ⟨by omega, ?_, by show 264 ≤ 16384; decide⟩
  show ((Spike.Lib.X64.Flow.Ret0.stacksA L.lab + 16384#64).toNat + 16384) % 16 = 0
  rw [L.lab_stacks, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end Spike.Lib.X64.HelloPh.StackB

/-- info: 'Spike.Lib.X64.HelloPh.StackB.bandTiH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StackB.bandTiH_of

/-- info: 'Spike.Lib.X64.HelloPh.StackB.childB_r1Of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StackB.childB_r1Of
