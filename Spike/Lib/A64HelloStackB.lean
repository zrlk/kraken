/-
**hello's stack-bound checks** (AArch64): the region depths the thread and
main segments ask for, checked against the 16 KiB stacks they run on.

- 5f (thread): `seg_thrWorker`'s `R.lo ≤ -272` is met by `SegR.childP_of_clone` at region `childR top (-272)` given
  the handed stack's top below `2 ^ 64`, 16-aligned, and at least 272 bytes; `childB_r1Of` gives these at the
  runtime's second stack `r1Of` (16384 bytes), from its place in the pool (`HelloRootBase.hsub`).
- 5f' (main): `wc_main`'s region `wcR R helloD` reaches `-336` (`wcMidW_wcGH`, frame 144 + `scc_rt_alloc_tcb`'s
  callee 192) and `-192` (`wcResW_wcGH`); main's new-stack region `helloLsw` holds `wc_main`'s plus `scc_rt_main`'s
  frame `80` and fits the 16 KiB main stack (`helloD_mainB`, `wcR_loH`); the band `BandTiH` (`bandTiH_of`, as
  `H2Rt.bandSp3H_of`) from `BoxPureH`'s `R.base + 80` the first stack's top.

No absolute address appears in a statement here.
-/
import Spike.Lib.A64HelloStartH0G
import Spike.Lib.A64HelloWcSp4W
import Spike.Lib.Rt.A64RtPreChild

namespace Spike.Lib.A64.HelloPh.StackB

open Spike.Lib (Region)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)

/-- **The main depths' bounds** (row 5f'): `wc_main`'s region reaches `scc_rt_alloc_tcb`'s callee (`-336`) and the
reserve's (`-192`), main's new-stack region holds it under `scc_rt_main`'s frame `80`, inside the 16 KiB stack. -/
theorem helloD_mainB : 336 ≤ helloD ∧ 192 ≤ helloD ∧ 80 + helloD ≤ helloLsw ∧ helloLsw ≤ 16384 := by
  decide

/-- **`wc_main`'s region at `helloD` reaches `-336`** (`wcMidW_wcGH`'s `R.lo ≤ -336`, hence `wcResW_wcGH`'s
`-192`). -/
theorem wcR_loH (R : Region) : (Spike.Lib.A64.Flow.HelloM.wcR R helloD).lo ≤ -336 := by
  show -helloD ≤ -336
  decide

/-- **The band `[-192, -144]` of a region 80 below the first stack's top on the pool** (`BandTiH`; row 5f', the
twin of `H2Rt.bandSp3H_of`). -/
theorem bandTiH_of {L : RuntimeLayout} {R : Region} (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384) :
    Spike.Lib.A64.HelloPh.WcSp4W.BandTiH L R := by
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

/-- **The handed stack's bounds at the runtime's second stack** (row 5f; `SegR.childP_of_clone`'s `htop`, `hal`,
`hsz` at `r1 := r1Of L.lab`): in the pool (`hsub`), so its top fits; 16-aligned, as the first stack's base; 16384
bytes. -/
theorem childB_r1Of (L : RuntimeLayout) (hsub : (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).Sub L.Λ.stackPool) :
    (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).lo + (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).size < 2 ^ 64 ∧
      ((Spike.Lib.A64.Rt.PreChild.r1Of L.lab).lo + (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).size) % 16 = 0 ∧
      272 ≤ (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).size := by
  have hf := L.pool_fit
  have hal := L.stacks_al
  obtain ⟨-, h2⟩ := hsub
  refine ⟨by omega, ?_, by show 272 ≤ 16384; decide⟩
  show ((Spike.Lib.A64.Flow.Ret0.stacksA L.lab + 16384#64).toNat + 16384) % 16 = 0
  rw [L.lab_stacks, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end Spike.Lib.A64.HelloPh.StackB

/-- info: 'Spike.Lib.A64.HelloPh.StackB.helloD_mainB' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StackB.helloD_mainB

/-- info: 'Spike.Lib.A64.HelloPh.StackB.bandTiH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StackB.bandTiH_of

/-- info: 'Spike.Lib.A64.HelloPh.StackB.childB_r1Of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StackB.childB_r1Of
