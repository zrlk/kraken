/-
**hello.w's global owned-words map on the threads abort path** (AArch64;
twin of `A64WakeOwnGAb`): on wake's path predicate
`WakePh.AbP` (the pc in `[scc_rt_abort, scc_rt_thr_worker)`, `x30` the
caller's return address `ra`, `sp` in the 48 bytes below the caller's),
`ownGH` picks the instance by `ra` and the band (`WakePh.BandIn`,
`BandOut`). The path's block and node facts (`WakePh.abP_blk`, `abP_node`,
`BlkW.agree_of`, `NodeW.agree_of`) are program independent and reused.

- `good2aH_ab`, `good2bH_ab`, `goodWH_ab`: where `ownGH` picks each
  instance on the path (the spawn failure's return address `.L22_wc_main.sp15`).
-/
import Spike.Lib.A64HelloOwnGNode
import Spike.Lib.A64WakeOwnGAb

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh (AbP BandIn BandOut spPool_of_band not_spPool_of_band)

variable {L : RuntimeLayout} {s : State}

/-- The two return addresses on the path differ. -/
private theorem ra_neH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec ≠ (L.lab ".L22_wc_main.sp15").toBitVec := by
  rw [hlab _ 2164996 (by rw [← codeT_eq]; decide +kernel), hlab _ 2169912 (by rw [← codeT_eq]; decide +kernel)]
  decide

/-- **`ownGH` picks `own2aH` on the path** from `scc_rt_alloc_tcb`'s abort
on a pool stack. -/
theorem good2aH_ab {R : Region} (h : AbP L R (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec s) (hb : BandIn L R) :
    Good2aH L s :=
  .inr (.inr ⟨h.1, h.2.1, spPool_of_band hb h.2.2⟩)

/-- **`ownGH` picks `own2bH` on the path** from `wc_main`'s spawn failure. -/
theorem good2bH_ab (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {R : Region}
    (h : AbP L R (L.lab ".L22_wc_main.sp15").toBitVec s) : Good2bH L s :=
  .inr (.inr ⟨h.1, h.2.1, fun ⟨hx, _⟩ => ra_neH hlab (hx.symm.trans h.2.1)⟩)

/-- **`ownGH` picks `ownH` on the path** from any other caller, or from
`scc_rt_alloc_tcb`'s abort off the pool stacks. -/
theorem goodWH_ab {R : Region} {ra : BitVec 64} (h : AbP L R ra s)
    (h13 : ra = (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec → BandOut L R)
    (h15 : ra ≠ (L.lab ".L22_wc_main.sp15").toBitVec) : GoodWH L s := by
  refine .inr (.inl ⟨h.1, fun ⟨hx, hp⟩ => ?_, fun hx => h15 (h.2.1.symm.trans hx)⟩)
  exact not_spPool_of_band (h13 (h.2.1.symm.trans hx)) h.2.2 hp

/-- info: 'Spike.Lib.A64.HelloPh.good2bH_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.good2bH_ab

end Spike.Lib.A64.HelloPh
