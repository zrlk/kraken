/-
**hello.w's global owned-words map on the threads abort path** (x86-64; the
twin of `Spike/Lib/A64HelloOwnGAb.lean`, at the template of
`Spike/Lib/X64WakeOwnGAb.lean`): on wake's path predicate `WakePh.AbP` (the
pc in `[scc_rt_abort, scc_rt_thr_worker)`, the return address word at
`R.addr 8` holding the caller's `ra`, `%rsp` in the band `[-32, 8]`),
`ownGH` (`Spike/Lib/X64HelloOwnG.lean`) picks the instance by `ra` and the
band (`WakePh.BandIn`, `BandOut`). The path's block and node facts
(`WakePh.abP_blk`, `abP_node`, `BlkW.agree_of`, `NodeW.agree_of`) are
program independent and reused.

- `good2bH_ab`, `goodWH_ab`: where `ownGH` picks `own2bH` and `ownH` on the
  path (the spawn failure's return address `.Lwc_main.x27`, the second
  `scc_rt_alloc_tcb`'s abort's `.Lscc_rt_alloc_tcb.x6`).

**Deviation from the A64 file.** The return address is the private word at
`R.addr 8` (`WakePh.raAt_iff`), not `x30`; the labels are hello's x86-64
ones (A64: `.L22_wc_main.sp15`, `.L3_scc_rt_alloc_tcb.sp13`). A64's
`good2aH_ab` has no consumer and is not twinned.
-/
import Spike.Lib.X64HelloOwnGNode
import Spike.Lib.X64WakeOwnGAb

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (AbP BandOut raAt_iff not_spPool_of_band)

variable {L : RuntimeLayout} {s : State}

/-- The two return addresses on the path differ. -/
private theorem ra_neH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (L.lab ".Lscc_rt_alloc_tcb.x6").toBitVec ≠ (L.lab ".Lwc_main.x27").toBitVec := by
  rw [hlab _ 4199282 (by rw [← codeT_eq]; decide +kernel), hlab _ 4203909 (by rw [← codeT_eq]; decide +kernel)]
  decide

/-- **`ownGH` picks `own2bH` on the path** from `wc_main`'s spawn failure. -/
theorem good2bH_ab (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {R : Region}
    (h : AbP L R (L.lab ".Lwc_main.x27").toBitVec s) : Good2bH L s :=
  .inr (.inr ⟨h.1, (raAt_iff h _).2 rfl, fun ⟨hx, _⟩ => ra_neH hlab ((raAt_iff h _).1 hx)⟩)

/-- **`ownGH` picks `ownH` on the path** from any other caller, or from
`scc_rt_alloc_tcb`'s abort off the pool stacks. -/
theorem goodWH_ab {R : Region} {ra : BitVec 64} (h : AbP L R ra s)
    (h6 : ra = (L.lab ".Lscc_rt_alloc_tcb.x6").toBitVec → BandOut L R)
    (h27 : ra ≠ (L.lab ".Lwc_main.x27").toBitVec) : GoodWH L s := by
  refine .inr (.inl ⟨h.1, fun ⟨hx, hp⟩ => ?_, fun hx => h27 ((raAt_iff h _).1 hx).symm⟩)
  exact not_spPool_of_band (h6 ((raAt_iff h _).1 hx).symm) h.2.2.2 hp

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.good2bH_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.good2bH_ab

/-- info: 'Spike.Lib.X64.HelloPh.goodWH_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.goodWH_ab
