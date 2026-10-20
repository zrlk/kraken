/-
The failing-RMW route smoke tests:

1. `dirs_phase1F` accepts `casal` (which the release-RMW extension's `dirs_phase1R` rejects,
   `RmwRelSmoke.lean`), so the `casal` lock worker's code is `F`-phase-1.
2. **The VC of a release-kind CAS that may fail**, on the CAS lock's plan
   (`casPlan`): the TTAS worker's acquire `casa` replaced by `casal` (as
   `ldaxr/stlxr`-free lock acquisition with release semantics, the AArch64
   twin of x64 `lock cmpxchg`, which TSO makes release-kind). The written
   value `1` is pure, so a prepaid promise of it gives nothing away; the
   RMW is release-kind (`effRelRmw`), so the release-RMW extension's `Phase1ShapeR` rejects it
   (its operation fails when the lock is taken). `vc_casal` is `vc_casa`'s
   proof with the claim condition from `acqRel`: both outcomes, failure
   (`Fr` kept) and success (`H1`), are covered.
-/
import Kraken.Promising.SLR.EnvG.A64RmwFail
import Kraken.Promising.SLR.EnvG.CasVC
import Kraken.Promising.SLR.EnvG.CasStepRmwU
import Kraken.AArch64.Parser

namespace Kraken.Promising.AArch64.EnvG.RmwFailSmoke

open Kraken Kraken.Promising Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser

/-- A release CAS (rejected by `dirs_phase1R`). -/
def relCas : Program := parseAArch64("
    casal w3, w2, [x0]
")

/-- `dirs_phase1F` accepts it. -/
example [layout : _root_.Layout] : DirsPhase1F (layout relCas) := by dirs_phase1F relCas

/-- The release swap and fetch-add of `RmwRelSmoke` stay accepted. -/
def relRmws : Program := parseAArch64("
    mov w3, #0
    swpl w3, w2, [x0]
    mov w4, #1
    ldaddl w4, w5, [x1]
    casal w3, w2, [x0]
")

example [layout : _root_.Layout] : DirsPhase1F (layout relRmws) := by dirs_phase1F relRmws

end Kraken.Promising.AArch64.EnvG.RmwFailSmoke

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon

variable {P : Sys} {tid : Nat}

/-- **VC `casal w2, w3, [x0]`** (`w2 = 0`, `w3 = 1`, acquire-release, on
`casPlan`): permitted (the lock share, the pure written value `1`, the claim
condition from `acqRel`), and every outcome either fails (`Fr` kept) or takes
the lock (`H1`). The RMW is release-kind and may fail: outside the release-RMW extension's
`Phase1ShapeR`, inside `Phase1ShapeF`. -/
theorem vc_casal (hN0 : 0 < P.N) (σ : State isa) (h : Fr P tid σ) :
    (E P tid).ok (.rmw .acqRel P.Lk.addr P.Lk.bytes casOp) σ ∧
      ∀ old (σ' : State isa), (E P tid).step (.rmw .acqRel P.Lk.addr P.Lk.bytes casOp) σ old σ' →
        (BitVec.setWidth 32 old ≠ 0 ∧ Fr P tid σ') ∨ (BitVec.setWidth 32 old = 0 ∧ H1 P tid σ') := by
  have hU := stepRmwU Arch.armv8 tid (casPlan P tid)
  obtain ⟨hW, hf, hC, hfw, hz⟩ := h
  have hnf : ∀ tr, ¬ Fwded σ.vs P.Lk tr := fun tr ⟨f, hf', _⟩ => by rw [hfw] at hf'; cases hf'
  refine ⟨⟨?_, fun c g tr old new _ _ hop => ⟨fun _ => .inl rfl, fun _ => ?_, fun hr => ?_⟩⟩, ?_⟩
  · show 0 < (σ.r.wr P.Lk).q
    have := one_div_pos hN0; have := hf.2.2; grind
  · obtain ⟨-, rfl⟩ := casOp_some hop
    rw [hW.1]; exact lockPred_pure (by decide)
  · obtain ⟨-, rfl⟩ := casOp_some hop
    rw [casPlan_rel_one] at hr; cases hr
  intro old σ' hs
  obtain ⟨c, tr, hanc, hrd, hvle, -, hacq, hbr⟩ := hU _ _ _ _ _ _ _ hs
  rcases hbr with ⟨hop, hr⟩ | ⟨new, tw, hop, -, hun, -, hcoh, hr⟩
  · refine .inl ⟨fun h0 => ?_, hW.mono hanc.ghost, hr ▸ hf, hr ▸ hC, by rw [rmw_fail_getFwd hs hop]; exact hfw,
      hr ▸ hz⟩
    simp [rmwOpBits, h0] at hop
  obtain ⟨hz0, rfl⟩ := casOp_some hop
  refine .inr ⟨hz0, hW.mono hanc.ghost, ?_⟩
  obtain ⟨rF, E'⟩ := hanc.erase
  obtain ⟨R, R', hprod, hgb⟩ := World.lock_claim' (hW.mono hanc.ghost) E' hrd.val hz0 hun
  have hval := valid_claimed (tid := tid) E' hanc.lt P.Lk tr
  rw [hprod] at hval
  obtain ⟨_, -, hr⟩ := hr
  have hr' : σ'.r = (σ.r.op (R.op R')).addW P.Lk (1#128, tw) := by
    rw [hr, Plan.afterRmw, Plan.after, casPlan_rel_one, hprod]; rfl
  have hacq' := hacq rfl (hnf tr)
  have hR'C : ∀ S, Pool P.N P.C P.K P.F S R → (R'.wr P.C).q = 0 := fun S hpool => by
    have h1 := hval.1 P.C
    change (R.wr P.C).q + (R'.wr P.C).q ≤ 1 at h1
    have := (R'.wr P.C).nonneg; rw [hpool.1] at h1; grind
  rcases hgb with ⟨k, S, ts, hpool, hX, hmax, hk, hts⟩ | hbad
  · exact ⟨S, k, R, σ.r, R', tw, hr', hf, hC, hR'C S hpool, hz, hcoh, hpool,
      .inl ⟨ts, hX, hmax, hk, Nat.le_trans hts hacq'.1, Nat.le_trans hts hacq'.2⟩⟩
  · obtain ⟨S, hpool⟩ := hbad.2
    exact ⟨S, 0, R, σ.r, R', tw, hr', hf, hC, hR'C S hpool, hz, hcoh, hpool, .inr hbad⟩

/-- The `casal` is release-kind on AArch64 (so the release-RMW extension's `Phase1ShapeR` asks
its operation to be total, which `casOp` is not). -/
example : effRelRmw Arch.armv8 .acqRel := rfl

end Kraken.Promising.SLR.EnvG.CasSmoke
