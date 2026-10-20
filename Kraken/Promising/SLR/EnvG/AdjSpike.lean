/-
Own-message
adjacency at release RMWs, the fact a history invariant on `top` needs for
Treiber with two pushers (`treiber2_nodes.kl`). ISA-neutral; only
`AdjSpikeLink.lean` imports it.

## The gap is in the obligation, not only in the facts

The Treiber proof located the missing adjacency in `RmwFactsC` (the step's facts).
The predicate of the CAS's *own* message, though, is established in the
**obligation** of `RmwOkC` (`EnvG/RmwGhost.lean`), at an arbitrary
admissible anchor `c` and an arbitrary read `tr` offered there (`ReadAt`),
for the fresh timestamp `|M| + 1`. Those hypotheses carry **no**
`Memory.atomic` at all: messages to `l` of *other* threads in
`(tr, |M|]` are not excluded either, only own ones (F1/F2) are missing from
`RmwFactsC`. A history predicate on the written message (its predecessor
at `l` is the message read) is therefore unprovable on `EnvGC`, by any
program-level device (tokens included: a predicate sees the memory and its
own resource, not other messages' slots, and the anchor's erasure has an
arbitrary `rF`).

## The fix is additive

Both sites where the link uses the obligation have the fact at hand:

- the fresh release RMW (`NodeRel.rmwC'`, no release in flight): the real
  read, its write's `atomic` (`WriteOk`), the context's `OwnCoh`
  (`Ctx.Inv`) and "no own pending promise" (`hnp0`);
- the prepay (`InvGF.prepay_of_okAtFC`): the certification's fulfilling
  write at `|M| + 1` (its `atomic`, which `relFulfilsLive_firstAccessF`
  currently drops), `OwnCoh` of the unpromised context, and `hn0` (no
  release in flight).

The in-flight fulfilment (`NodeRel.rmwRelC`) uses only the unguarded
conjuncts (`l ∉ gives`), so it needs nothing.

Contents (all proved, std axioms; everything except
`fulfil_write_atomic`/`relFulfilsLive_firstAccessFA` to `EnvG/AdjCore.lean`,
same names and statements, so that the `EnvGC` link and rule are instances):
- `AdjAt tid c g l tr tw`: every message to `l` strictly between `tr` and
  `tw` is an own outstanding non-pending promise.
- `adj_of_readSuccs`, `adjAt_of_ctx` (fresh site), `adjAt_of_promised`
  (prepay site): `AdjAt` from the link's facts (`atomic_between`,
  `ownSeen_of_readSuccs`).
- `AdjAt.loc_ne_of_impure`, `AdjAt.lastAt`: the program-side use: at a
  location whose release predicate is impure everywhere, no message to `l`
  lies strictly between, so `tr` is the latest message to `l` below `tw`.
- `fulfil_write_atomic`, `relFulfilsLive_firstAccessFA`: the prepay site's
  `atomic` (a copy of `relFulfilsLive_firstAccessF` that keeps it).
- `RmwOkCAdj`, `EnvGCAdj`: the sibling environment (obligation with `AdjAt`);
  `RmwOkC.toCAdj`, `envGC_ok_toCAdj`, `envGCAdj_step_iff`: every `EnvGC` program
  is an `EnvGCAdj` program.

The sibling link: `EnvG/AdjSpikeLink.lean` (per tree: `NodeRel.rmwCAdj'`,
now in `EnvG/RmwGhostLink.lean`, supplies `adjAt_of_ctx`), `EnvG/AdjSpikeRule.lean` (rule: the prepay
supplies `adjAt_of_promised`; `ThreadRuleRXF.ofEnvGFCAdj`, giving `NPSafeF`,
whose Theorem 1′ is `theorem1FChain`), `EnvG/AdjSpikeA64.lean` (AArch64:
`ThreadRuleRXF.ofSafelyEnvGFCAdj`, no-fault, init, and `qa64C_toCAdj`).
-/
import Kraken.Promising.SLR.EnvG.AdjCore
import Kraken.Promising.SLR.EnvG.FulfilAtomic
import Kraken.Promising.SLR.EnvG.RmwFailGhostLink
import Kraken.Promising.SLR.EnvG.RmwFailRuleLink
import Kraken.Promising.SLR.EnvG.RmwGhostRule

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! The adjacency (`AdjAt`, `adj_of_readSuccs`, `adjAt_of_ctx`, `adjAt_of_promised`,
`AdjAt.loc_ne_of_impure`, `AdjAt.lastAt`) is in `EnvG/AdjCore.lean`. -/

/-! ## The prepay site: the certification's fulfilling write is atomic -/

/- `fulfil_write_atomic` is in `EnvG/FulfilAtomic.lean` (same name
and statement, now the second half of `fulfil_write_atomicTR`). -/

/-- **`relFulfilsLive_firstAccessF` keeping the fulfilling write's
atomicity** (copy; the RMW branch additionally exposes
`x.2.2.mem.atomic l tid x.1 ts`, which `adjAt_of_promised` consumes). -/
theorem relFulfilsLive_firstAccessFA {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {prom : List Time}
    {mem : Memory} {w : Msg} (hts : ts ∈ prom) (hget : mem.get? ts = some w) {σ : Type} :
    ∀ (tree : EvTree σ) (cx : Ctx), cx.prom = prom → cx.mem = mem → Phase1ShapeF tree →
      tree.RelFulfilsLive A tid iv ts cx →
      FirstAccess (fun _ _ l v => l = w.loc ∧ v = w.val ∧ AboveAt prom mem ts l)
        (fun cxN k noRet l op => l = w.loc ∧ effRelRmw A k ∧ AboveAt prom mem ts l ∧
          ∃ x ∈ readSuccs A iv (fenceOptCtx A cxN) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
            op x.2.1 = some w.val ∧ x.2.2.mem.atomic l tid x.1 ts = true) cx tree
  | .done _, _, _, _, _, h => h
  | .fault _, _, _, _, _, h => h
  | .choose _ k, cx, _, _, hs, ⟨i, h⟩ => AccessFree.not_relFulfilsLive (k i) cx (hs.1 i) h
  | .fence k ret, cx, hp, hm, hs, h =>
    relFulfilsLive_firstAccessFA hts hget (ret ()) (fenceStep cx k) (by rw [fenceStep_prom]; exact hp)
      (by rw [fenceStep_mem]; exact hm) hs h
  | .load _ _ _ ret, _, _, _, hs, ⟨x, _, h⟩ => AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h
  | .rmw k noRet l op ret, cx, hp, hm, hs, ⟨x, hx, h⟩ => by
    rcases h with h | ⟨new, hop, c', hc', h⟩
    · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h).elim
    · rcases h with ⟨⟨hk, htc, htc'⟩, hnd⟩ | h
      · obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
        obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
        obtain ⟨hl, hv, hab⟩ := fulfil_write_facts hts hget (hp1.trans (hp0.trans hp)) (hm1.trans (hm0.trans hm))
          hc' htc htc' hnd
        subst hv
        have hle : ts ≤ x.2.2.mem.last := by
          rw [hm1.trans (hm0.trans hm)]; exact mem.last_le_of_get?_eq_some hget
        exact ⟨hl, hk, hab, x, hx, hop, fulfil_write_atomic hc' htc htc' hle⟩
      · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h).elim
  | .store k xcl l v ret, cx, hp, hm, hs, h => by
    rcases h with ⟨c', hc', ⟨⟨-, htc, htc'⟩, hnd⟩ | h⟩ | h
    · exact fulfil_write_facts hts hget hp hm hc' htc htc' hnd
    · exact (AccessFree.not_relFulfilsLive (ret true) _ (hs.2.2 true) h).elim
    · exact (AccessFree.not_relFulfilsLive (ret false) _ (hs.2.2 false) h).elim

/-! The sibling environment (`RmwOkCAdj`, `EnvGCAdj`, `RmwOkC.toCAdj`,
`envGC_ok_toCAdj`, `envGCAdj_step_iff`) is in `EnvG/AdjCore.lean`. -/

end Kraken.Promising.SLR.EnvG
