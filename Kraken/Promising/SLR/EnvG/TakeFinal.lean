/-
**Part 4: adequacy for programs with taking
threads** (the consumer of `npSafeP_of_safelyEnvGT`).

- `final_of_relWritesJS` (ISA-neutral; in
  `EnvG/TakeFinalCommon.lean`, same name and statement): `final_of_relWritesJ`
  (`EnvG/RelPureEnv.lean`) with `NPSafeP … G₀ (K2Scope (model I) AllocIds)`
  per thread in place of `NPSafe`, through `theorem1IIPure_G₀_S`
  (`SLR/TakeRuleThread.lean`). Threads proved by the existing rules enter by
  `NPSafe.toP` (`K2₀.toScope`), taking threads by `npSafeP_of_safelyEnvGT`.
- `final_of_relPureSafelyS` (AArch64): `final_of_relPureSafely`
  (`EnvG/RelPureEnvA64.lean`) likewise: one `RelPureSpec` per thread.

**Purity carries over unchanged (no `relPureT`).** `PromisePure` (the (O5)
hypothesis of Theorem 1′) and its per-instruction form `RelWrites` speak
about the machine's writes and the *initial* ghost's release predicates
`g₀.rel` only. A take changes acquire ids, slots and the thread's resource,
never `rel` (`Ghost.Le` fixes it, `takeGhost` keeps it), and it is not
visible to the program's code at all. So the purity environment
`SharedEnv.relPure A g₀.rel` and its `vcgen` proofs apply to taking threads
as they are; the guard is `G₀` (`PromisePure' G₀ = PromisePure`,
`promisePure_iff_G₀`).

No other Theorem 1′ variant is needed: the take route's rules are at `G₀`
(`ThreadRuleRXGS G₀`); the `_F_S`/`_Hyb_S` variants (`SLR/Theorem1FinalP.lean`)
would be needed only for fence-released *and* taking programs, which have no
link yet.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.EnvG.TakeFinalCommon
import Kraken.Promising.SLR.TakeRuleThread
import Kraken.Promising.SLR.Theorem1FinalP

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR

/-- **Adequacy for AArch64 programs with taking threads, purity by `vcgen`**:
`final_of_relPureSafely` at `NPSafeP … G₀ (K2Scope AllocIds)`. -/
theorem final_of_relPureSafelyS (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpec A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model isa) A B tid G₀ (K2Scope (model isa) AllocIds) n m True (Config.init states initMem)
        (rF tid) g₀)
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relWritesJS A fuel hH hE hpend (fun tid st => (sp tid).Holds st)
    (fun tid _ tree h hex => relPureSpec_step (sp tid) h tree hex) h0 hsafe hc hf hfin

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.SLR.final_of_relWritesJS
#print axioms Kraken.Promising.AArch64.EnvG.final_of_relPureSafelyS
