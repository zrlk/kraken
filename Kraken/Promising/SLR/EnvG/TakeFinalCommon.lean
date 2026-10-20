/-
**Adequacy for programs with taking threads, ISA-neutral part**.

- `final_of_relWritesJS`: `final_of_relWritesJ` (`EnvG/RelPureEnv.lean`)
  with `NPSafeP … G₀ (K2Scope (model I) AllocIds)` per thread in place of
  `NPSafe`, through `theorem1IIPure_G₀_S` (`SLR/TakeRuleThread.lean`).
  Threads proved by the existing rules enter by `NPSafe.toP`
  (`K2₀.toScope`), taking threads by `npSafeP_of_safelyEnvGT` (AArch64) or
  `npSafeP_of_safelyEnvGTX` (x64).

Users: `EnvG/TakeFinal.lean` (`final_of_relPureSafelyS`, AArch64) and
`EnvG/TakeX64Final.lean` (whose `final_of_relWritesJSX` is now an alias of
this theorem). See `EnvG/TakeFinal.lean`'s module docstring for why purity
carries over to taking threads unchanged.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnv
import Kraken.Promising.SLR.TakeRuleThread
import Kraken.Promising.SLR.Theorem1FinalP

namespace Kraken.Promising.SLR

open Kraken Kraken.Promising

variable {I : ISA}

/-- **Adequacy for programs with taking threads, from a per-thread purity
step**: `final_of_relWritesJ` at `NPSafeP … G₀ (K2Scope AllocIds)`. -/
theorem final_of_relWritesJS [I.LawfulState] (A : Arch) (fuel : Nat) {states : List I.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config I → Res → Ghost → Prop}
    {Φ : Config I → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (J : Nat → I.State → Prop)
    (hstep : ∀ tid st tree, J tid st → I.exec st = some tree →
      tree.RelWrites A (fun l v => Pred.Pure (g₀.rel l) v) ∧ tree.All (J tid))
    (h0 : ∀ tid s, states[tid]? = some s → J tid s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model I) A B tid G₀ (K2Scope (model I) AllocIds) n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hpure : PromisePure A fuel states initMem g₀.rel :=
    promisePure_of_relWrites (fun st => ∃ tid, J tid st) (fun _ hc' tid t ht => ⟨tid,
      relWrites_reach J hstep h0 hc' tid t ht⟩) (fun st tree ⟨tid, hJ⟩ hex => (hstep tid st tree hJ hex).1)
  obtain ⟨v, rF', g', hv, E', hle, hB⟩ :=
    theorem1IIPure_G₀_S A fuel B states initMem rF g₀ hH hE hpend (promisePure_iff_G₀.mp hpure) hsafe c hc
      ⟨c, .refl c, hf⟩
  obtain rfl : v = c := Config.VirtualOfG.eq_of_final hf hv
  exact hfin rF' g' E' hle (by rw [Reachable.size_eq hc, Config.init_size]) hB

end Kraken.Promising.SLR
