/-
Part 4: **the AArch64 purity/adequacy link for
`NPSafeF` rules**.

`final_of_relPureSafelyF` is `final_of_relPureSafely` (`EnvG/RelPureEnvA64.lean`)
with `NPSafeF` per thread in place of `NPSafe`: Theorem 1′ for `NPSafeF` is
`theorem1FChain` (`EnvG/RmwFailChain.lean`, closed), purity
(`PromisePure`) comes from the threads' `RelPureSpec`s exactly as in
`final_of_relWritesJ`. Rules from `ThreadRuleRXF.ofSafelyEnvGF` /
`ThreadRuleRXF.ofSafelyEnvGFC` (failing release RMWs, `casal`) feed it. The
x64 counterpart is `CmpxPublic.final_of_relPureSafelyQX_tsoF`
(`EnvG/RelPureEnvX64F.lean`).
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.EnvG.RmwFailChain

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike

/-- **`final_of_relPureSafely` for `NPSafeF` rules**: one `RelPureSpec A g₀.rel`
per thread id, holding at the thread's initial state, and `NPSafeF` per
thread; Theorem 1′ is `theorem1FChain`. -/
theorem final_of_relPureSafelyF (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpec A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (model isa) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hstep : ∀ tid st tree, (sp tid).Holds st → isa.exec st = some tree →
      tree.RelWrites A (fun l v => Pred.Pure (g₀.rel l) v) ∧ tree.All (sp tid).Holds :=
    fun tid _ tree h hex => relPureSpec_step (sp tid) h tree hex
  have hpure : PromisePure A fuel states initMem g₀.rel :=
    promisePure_of_relWrites (fun st => ∃ tid, (sp tid).Holds st)
      (fun _ hc' tid t ht => ⟨tid, relWrites_reach (fun tid st => (sp tid).Holds st) hstep h0 hc' tid t ht⟩)
      (fun st tree ⟨tid, hJ⟩ hex => (hstep tid st tree hJ hex).1)
  exact final_of_virtual hc hf
    (theorem1FChain A fuel B states initMem rF g₀ hH hE hpend hpure hsafe c hc ⟨c, .refl c, hf⟩) hfin

end Kraken.Promising.AArch64.EnvG
