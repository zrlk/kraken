import Kraken.Promising.SLR.Theorem1D1
import Kraken.Promising.SLR.Cond3Proof

/-!
# Theorem 1′ for the SLR model, unconditional

`theorem1IIPure` closes `theorem1II_pure` (every case of the induction
step) with condition (3) (`cond3`: promise validity at every annotated
configuration). The only program-level input left inside `Theorem1IIPure` is
`PromisePure` (O5), discharged per program (e.g. `SwpInv.swp_promisePure`,
`promisePure_tso` for NT-free x64 programs).

`theorem1IIPure'` is the same theorem for any prepay guard `G`, virtual guard
`GV` and K2 frame `K` that satisfy `GuardOK`/`K2OK` with `G ≤ GV`; `theorem1IIPure` is its instance at `G₀`, `GRF`, `K2₀`.

`theorem1IIPureS'` is the same for per-thread tokens with a
step guard `S` (`NPSafePS`); `theorem1IIPure'` is its corollary at
`StepGuard.top`. `theorem1IIPureXS'` is the same again for an
erasure `Er` and a promise obligation `Ob` with `ChainExt Er Ob`;
`theorem1IIPureS'` is its instance at `Erase`, `ObPure`.
-/

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- **Theorem 1′ with an erasure, an obligation and a step guard**: `Theorem1IIPureXS'` for every `Er`, `Ob` with `ChainExt Er Ob`
(e.g. `Erase ∧ X` and purity with freshness, `SLR/LoadClaimFinal.lean`). -/
theorem theorem1IIPureXS' {G GV : PrepayGuard I} {K : K2Frame (model I)} {Er : ErasureP I}
    {S : StepGuard (modelErase I Er)} {Ob : PromiseOb} (ErOK : ChainExt Er Ob)
    (GOK : GuardOK G) (GVOK : GuardOK GV)
    (hGV : ∀ A tid ts (t : Thread I) mem, G A tid ts t mem → GV A tid ts t mem) (KOK : K2OK (model I) K)
    [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIPureXS' (I := I) G GV K Er S Ob A fuel :=
  theorem1II_pure' ErOK GOK GVOK hGV fun states initMem => cond3' KOK A fuel states initMem

/-- **Theorem 1′ with a step guard**: `theorem1IIPure'` for
per-thread tokens `NPSafePS … S`, for every step guard `S`; the chain
discharges the guard at its two `stepAt` sites from `StepFulP`. At
`S := StepGuard.ful _` this is Theorem 1′ for the failing-RMW route's `NPSafeF`
(`EnvG/RmwFailChain.lean`, `theorem1FChain`). -/
theorem theorem1IIPureS' {G GV : PrepayGuard I} {K : K2Frame (model I)} {S : StepGuard (model I)}
    (GOK : GuardOK G) (GVOK : GuardOK GV)
    (hGV : ∀ A tid ts (t : Thread I) mem, G A tid ts t mem → GV A tid ts t mem) (KOK : K2OK (model I) K)
    [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIPureS' (I := I) G GV K S A fuel :=
  theorem1IIPureXS' (Er := Erase) (S := S) (Ob := ObPure) chainExt_Erase GOK GVOK hGV KOK A fuel

/-- Theorem 1′ (SLR instance), generic in the prepay guard `G`, the virtual
guard `GV` and the K2 frame `K`, with no remaining hypotheses beyond those
inside `Theorem1IIPure'` (scope `NTFree`, initial erasure, `PromisePure'`,
per-thread `NPSafeP`). -/
theorem theorem1IIPure' {G GV : PrepayGuard I} {K : K2Frame (model I)} (GOK : GuardOK G) (GVOK : GuardOK GV)
    (hGV : ∀ A tid ts (t : Thread I) mem, G A tid ts t mem → GV A tid ts t mem) (KOK : K2OK (model I) K)
    [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIPure' (I := I) G GV K A fuel :=
  (theorem1IIPureS' GOK GVOK hGV KOK (S := StepGuard.top _) A fuel).toP

/-- Theorem 1′ (SLR instance), with no remaining hypotheses beyond those
inside `Theorem1IIPure` (scope `NTFree`, initial erasure, `PromisePure`,
per-thread `NPSafe`). The instance of `theorem1IIPure'` at `G₀`, `GRF`,
`K2₀` (`npgen`, `SLR/NPSafePGen.lean`). -/
theorem theorem1IIPure [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIPure (I := I) A fuel := by
  npgen theorem1IIPure'

end Kraken.Promising.SLR
