/-
**The x64 purity link for `NPSafeF`**: the program-
independent assembly step of `EnvG/X64CmpxPublic.lean`, moved here so other
x64 programs whose rules give `NPSafeF` (failing release-kind RMWs, the `F`
link `EnvG/X64RmwFail.lean`) can use it without importing the cmpxchg
spinlock.

- `CmpxPublic.final_of_relPureSafelyQX_tsoF` (name unchanged by the move):
  `final_of_relPureSafelyQX_tso` (`EnvG/RelPureEnvX64.lean`) with Theorem 1′
  for `NPSafeF` taken from the open `Theorem1FChain` (`EnvG/RmwFailRule.lean`)
  hypothesis `hchain`, in place of `theorem1IIPure`.
- **`CmpxPublic.final_of_relPureSafelyQX_tsoF'`** (moved unchanged
  from the x64 Treiber proof's `EnvG/X64RmwFailGhost.lean`): the same with `hchain`
  discharged by `theorem1FChain` (`EnvG/RmwFailChain.lean`), so
  unconditional. The x64 default for programs whose rules give `NPSafeF`
  (the x64 counterpart of `final_of_relPureSafelyF`,
  `EnvG/A64RmwFailFinal.lean`).
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvX64
import Kraken.Promising.SLR.EnvG.RmwFailRule
import Kraken.Promising.SLR.EnvG.RmwFailChain
import Kraken.Promising.NTFreeTso

namespace Kraken.Promising.X64.EnvG.CmpxPublic

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike
open Kraken.Promising.X64.EnvG

/-! ## Adequacy for `NPSafeF` from the open chain -/

/-- **`final_of_relPureSafelyQX_tso` for `NPSafeF`**, from the open
`Theorem1FChain` (`hchain`): the same scope and purity argument (x64
all-release specifications, `Arch.tso`), with Theorem 1′ for `NPSafeF`. -/
theorem final_of_relPureSafelyQX_tsoF {fuel : Nat} (hchain : Theorem1FChain (I := isa) Arch.tso fuel)
    {states : List isa.State} {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost}
    {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (model isa) Arch.tso B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hs : ∀ s ∈ states, ∃ tid, (sp tid).Holds s := fun s hs => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    exact ⟨i, h0 i _ (List.getElem?_eq_getElem hi)⟩
  have hstep : ∀ tid st tree, (sp tid).Holds st → isa.exec st = some tree →
      tree.RelWrites Arch.tso (fun l v => Pred.Pure (g₀.rel l) v) ∧ tree.All (sp tid).Holds :=
    fun tid _ tree h hex => ⟨EvTree.NoNT.relWrites tso_storeKind_rel
      (EvTree.noNT_tso_of_relWrites_false (relPureSpecQX_step (sp tid) h tree hex).1),
      (relPureSpecQX_step (sp tid) h tree hex).2⟩
  have hpure : PromisePure Arch.tso fuel states initMem g₀.rel :=
    promisePure_of_relWrites (fun st => ∃ tid, (sp tid).Holds st)
      (fun _ hc' tid t ht => ⟨tid, relWrites_reach (fun tid st => (sp tid).Holds st) hstep h0 hc' tid t ht⟩)
      (fun st tree ⟨tid, hJ⟩ hex => (hstep tid st tree hJ hex).1)
  exact final_of_virtual hc hf
    (hchain B states initMem rF g₀ (fun _ hc' => Config.ntFree_of_noNTInv (noNTInv_of_specQX sp) hs hc') hE hpend
      hpure hsafe c hc ⟨c, .refl c, hf⟩) hfin

/-! ## Adequacy for `NPSafeF`, unconditional -/

/-- **The x64 purity/adequacy link for `NPSafeF` rules, unconditional**:
`final_of_relPureSafelyQX_tsoF` with Theorem 1′ for `NPSafeF` discharged by
`theorem1FChain` (the x64 counterpart of `final_of_relPureSafelyF`). -/
theorem final_of_relPureSafelyQX_tsoF' {fuel : Nat}
    {states : List isa.State} {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost}
    {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (model isa) Arch.tso B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relPureSafelyQX_tsoF (theorem1FChain Arch.tso fuel) hE hpend sp h0 hsafe hc hf hfin

end Kraken.Promising.X64.EnvG.CmpxPublic
