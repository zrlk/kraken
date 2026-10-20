/-
**The K-world chain payoff: the Stage 2 hubs over `ReachableK`, x64 side**. The
citable forms of the clones of
`ChainK/HubsX64.lean`: every reachability hypothesis is the fuel-free
`ReachableK A`, and each theorem is the clone at `fuel := 0` (see
`ChainK/Payoff.lean`).
-/
import Kraken.Promising.SLR.ChainK.HubsX64

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.Live.Bridge

/-- **`final_of_relPureSafelyX` over `ReachableK`** (the K-world chain payoff;
`final_of_relPureSafelyXK` at `fuel := 0`). -/
theorem final_of_relPureSafelyX_reachK (A : Arch) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, ReachableK A (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecX A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model isa) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : ReachableK A (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relPureSafelyXK A 0 hH hE hpend sp h0 hsafe hc hf hfin

/-- **`final_of_relPureSafelyQX_tso` over `ReachableK`** (the K-world chain payoff;
`final_of_relPureSafelyQX_tsoK` at `fuel := 0`). -/
theorem final_of_relPureSafelyQX_tso_reachK {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model isa) Arch.tso B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : ReachableK Arch.tso (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relPureSafelyQX_tsoK 0 hE hpend sp h0 hsafe hc hf hfin

/-- **`final_of_relPureSafelyQX_tsoD` over `ReachableK`** (the K-world chain payoff;
`final_of_relPureSafelyQX_tsoDK` at `fuel := 0`). -/
theorem final_of_relPureSafelyQX_tsoD_reachK {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).Sized)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsD (ds tid) s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model isa) Arch.tso B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : ReachableK Arch.tso (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relPureSafelyQX_tsoDK 0 hE hpend sp ds hsz h0 hsafe hc hf hfin

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.X64.EnvG.final_of_relPureSafelyX_reachK
#print axioms Kraken.Promising.X64.EnvG.final_of_relPureSafelyQX_tsoD_reachK
