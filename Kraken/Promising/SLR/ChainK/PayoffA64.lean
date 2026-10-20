/-
**The K-world chain payoff: the Stage 2 hubs over `ReachableK`, AArch64 side**
. The citable forms of the clones of
`ChainK/HubsA64.lean`: every reachability hypothesis is the fuel-free
`ReachableK A`, and each theorem is the clone at `fuel := 0` (see
`ChainK/Payoff.lean`). `spin_counter_core_reachK` and
`ticket_counter_core_reachK` are ISA-generic; they live here because their
sources import the AArch64 side.
-/
import Kraken.Promising.SLR.ChainK.HubsA64

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.Live.Bridge

/-- **`final_of_relPureSafely` over `ReachableK`** (the K-world chain payoff;
`final_of_relPureSafelyK` at `fuel := 0`). -/
theorem final_of_relPureSafely_reachK (A : Arch) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, ReachableK A (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpec A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model isa) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : ReachableK A (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relPureSafelyK A 0 hH hE hpend sp h0 hsafe hc hf hfin

/-- **`final_of_relPureSafelyD` over `ReachableK`** (the K-world chain payoff;
`final_of_relPureSafelyDK` at `fuel := 0`). -/
theorem final_of_relPureSafelyD_reachK (A : Arch) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, ReachableK A (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpec A g₀.rel) (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).StrictSized)
    (hnp : ∀ tid, Kraken.Executable.noPairs (sp tid).e = true)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsD (ds tid) s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model isa) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : ReachableK A (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relPureSafelyDK A 0 hH hE hpend sp ds hsz hnp h0 hsafe hc hf hfin

end Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken Kraken.Promising Kraken.Promising.Live.Bridge
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon

/-- **`spin_counter_core` over `ReachableK`** (the K-world chain payoff;
`spin_counter_coreK` at `fuel := 0`). -/
theorem spin_counter_core_reachK {I : ISA} {A : Arch} (N : Nat) {l c : BitVec 64}
    (hdisj : Decls.overlaps l 4 c 4 = false) {states : List I.State} {initMem : List (Loc × Val)}
    (hN : states.length = N) (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    {cfg : Config I} (hc : ReachableK A (Config.init states initMem) cfg) (hf : cfg.final = true)
    (hrun : l ≠ c → 0 < N → (∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) cfg →
        (spinGhost ⟨l, 4⟩ (lockPred N ⟨l, 4⟩ ⟨c, 4⟩ (ghostSys N l c).K (ghostSys N l c).F)
          (poolRes (Config.init states initMem).mem N ⟨c, 4⟩ (ghostSys N l c).K)).Le g' →
        cfg.threads.size = states.length → (∀ tid, cfg.Done tid → Post N ⟨l, 4⟩ (ghostSys N l c).K (rF' tid)) →
        cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N) → cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  spin_counter_coreK (fuel := 0) N hdisj hN hC0 hc hf hrun

end Kraken.Promising.SLR.EnvG.CasSmoke

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.Live.Bridge

variable {I : ISA} [I.LawfulState]

/-- **`ticket_counter_core` over `ReachableK`** (the K-world chain payoff;
`ticket_counter_coreK` at `fuel := 0`). -/
theorem ticket_counter_core_reachK (A : Arch)
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List I.State} {initMem : List (Loc × Val)} (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (H : Nat → Bool → I.State → Prop)
    (hNT : ∀ cf, ReachableK A (Config.init states initMem) cf → cf.NTFree A)
    (hstep : ∀ (_ : Locs (tkSys N x o c)) tid b st tree, H tid b st → I.exec st = some tree →
      (TreeJ.disp A (fun l v => Pred.Pure ((tkGhost (Config.init states initMem).mem (tkSys N x o c)).rel l) v)
        ⟨x, 4⟩ (N + 1) (fun s b => H tid b s)).W tree b)
    (h0 : ∀ (_ : Locs (tkSys N x o c)) tid s, states[tid]? = some s → H tid false s)
    (hsafe : ∀ (hL : Locs (tkSys N x o c)) tid s, states[tid]? = some s → ∀ n m,
      NPSafeP (modelX I (disp (tkSys N x o c) hL.xo).TX) A (fun cf r _ => TPost (tkSys N x o c) cf r) tid
        G₀ (K2Scope (model I) AllocIds) n m True (Config.init states initMem)
        (thRes (Config.init states initMem).mem (tkSys N x o c) tid) (tkGhost (Config.init states initMem).mem
          (tkSys N x o c)))
    {cfg : Config I} (hc : ReachableK A (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  ticket_counter_coreK A (fuel := 0) N x o c hxo hxc hoc hN32 hN hX0 hO0 hC0 H hNT hstep h0 hsafe hc hf

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.AArch64.EnvG.final_of_relPureSafelyD_reachK
#print axioms Kraken.Promising.SLR.EnvG.CasSmoke.spin_counter_core_reachK
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.ticket_counter_core_reachK
