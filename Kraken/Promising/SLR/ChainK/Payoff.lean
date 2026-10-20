/-
**The K-world chain payoff: the Stage 2 hubs over `ReachableK`, ISA-neutral part**
. The clones (`ChainK/Final.lean`,
`ChainK/PromisePure.lean`) state the hubs over `ReachableKF A fuel`, an
`abbrev` for `ReachableK A` whose `fuel` is phantom. The theorems here are
the citable forms: every reachability hypothesis is the fuel-free
`ReachableK A` (the fuel-free reachability along `SuccKind` steps), and each
is the clone at `fuel := 0`. `ReachableK` contains the executable machine
(`ReachableK.of_reachable`) and the semantic one
(`ReachableK.of_reachableSem'` with `Config.init_bnd`).

The `PromisePureK`/`PromisePure'K` hypotheses keep a fuel argument (`0`
here): it is phantom too, since `PathK` steps along `succsK`, which ignores
it, but `PathK A fuel` is a different type for each `fuel`.
`promisePure_of_relWrites_reachK` produces it from a fuel-free invariant.
-/
import Kraken.Promising.SLR.ChainK.PromisePure

namespace Kraken.Promising.SLR

open Kraken Kraken.Promising Kraken.Promising.Live.Bridge

variable {I : ISA}

/-- **`final_of_virtual` over `ReachableK`** (the K-world chain payoff; `final_of_virtualK`
at `fuel := 0`). -/
theorem final_of_virtual_reachK [I.LawfulState] {A : Arch} {states : List I.State} {initMem : List (Loc × Val)}
    {B : Config I → Res → Ghost → Prop} {g₀ : Ghost} {Φ : Config I → Prop} {c : Config I}
    (hc : ReachableK A (Config.init states initMem) c) (hf : c.final = true)
    (hT : ∃ v rF' g', (VirtualRel.ii A).rel c v ∧ Erase rF' g' (fun _ => False) v ∧ g₀.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g')
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_virtualK (fuel := 0) hc hf hT hfin

/-- **Theorem 1′ (generic in `G`, `GV`, `K`) over `ReachableK`** (the K-world chain
payoff; `theorem1IIPure'K` at `fuel := 0`, unfolded): `Theorem1IIPure'` with
the scope hypothesis and the conclusion over `ReachableK` and `Config.LiveK`. -/
theorem theorem1IIPure'_reachK {G GV : PrepayGuard I} {K : K2Frame (model I)} (GOK : GuardOK G)
    (GVOK : GuardOK GV) (hGV : ∀ A tid ts (t : Thread I) mem, G A tid ts t mem → GV A tid ts t mem)
    (KOK : K2OK (model I) K) [I.LawfulState] (A : Arch)
    (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost)
    (hH : ∀ c, ReachableK A (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g.pend)
    (hpure : PromisePure'K G A 0 states initMem g.rel)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model I) A B tid G K n m True (Config.init states initMem) (rF tid) g)
    (c : Config I) (hc : ReachableK A (Config.init states initMem) c) (hlive : c.LiveK A) :
    ∃ v rF' g', c.VirtualOfG GV A v ∧ Erase rF' g' (fun _ => False) v ∧ g.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g' :=
  theorem1IIPure'K GOK GVOK hGV KOK A 0 B states initMem rF g hH hE hpend hpure hsafe c hc hlive

/-- **Adequacy from Theorem 1′ (SLR instance) over `ReachableK`** (the K-world chain
payoff; `final_of_theorem1PureK` at `fuel := 0`, with its `Theorem1IIPureK`
hypothesis discharged by `theorem1IIPureK`). -/
theorem final_of_theorem1Pure_reachK [I.LawfulState] {A : Arch}
    {states : List I.State} {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost}
    {B : Config I → Res → Ghost → Prop} {Φ : Config I → Prop}
    (hH : ∀ c, ReachableK A (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (hpure : PromisePureK A 0 states initMem g₀.rel)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config I} (hc : ReachableK A (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_theorem1PureK (theorem1IIPureK A 0) hH hE hpend hpure hsafe hc hf hfin

/-- **`PromisePureK` from a fuel-free invariant** (the K-world chain payoff;
`promisePure_of_relWritesK` at `fuel := 0`). -/
theorem promisePure_of_relWrites_reachK [I.LawfulState] {A : Arch} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (Jinv : I.State → Prop)
    (hJ : ∀ c, ReachableK A (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv t.st)
    (hcell : ∀ st tree, Jinv st → I.exec st = some tree → tree.RelWrites A fun l v => Pred.Pure (rel l) v) :
    PromisePureK A 0 states initMem rel :=
  promisePure_of_relWritesK (fuel := 0) Jinv hJ hcell

/-- **`final_of_relWritesJ` over `ReachableK`** (the K-world chain payoff;
`final_of_relWritesJK` at `fuel := 0`). -/
theorem final_of_relWritesJ_reachK [I.LawfulState] (A : Arch) {states : List I.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config I → Res → Ghost → Prop}
    {Φ : Config I → Prop}
    (hH : ∀ c, ReachableK A (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (J : Nat → I.State → Prop)
    (hstep : ∀ tid st tree, J tid st → I.exec st = some tree →
      tree.RelWrites A (fun l v => Pred.Pure (g₀.rel l) v) ∧ tree.All (J tid))
    (h0 : ∀ tid s, states[tid]? = some s → J tid s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config I} (hc : ReachableK A (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relWritesJK A 0 hH hE hpend J hstep h0 hsafe hc hf hfin

end Kraken.Promising.SLR

#print axioms Kraken.Promising.SLR.theorem1IIPure'_reachK
#print axioms Kraken.Promising.SLR.final_of_theorem1Pure_reachK
#print axioms Kraken.Promising.SLR.final_of_relWritesJ_reachK
