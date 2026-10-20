/-
Part 2: **the rule link of the claim-conditional
environment with failing in-flight release RMWs** (F × C). ISA-neutral. New
file; copies of `RmwFailRuleLink.lean`'s `InvGF.wp`/`InvGF.prepay` over
`EnvGC` (`RmwGhostRule.lean`'s `InvGR.wpC`/`InvGR.prepay_of_okAtC` with the
totality condition dropped).

- `LinkHypsFC`: `LinkHypsF` over `EnvGC` **without** `giveOk`
  (`RelRmwGiveOk`), i.e. `LinkHypsRC` with `Phase1ShapeF` trees. The
  invariant `InvGF` and the core `CoreAtF` are reused unchanged (they do not
  mention the environment).
- `InvGF.wpFC`: through `treeJ_envGC_eraseWPRDSF_start`; a leaf with the
  in-flight escape (`Alive`: the in-flight RMW failed) goes to `WpPostRF`'s
  left disjunct.
- `InvGF.prepay_of_okAtFC`/`InvGF.prepayFC`: `RmwOkC` at the first access and
  `prepayGenericRmwC` (no give-away side condition); the first access is
  found by `relFulfilsLive_firstAccessF` (any operation).
- `ThreadRuleRXF.ofEnvGFC`, `npSafeF_of_envGFC`: the rule, giving `NPSafeF`
  (Theorem 1′ for it: `theorem1FChain`, `EnvG/RmwFailChain.lean`).
- `noFaultRuleF_ofEnvGFC_struct`: no-fault from fault-free trees.

`InvGF.wpFC` and `InvGF.prepay_of_okAtFC` are instances of
the adjacency link's `InvGF.wpFCAdj`/`InvGF.prepay_of_okAtFCAdj` (`EnvG/AdjSpikeRule.lean`,
now imported here) through `LinkHypsFC.toFCAdj` and `RmwOkAtC.toCAdj`.

Phase-1 limits otherwise apply (single-access trees, read-side acquire only;
a release RMW cannot forward what it claims).
-/
import Kraken.Promising.SLR.EnvG.RmwFailGhostLink
import Kraken.Promising.SLR.EnvG.RmwFailRuleLink
import Kraken.Promising.SLR.EnvG.RmwGhostRule
import Kraken.Promising.SLR.EnvG.AdjSpikeRule

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- **The hypotheses of the rule link of `EnvGC` with failing release RMWs**:
`LinkHypsRC` with `Phase1ShapeF` trees (no totality, no give-away side
condition). -/
structure LinkHypsFC (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeF tree
  link : ∀ (J : TreeJLive (EnvGC I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- The `RC` link's hypotheses are the `FC` link's. -/
theorem LinkHypsRC.toFC {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    (H : LinkHypsRC A tid pl Q) : LinkHypsFC A tid pl Q :=
  ⟨H.valid, fun st σ hQ tree hex => (H.shape st σ hQ tree hex).toF, H.link⟩

/-- `RmwOkAtC` is `RmwOkAtCAdj` (`RmwOkC.toCAdj` at the first RMW). -/
theorem RmwOkAtC.toCAdj {A : Arch} {tid : Nat} {pl : Plan} {σ : Type} :
    ∀ (tree : EvTree σ) (s : State I), RmwOkAtC A tid pl tree s → RmwOkAtCAdj A tid pl tree s
  | .fence k ret, s, h => RmwOkAtC.toCAdj (ret ()) (fenceState s k) h
  | .rmw .., _, h => ⟨h.1, h.2.toCAdj⟩
  | .done _, _, _ => trivial
  | .fault _, _, _ => trivial
  | .choose .., _, _ => trivial
  | .load .., _, _ => trivial
  | .store .., _, _ => trivial

/-- The `FC` link's hypotheses are the `FCAdj` link's (an `EnvGCAdj`
judgment is an `EnvGC` one, `TreeJLive.ofCAdj`). -/
theorem LinkHypsFC.toFCAdj {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    (H : LinkHypsFC A tid pl Q) : LinkHypsFCAdj A tid pl Q :=
  ⟨H.valid, H.shape, fun J st σ tree hQ hex hP => H.link J.ofCAdj st σ tree hQ hex hP⟩

section RuleFC

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`wp`** for `EnvGC` with failing release RMWs (`InvGF.wp` over
`EnvGC`). -/
theorem InvGF.wpFC (H : LinkHypsFC A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvGF tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostRF (InvGF tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) :=
  InvGF.wpFCAdj H.toFCAdj rF t tree h he hg ht hex E hm hnp

/-- **`prepay` for `EnvGC` with failing release RMWs, from the first-access
judgments** (`InvGR.prepay_of_okAtC` with `CoreAtF`, `Phase1ShapeF` and
`relFulfilsLive_firstAccessF`). -/
theorem InvGF.prepay_of_okAtFC (hvalid : pl.Valid)
    (hshape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeF tree)
    (hok : ∀ st σ tree, Q st σ → I.exec st = some tree → StoreOkAt A tid pl tree σ ∧ RmwOkAtC A tid pl tree σ)
    {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvGF tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvGF tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) :=
  InvGF.prepay_of_okAtFCAdj hvalid hshape
    (fun st σ tree hQ hex => (hok st σ tree hQ hex).imp_right (RmwOkAtC.toCAdj tree σ)) rF t₁ w h he hg
    ht E hm hnp hrel

/-- **`prepay`** for `EnvGC` with failing release RMWs. -/
theorem InvGF.prepayFC (H : LinkHypsFC A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvGF tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvGF tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) :=
  InvGF.prepay_of_okAtFC H.valid H.shape
    (fun st σ tree hQ hex =>
      ⟨H.link (TreeJLive.storeOkC A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial),
        H.link (TreeJLive.rmwOkC A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial)⟩)
    rF t₁ w h he hg ht E hm hnp hrel

end RuleFC

/-- **The rule link of `EnvGC` with failing release RMWs**: a
`ThreadRuleRXF` from a thread-local invariant `Q` of `EnvGC` (`LinkHypsFC`)
and the postcondition at halted threads (`hB`). -/
def ThreadRuleRXF.ofEnvGFC {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsFC A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid where
  Inv := InvGF tid pl Q
  done h he hg hcl hd := InvGF.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvGF.wpFC H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvGF.prepayFC H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafeF` from the rule link of `EnvGC` with failing release RMWs**
(`NPSafeF.of_ruleRXF`). -/
theorem npSafeF_of_envGFC {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsFC A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvGF tid pl Q cl c r g) :
    NPSafeF (model I) A B tid n m cl c r g :=
  NPSafeF.of_ruleRXF (ThreadRuleRXF.ofEnvGFC H hB) n m cl c r g h

/-- **The no-fault rule for the `FC` link from fault-free trees**
(`noFaultRuleF_ofEnvGF_struct`). -/
theorem noFaultRuleF_ofEnvGFC_struct {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsFC A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HS : ∀ st σ tree, Q st σ → I.exec st = some tree → tree.NoFault) :
    NoFaultRuleF (ThreadRuleRXF.ofEnvGFC H hB) :=
  NoFaultRuleF.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGF.q_at rF t h he hg ht E hnp
    exact HS t.st σ tree hQ hex

end Kraken.Promising.SLR.EnvG
