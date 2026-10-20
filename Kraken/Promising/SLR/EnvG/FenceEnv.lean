/-
Whole-thread environment (`EnvG`): **the rule link at
the fence-aware guard `GHyb rel`** — EnvG support for fence-released stores
(`dmb ish; str`). ISA-neutral.

## Why no frozen statement changes

`EnvG` already models fence release: the state's fence
bits `fencedR`/`fencedW` (set by `fence .sy`, cleared by accesses,
`FenceOut`/`LoadOut`/`StoreOut`/`RmwOut`), `effRel A σ k := A.storeKind k =
.rel ∨ (σ.fencedR ∧ σ.fencedW)`, and `StoreOk` lets the plan mark a store as
a release only when `effRel` holds; `NodeRel`/`EnvRel` carry the actual-view
fact `FencedInv`, from which the existing link derives the release split's
timestamp bound. So the *wp* side of a fence-released release store is
already proved by `ThreadRuleRX.ofEnvG`. What was missing is the *rule* side:
`ofEnvG` produces a `ThreadRuleRX` (prepay guard `G₀`, keyed to syntactic
`.rel`), whose `NPSafe` cannot be used with `RelWritesF`
(`theorem1IIPure_of_relWritesF` needs `NPSafeP (GHyb g.rel)`).

## What this file adds

- `relFulfilsLiveF_firstAccessF`: the fence-aware live fulfilment
  (`EvTree.RelFulfilsLiveF`) by a phase-1 tree is its first access: a store
  of the promised message, or a non-release RMW of the location writing the
  promised value.
- `FirstAccess.storeOk_of_noRmw`: walking the fences with the env state, the
  first access is a permitted store, once the RMW branch is refuted at its
  env state.
- `InvG.prepay_of_firstStore`: `InvG.prepay` from the first-store fact (the
  existing proof after `relFulfilsLive_firstStore`; the existing lemma takes the
  `G₀` guard as hypothesis). Now in `EnvG/RuleLink.lean`, where `InvG.prepay`
  is proved from it.
- `InvG.prepayHyb`: `prepay` at `GHyb rel`. The `G₀` disjunct is
  `InvG.prepay`. The fence-aware disjunct fulfils an impure message
  (`¬ Pure (rel w.loc) w.val`): a store is prepaid exactly like a `stlr`
  (`StoreOk` → `prepayGeneric`, which is store-kind agnostic); an RMW is
  impossible (phase-1 RMWs are non-release, so `RmwOk` makes their written
  value pure, read transferred by `NodeRel.readAt_promised`).
- `ThreadRuleRXG.ofEnvGHyb`, `npSafeP_hyb_of_envG(_S)`: the rule (`Inv`,
  `done`, `wp` are `ofEnvG`'s) and `NPSafeP (GHyb rel)` in frame `K2₀` and in
  option (S)'s frame `K2Scope AllocIds`.

Hypothesis beyond `LinkHyps`: `hrel : ∀ st σ, Q st σ → σ.g.rel = rel` (the
env's release predicates are `rel`; `link_relFix` turns any `Q` into one with
fixed predicates). Phase-1 limits are `ofEnvG`'s.
-/
import Kraken.Promising.SLR.EnvG.RuleLink
import Kraken.Promising.SLR.NPSafePHyb

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The fence-aware fulfilment of a phase-1 tree is its first access -/

/-- An access-free tree fulfils no promise, fence-aware. -/
theorem AccessFree.not_relFulfilsLiveF {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {σ : Type} :
    ∀ (tree : EvTree σ) (cx : Ctx), AccessFree tree → ¬ tree.RelFulfilsLiveF A tid iv ts cx
  | .done _, _, _, h => h
  | .fault _, _, _, h => h
  | .choose _ k, cx, ha, ⟨i, h⟩ => AccessFree.not_relFulfilsLiveF (k i) cx (ha i) h
  | .fence k ret, cx, ha, h => AccessFree.not_relFulfilsLiveF (ret ()) (fenceStep cx k) ha h
  | .load .., _, ha, _ => ha
  | .store .., _, ha, _ => ha
  | .rmw .., _, ha, _ => ha

/-- **The fence-aware live fulfilment of a promise by a phase-1 tree is its
first access**: a store of the promised message (leaving every other own
promise to its location above the fulfilled one), or a non-release RMW of the
promised location whose read (in the context it is reached in) writes the
promised value. -/
theorem relFulfilsLiveF_firstAccessF {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {prom : List Time}
    {mem : Memory} {w : Msg} (hts : ts ∈ prom) (hget : mem.get? ts = some w) {σ : Type} :
    ∀ (tree : EvTree σ) (cx : Ctx), cx.prom = prom → cx.mem = mem → Phase1Shape A tree →
      tree.RelFulfilsLiveF A tid iv ts cx →
      FirstAccess (fun _ _ l v => l = w.loc ∧ v = w.val ∧ AboveAt prom mem ts l)
        (fun cxN k noRet l op => l = w.loc ∧ ¬ effRelRmw A k ∧
          ∃ x ∈ readSuccs A iv (fenceOptCtx A cxN) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
            op x.2.1 = some w.val) cx tree
  | .done _, _, _, _, _, h => h
  | .fault _, _, _, _, _, h => h
  | .choose _ k, cx, _, _, hs, ⟨i, h⟩ => AccessFree.not_relFulfilsLiveF (k i) cx (hs.1 i) h
  | .fence k ret, cx, hp, hm, hs, h =>
    relFulfilsLiveF_firstAccessF hts hget (ret ()) (fenceStep cx k) (by rw [fenceStep_prom]; exact hp)
      (by rw [fenceStep_mem]; exact hm) hs h
  | .load _ _ _ ret, _, _, _, hs, ⟨x, _, h⟩ => AccessFree.not_relFulfilsLiveF (ret x.2.1) _ (hs.2.2 _) h
  | .rmw k noRet l op ret, cx, hp, hm, hs, ⟨x, hx, h⟩ => by
    rcases h with h | ⟨new, hop, c', hc', h⟩
    · exact (AccessFree.not_relFulfilsLiveF (ret x.2.1) _ (hs.2.2 _) h).elim
    · rcases h with ⟨⟨-, htc, htc'⟩, hnd⟩ | h
      · obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
        obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
        obtain ⟨hl, hv, -⟩ := fulfil_write_facts hts hget (hp1.trans (hp0.trans hp)) (hm1.trans (hm0.trans hm))
          hc' htc htc' hnd
        subst hv
        exact ⟨hl, hs.2.1, x, hx, hop⟩
      · exact (AccessFree.not_relFulfilsLiveF (ret x.2.1) _ (hs.2.2 _) h).elim
  | .store k xcl l v ret, cx, hp, hm, hs, h => by
    rcases h with ⟨c', hc', ⟨⟨-, htc, htc'⟩, hnd⟩ | h⟩ | h
    · exact fulfil_write_facts hts hget hp hm hc' htc htc' hnd
    · exact (AccessFree.not_relFulfilsLiveF (ret true) _ (hs.2.2 true) h).elim
    · exact (AccessFree.not_relFulfilsLiveF (ret false) _ (hs.2.2 false) h).elim

/-- **The first access is a permitted store** once the RMW branch is refuted
at its env state: walking the fences from `(s, cx)` (any `Φ` the fences
keep), the tree's first access is a store (`FirstStore S`), permitted at the
env state reached. -/
theorem FirstAccess.storeOk_of_noRmw {A : Arch} {tid : Nat} {pl : Plan} {S : StoreKind → Bool → Loc → Val → Prop}
    {R : Ctx → RmwKind → Bool → Loc → (Val → Option Val) → Prop} {Φ : State I → Ctx → Prop}
    (hΦ : ∀ s cx k, Φ s cx → Φ (fenceState s k) (fenceStep cx k))
    (hR : ∀ s cx k l op, R cx k false l op → RmwOk A tid pl s k l op → Φ s cx → False) {σ : Type} :
    ∀ (tree : EvTree σ) (s : State I) (cx : Ctx), FirstAccess S R cx tree → StoreOkAt A tid pl tree s →
      RmwOkAt A tid pl tree s → Φ s cx →
      FirstStore S tree ∧ ∃ s' cx' k xcl l v, S k xcl l v ∧ StoreOk A tid pl s' k xcl l v ∧ Φ s' cx'
  | .fence k ret, s, cx, h, hs, hr, hp =>
    FirstAccess.storeOk_of_noRmw hΦ hR (ret ()) (fenceState s k) (fenceStep cx k) h hs hr (hΦ s cx k hp)
  | .store k xcl l v _, s, cx, h, hs, _, hp => ⟨h, s, cx, k, xcl, l, v, h, hs, hp⟩
  | .rmw k noRet l op _, s, cx, h, _, ⟨hn, hr⟩, hp => by
    subst hn; exact (hR s cx k l op h hr hp).elim
  | .done _, _, _, h, _, _, _ => h.elim
  | .fault _, _, _, h, _, _, _ => h.elim
  | .choose _ _, _, _, h, _, _, _ => h.elim
  | .load .., _, _, h, _, _, _ => h.elim

/-! ## The prepay at the fence-aware guard -/

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`prepay` at the fence-aware guard `GHyb rel`**, for env states whose
release predicates are `rel` (`hrel`). The current guard is `InvG.prepay`.
A fence-aware fulfilment of an impure message is the in-flight instruction's
first store (an RMW would be non-release, so `RmwOk` makes its written value
pure), prepaid as a release store: `StoreOk` (the plan marks the impure
value as a release, which `effRel` permits after `dmb ish`) and
`prepayGeneric`. -/
theorem InvG.prepayHyb (H : LinkHyps A tid pl Q) {rel : Loc → Pred} (hrel : ∀ st σ, Q st σ → σ.g.rel = rel)
    {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvG A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hG : GHyb rel A tid (c.mem.append { w with tid }).2
      { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] } (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvG A tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  rcases hG with h0 | ⟨⟨tree, hex, hrfl⟩, w', hw', himp⟩
  · exact InvG.prepay H rF t₁ w h he hg ht E hm hnp h0
  have hget : (c.mem.append { w with tid }).1.get? (c.mem.append { w with tid }).2 = some { w with tid } :=
    Memory.get?_append_last _ _
  obtain rfl : w' = { w with tid } := Option.some.inj (hw'.symm.trans hget)
  -- the env state of the invariant, at `c`
  have hinv := h
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t₁.st σ := hst ▸ hQ₀
  have hsh := H.shape _ _ hQ tree hex
  have hFA := relFulfilsLiveF_firstAccessF (List.mem_append_right _ (List.mem_singleton_self _)) hget tree _ rfl
    rfl hsh hrfl
  have hJs : StoreOkAt A tid pl tree σ :=
    H.link (TreeJLive.storeOk A tid pl I.State) t₁.st σ tree hQ hex (fun _ _ _ => trivial)
  have hJr : RmwOkAt A tid pl tree σ :=
    H.link (TreeJLive.rmwOk A tid pl I.State) t₁.st σ tree hQ hex (fun _ _ _ => trivial)
  have hN0 := hC.rel.toNodeRel rF (I.deps t₁.st) E hm
  let Φ : State I → Ctx → Prop := fun s P =>
    ∃ cxu, NodeRel tid pl (instrViews t₁ (I.deps t₁.st)) rF c t₁ σ.r g cl s r g cxu ∧ P.views = cxu.views ∧
      P.prom = cxu.prom ++ [c.mem.last + 1] ∧ P.mem = (c.mem.append { w with tid }).1
  have hΦ : ∀ s P k, Φ s P → Φ (fenceState s k) (fenceStep P k) := by
    rintro s P k ⟨cxu, hN, hv, hp, hm'⟩
    exact ⟨_, hN.fence k, by rw [fenceStep_views, fenceStep_views, hv],
      by rw [fenceStep_prom, fenceStep_prom, hp], by rw [fenceStep_mem, hm']⟩
  -- the RMW branch is impossible: its written value would be pure
  have hR : ∀ s P k l op, (l = w.loc ∧ ¬ effRelRmw A k ∧
      ∃ x ∈ readSuccs A (instrViews t₁ (I.deps t₁.st)) (fenceOptCtx A P)
        (if false then .plain else (A.rmwKind k).loadKind) false l false, op x.2.1 = some w.val) →
      RmwOk A tid pl s k l op → Φ s P → False := by
    rintro s P k l op ⟨rfl, hk, x, hx, hop⟩ hok ⟨cxu, hN, hv, hp, hm'⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at hx
    have hrd := hN.readAt_promised (w := { w with tid }) hv hp hm' hx
    obtain ⟨-, hpure, hrl⟩ := hok.2 c g x.1 x.2.1 w.val hN.anchorOk hrd hop
    cases hpl : pl.rel w.loc w.val with
    | true => exact hk (hrl hpl).1
    | false =>
      have hp' := hpure hpl
      have e : s.g.rel = rel := by rw [← hN.ghost.rel, hC.rel.ghost.rel]; exact hrel _ _ hQ
      rw [e] at hp'
      exact himp hp'
  obtain ⟨hFS, -⟩ := FirstAccess.storeOk_of_noRmw hΦ hR tree σ _ hFA hJs hJr ⟨_, hN0, rfl, rfl, rfl⟩
  exact InvG.prepay_of_firstStore H rF t₁ w hinv he hg ht E hm hnp tree hex hFS

end Rule

/-! ## The rule and `NPSafeP` -/

/-- **The rule link at the fence-aware guard**: a `ThreadRuleRXG (GHyb rel)`
from a thread-local invariant `Q` of `EnvG` whose release predicates are
`rel`. `Inv`, `done` and `wp` are `ThreadRuleRX.ofEnvG`'s. -/
def ThreadRuleRXG.ofEnvGHyb {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps A tid pl Q) {rel : Loc → Pred}
    (hrel : ∀ st σ, Q st σ → σ.g.rel = rel)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXG (GHyb rel) A B tid where
  Inv := InvG A tid pl Q
  done h he hg hcl hd := InvG.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvG.wp H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hG := InvG.prepayHyb H hrel rF t₁ w h he hg ht E hm hnp hG

/-- `ofEnvGHyb` and `ofEnvG` have the same invariant. -/
theorem ThreadRuleRXG.ofEnvGHyb_inv {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps A tid pl Q) {rel : Loc → Pred}
    (hrel : ∀ st σ, Q st σ → σ.g.rel = rel)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    (ThreadRuleRXG.ofEnvGHyb H hrel hB).Inv = (ThreadRuleRX.ofEnvG H hB).Inv := rfl

/-- **`NPSafeP (GHyb rel)` from the rule link** (`NPSafeP.of_ruleRXG`),
frame `K2₀`. -/
theorem npSafeP_hyb_of_envG {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps A tid pl Q) {rel : Loc → Pred}
    (hrel : ∀ st σ, Q st σ → σ.g.rel = rel)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvG A tid pl Q cl c r g) :
    NPSafeP (model I) A B tid (GHyb rel) (K2₀ (model I)) n m cl c r g :=
  NPSafeP.of_ruleRXG (ThreadRuleRXG.ofEnvGHyb H hrel hB) n m cl c r g h

/-- **`NPSafeP (GHyb rel)` from the rule link in option (S)'s frame**
`K2Scope AllocIds`, the frame of `theorem1IIPure_of_relWritesF`. -/
theorem npSafeP_hyb_of_envG_S {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps A tid pl Q) {rel : Loc → Pred}
    (hrel : ∀ st σ, Q st σ → σ.g.rel = rel)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvG A tid pl Q cl c r g) :
    NPSafeP (model I) A B tid (GHyb rel) (K2Scope (model I) AllocIds) n m cl c r g :=
  (npSafeP_hyb_of_envG H hrel hB n m h).toAllocIds

end Kraken.Promising.SLR.EnvG

#print axioms Kraken.Promising.SLR.EnvG.InvG.prepayHyb
#print axioms Kraken.Promising.SLR.EnvG.npSafeP_hyb_of_envG_S
