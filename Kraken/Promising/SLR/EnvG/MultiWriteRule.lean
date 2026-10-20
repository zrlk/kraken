/-
Whole-thread environment (`EnvG`), phase 3: **the rule link for
code with multi-write trees** (`STP`). ISA-neutral; the AArch64 instance is
`EnvG/MultiWriteA64.lean`.

`LinkHyps3` is `LinkHyps2` (`MultiRule.lean`) whose `shape` admits, beside
the phase-1 and phase-2 trees, the **phase-3 trees** `Phase3Shape`: a prefix
of loads then a sequence of stores (`MultiWriteS`, no RMW), with no
release-kind write on any path (`NoRelWrite`). The invariant is the existing
`InvG` unchanged.

- `wp`: phase-1 trees and trees under an in-flight release as in phase 1,
  phase-2 trees through the multi link (`treeJ_envG_eraseWPRDM_start`),
  phase-3 trees through the re-anchoring link (`treeJ_envG_eraseWPRDW_start`,
  `MultiWriteLink.lean`); all end in the phase-1 `PostS`, turned into
  `WpPostR` by `InvG.wpPost`.
- `prepay`: phase-2 and phase-3 trees fulfil no promise with a live release
  (`NoRelWrite.not_relFulfilsLive`); phase-1 trees as before.
- `ThreadRuleRX.ofEnvG3`, `npSafe_of_envG3`, `noFaultRule_ofEnvG3_struct`;
  `LinkHyps2.to3` (so `ofEnvG3` subsumes `ofEnvG2` and `ofEnvG`).

**Phase-3 limits**: loads only before the first store; no RMW in a
multi-write tree; no release-kind store in a multi-access tree (x64 stores
are releases under `Arch.tso`, so x64 vector stores are not covered); no
exclusive stores (`StoreOk` asks
`xcl = false`: `STXP` is LL/SC, deferred); `CASP` (two RMWs) is not covered.
-/
import Kraken.Promising.SLR.EnvG.MultiRule
import Kraken.Promising.SLR.EnvG.MultiWriteLink
import Kraken.Promising.SLR.EnvG.Answers

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The phase-3 shape -/

/-- **The phase-3 tree shape**: a prefix of loads, then a sequence of stores
(no RMW), and no release-kind write on any path. -/
def Phase3Shape (A : Arch) {σ : Type} (tree : EvTree σ) : Prop :=
  MultiWriteS True (fun _ _ => True) (fun _ => False) True tree ∧ NoRelWrite A tree

/-- Phase-3 trees satisfy the write link's side conditions without a release
in flight. -/
theorem Phase3Shape.none {A : Arch} {σ : Type} {tree : EvTree σ} (h : Phase3Shape A tree) :
    MultiWriteS (LokS none) (SokS none) (fun _ => False) (LokS none) tree :=
  MultiWriteS.mono (fun _ => rfl) (fun _ _ _ => .inl rfl) (fun _ h => h) (fun _ => rfl) h.1

/-! ## The hypotheses -/

/-- **The hypotheses of the phase-3 rule link** (`LinkHyps2` with phase-3
trees admitted). -/
structure LinkHyps3 (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree →
    Phase1Shape A tree ∨ Phase2Shape A tree ∨ Phase3Shape A tree
  link : ∀ (J : TreeJLive (EnvG I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- The phase-2 hypotheses are phase-3 hypotheses. -/
theorem LinkHyps2.to3 {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop} (H : LinkHyps2 A tid pl Q) :
    LinkHyps3 A tid pl Q :=
  ⟨H.valid, fun st σ h tree hex => (H.shape st σ h tree hex).imp_right .inl, H.link⟩

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`wp`** for phase-3 code: the phase-1 link at phase-1 trees and under an
in-flight release, the multi link at phase-2 trees, the re-anchoring link at
phase-3 trees. -/
theorem InvG.wp3 (H : LinkHyps3 A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvG A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvG A tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start2
  by_cases h1 : Phase1Shape A tree ∨ pf ≠ none
  · have ha := hsa tree hex h1
    have hW := H.link (TreeJLive.eraseWPRDS (nodeSimS_envG (A := A) (pl := pl) (iv := instrViews t (I.deps t.st))
      (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS) Q) t.st σ tree hQ hex (fun _ _ h => h)
    exact EvTree.EraseWPRD.mono (InvG.wpPost rF hC ht E hr) tree _ _ _
      (treeJ_envG_eraseWPRDS_start hC.rel (I.deps t.st) hS E hm hW ha)
  · simp only [not_or, ne_eq, Decidable.not_not] at h1
    obtain ⟨h1, rfl⟩ := h1
    rcases (H.shape _ _ hQ tree hex).resolve_left h1 with h2 | h3
    · have hW := H.link (TreeJLive.eraseWPRDM (nodeSimM_envG (A := A) (pl := pl)
        (iv := instrViews t (I.deps t.st)) (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS) Q)
        t.st σ tree hQ hex (fun _ _ h => h)
      exact EvTree.EraseWPRD.mono (InvG.wpPost rF hC ht E hr) tree _ _ _
        (treeJ_envG_eraseWPRDM_start hC.rel (I.deps t.st) hS E hm hW h2.none)
    · have hW := H.link (TreeJLive.eraseWPRDW (nodeSimW_envG (A := A) (pl := pl)
        (iv := instrViews t (I.deps t.st)) (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hC.rel.ht hm hS) Q)
        t.st σ tree hQ hex (fun _ _ h => h)
      exact EvTree.EraseWPRD.mono (InvG.wpPost rF hC ht E hr) tree _ _ _
        (treeJ_envG_eraseWPRDW_start hC.rel (I.deps t.st) hS E hm hW h3.none)

/-- **`InvG.prepay_of_firstStore` for phase-3 code**: `InvG.prepay_of_firstStore2`
with `LinkHyps3`, an instance of the generic `InvG.prepay_of_firstStoreG`
(`RuleLink.lean`; formerly a third copy of its proof). -/
theorem InvG.prepay_of_firstStore3 (H : LinkHyps3 A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res}
    {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvG A tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) (tree : EvTree I.State) (hex : I.exec t₁.st = some tree)
    (hsh : Phase1Shape A tree)
    (hFS : FirstStore (fun _ _ l v => l = w.loc ∧ v = w.val ∧
      AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
        (c.mem.append { w with tid }).2 l) tree) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvG A tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) :=
  InvG.prepay_of_firstStoreG H.valid
    (fun st σ tree hQ hex => H.link (TreeJLive.storeOk A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial))
    rF t₁ w h he hg ht E hm hnp tree hex hsh hFS

/-- **`prepay`** for phase-3 code: phase-2 and phase-3 trees fulfil no
promise with a live release; phase-1 trees as in `InvG.prepay`. -/
theorem InvG.prepay3 (H : LinkHyps3 A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvG A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvG A tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨tree, hex, hrfl⟩ := hrel
  have hsh : Phase1Shape A tree ∨ Phase2Shape A tree ∨ Phase3Shape A tree := by
    obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
    obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
    exact H.shape _ _ (hst ▸ hQ₀) tree hex
  rcases hsh with hsh | hsh | hsh
  · exact InvG.prepay_of_firstStore3 H rF t₁ w h he hg ht E hm hnp tree hex hsh
      (relFulfilsLive_firstStore (List.mem_append_right _ (List.mem_singleton_self _)) (Memory.get?_append_last _ _)
        tree _ rfl rfl hsh hrfl)
  · exact absurd hrfl (NoRelWrite.not_relFulfilsLive tree _ hsh.2)
  · exact absurd hrfl (NoRelWrite.not_relFulfilsLive tree _ hsh.2)

end Rule

/-- **The phase-3 rule link**: a `ThreadRuleRX` from a thread-local
invariant `Q` of `EnvG` whose code may have multi-write trees
(`LinkHyps3`), with the existing invariant `InvG`. -/
def ThreadRuleRX.ofEnvG3 {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps3 A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid where
  Inv := InvG A tid pl Q
  done h he hg hcl hd := InvG.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvG.wp3 H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvG.prepay3 H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafe` from the phase-3 rule link** (`NPSafe.of_ruleRX`). -/
theorem npSafe_of_envG3 {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps3 A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvG A tid pl Q cl c r g) :
    NPSafe (model I) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofEnvG3 H hB) n m cl c r g h

/-- **The phase-3 no-fault rule from fault-free trees** (as
`noFaultRule_ofEnvG_struct`): unconditional in the thread's promises. -/
theorem noFaultRule_ofEnvG3_struct {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps3 A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HS : ∀ st σ tree, Q st σ → I.exec st = some tree → tree.NoFault) :
    NoFaultRule (ThreadRuleRX.ofEnvG3 H hB) :=
  NoFaultRule.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp
    exact HS t.st σ tree hQ hex

end Kraken.Promising.SLR.EnvG
