/-
Whole-thread environment (`EnvG`), phase 2 (the multi-access link prototype): **the rule
link for code with load-prefix trees**. ISA-neutral; the AArch64 instance is
`EnvG/MultiA64.lean`.

`LinkHyps2` is `LinkHyps` (`RuleLink.lean`) whose `shape` admits, beside the
phase-1 trees (`Phase1Shape`), the **phase-2 trees** `Phase2Shape`: a prefix
of loads then at most one access (`MultiAccessS`), with **no release-kind
write on any path** (`NoRelWrite`: no store of release kind after
`A.storeKind`, no release-kind RMW). The invariant is the existing `InvG`
unchanged (its core `CoreAt` does not mention the shape).

- `wp`: a phase-1 tree, or any tree while a release is in flight (the
  in-flight facts make it `SingleAccessS`), goes through the phase-1 link
  `treeJ_envG_eraseWPRDS_start`; a phase-2 tree without a release in flight
  through `treeJ_envG_eraseWPRDM_start` (`MultiLink.lean`). Both end in the
  phase-1 `PostS`, which `InvG.wpPost` turns into `WpPostR` (the body of
  `InvG.wp`).
- `prepay`: a phase-2 tree fulfils no promise with a live release
  (`NoRelWrite.not_relFulfilsLive`), so the obligation is the phase-1 one at
  phase-1 trees (`InvG.prepay_of_firstStore2`, `InvG.prepay_of_firstStore`
  with the tree's shape as a hypothesis instead of `LinkHyps.shape`).
- `ThreadRuleRX.ofEnvG2`, `npSafe_of_envG2`; `LinkHyps.to2` (the phase-1
  hypotheses are phase-2 hypotheses, so `ofEnvG2` subsumes `ofEnvG`).

**Phase-2 limits** (prototype): loads before the access; no release-kind
write in a multi-access tree (so the x64 load-then-store instructions, whose
stores are releases under `Arch.tso`, are not covered: they need loads under
an in-flight release); multiple writes per
tree (`STP`, `CASP`, x64 vector stores) are not covered.
-/
import Kraken.Promising.SLR.EnvG.RuleLink
import Kraken.Promising.SLR.EnvG.MultiLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The phase-2 shape -/

/-- **No release-kind write** on any path: every store's kind is not a
release after `A.storeKind`, and no RMW is of release kind. -/
def NoRelWrite (A : Arch) {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, NoRelWrite A (k i)
  | .fence _ ret => NoRelWrite A (ret ())
  | .load _ _ _ ret => ∀ v, NoRelWrite A (ret v)
  | .store k _ _ _ ret => A.storeKind k ≠ .rel ∧ ∀ b, NoRelWrite A (ret b)
  | .rmw k _ _ _ ret => ¬ effRelRmw A k ∧ ∀ v, NoRelWrite A (ret v)

/-- **A tree with no release-kind write fulfils no promise with a live
release.** -/
theorem NoRelWrite.not_relFulfilsLive {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {σ : Type} :
    ∀ (tree : EvTree σ) (cx : Ctx), NoRelWrite A tree → ¬ tree.RelFulfilsLive A tid iv ts cx
  | .done _, _, _, h => h
  | .fault _, _, _, h => h
  | .choose _ k, cx, hn, ⟨i, h⟩ => NoRelWrite.not_relFulfilsLive (k i) cx (hn i) h
  | .fence k ret, cx, hn, h => NoRelWrite.not_relFulfilsLive (ret ()) (fenceStep cx k) hn h
  | .load _ _ _ ret, _, hn, ⟨x, _, h⟩ => NoRelWrite.not_relFulfilsLive (ret x.2.1) _ (hn _) h
  | .store k xcl l v ret, cx, hn, h => by
    rcases h with ⟨c', -, ⟨⟨hk, -⟩, -⟩ | h⟩ | h
    · exact hn.1 hk
    · exact NoRelWrite.not_relFulfilsLive (ret true) _ (hn.2 true) h
    · exact NoRelWrite.not_relFulfilsLive (ret false) _ (hn.2 false) h
  | .rmw k noRet l op ret, cx, hn, ⟨x, _, h⟩ => by
    rcases h with h | ⟨new, -, c', -, ⟨⟨hk, -⟩, -⟩ | h⟩
    · exact NoRelWrite.not_relFulfilsLive (ret x.2.1) _ (hn.2 _) h
    · exact hn.1 hk
    · exact NoRelWrite.not_relFulfilsLive (ret x.2.1) _ (hn.2 _) h

/-- **The phase-2 tree shape**: a prefix of loads, then at most one access
(no release-kind RMW), and no release-kind write on any path. -/
def Phase2Shape (A : Arch) {σ : Type} (tree : EvTree σ) : Prop :=
  MultiAccessS True (fun _ _ => True) (fun k => ¬ effRelRmw A k) True tree ∧ NoRelWrite A tree

/-- Phase-2 trees satisfy the multi link's side conditions without a release
in flight. -/
theorem Phase2Shape.none {A : Arch} {σ : Type} {tree : EvTree σ} (h : Phase2Shape A tree) :
    MultiAccessS (LokS none) (SokS none) (RokS A none) (LokS none) tree :=
  MultiAccessS.mono (fun _ => rfl) (fun _ _ _ => .inl rfl) (fun _ hk => ⟨rfl, hk⟩) (fun _ => rfl) h.1

/-! ## The hypotheses and the start -/

/-- **The hypotheses of the phase-2 rule link** (`LinkHyps` with phase-2
trees admitted). -/
structure LinkHyps2 (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1Shape A tree ∨ Phase2Shape A tree
  link : ∀ (J : TreeJLive (EnvG I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- The phase-1 hypotheses are phase-2 hypotheses. -/
theorem LinkHyps.to2 {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop} (H : LinkHyps A tid pl Q) :
    LinkHyps2 A tid pl Q :=
  ⟨H.valid, fun st σ h tree hex => .inl (H.shape st σ h tree hex), H.link⟩

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **The start from the core, by shape**: `CoreAt.start`, plus that with a
release in flight every tree of the thread is `SingleAccessS` at it,
whatever its shape. -/
theorem CoreAt.start2 {cl : Prop} {c : Config I} {r : Res} {g : Ghost} {σ : State I} {t : Thread I}
    (h : CoreAt A tid pl cl c r g σ t) :
    ∃ pf, StartS tid c t g pf ∧
      (∀ tree, I.exec t.st = some tree → Phase1Shape A tree ∨ pf ≠ none →
        SingleAccessS (LokS pf) (SokS pf) (RokS A pf) (LokS pf) tree) ∧ (pf = none → r = σ.r) := by
  rcases h.rel.res with ⟨hr, hn⟩ | ⟨ts, l, v, h1, h2, h3, -, h6⟩
  · refine ⟨none, ⟨fun _ => hn, fun _ _ e => absurd e (by simp)⟩, fun _ _ hs => ?_, fun _ => hr⟩
    rcases hs with hs | hs
    · exact hs.none
    · exact absurd rfl hs
  · obtain ⟨htree, habove, -⟩ := h.infl ts l v h1 h2 h3
    refine ⟨some (l, v), ⟨fun e => absurd e (by simp), fun l' v' e => ?_⟩, fun tree hex _ => htree tree hex,
      fun e => absurd e (by simp)⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨ts, h1, h2, h3, habove⟩

/-- **From the phase-1 post relation to `WpPostR`** (the body of
`InvG.wp`): `PostRel.finish` re-establishes `EnvRel` with the new clean
flag, and no own promise is pending afterwards. -/
theorem InvG.wpPost {cl : Prop} {c : Config I} {r : Res} {g : Ghost} {σ : State I} {t : Thread I}
    (rF : Nat → Res) (hC : CoreAt A tid pl cl c r g σ t) (ht : c.threads[tid]? = some t)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) {pf : Option (Loc × Val)} (hr : pf = none → r = σ.r)
    (st : I.State) (r' : Res) (g' : Ghost) (cx' : Ctx)
    (hP : PostOf (E := EnvG I A tid pl) Q
      (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t (I.deps t.st)) c t σ.r g cl pf r g σ' r' g' cx')
      st r' g' cx') :
    WpPostR (InvG A tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t st r' g' cx' := by
  obtain ⟨σ', hQ', hP, ⟨hg', hkeep, hnew, hacq, hown⟩, hlast, hpd, hcl⟩ := hP
  refine ⟨hg', hkeep, hnew, hacq, hown, fun t' ht' _ => ?_⟩
  obtain ⟨cxe, hcx, -⟩ := hP.ctx
  have hE := hP.finish (pl := pl) ht hcx.sim.bnd hcx.sim.ivb (hC.rel.bnd.regs.mono hlast) ht'
  have hcl' : (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) → σ'.cl := by
    cases pf with
    | none => exact fun ⟨h1, h2⟩ => hP.cl ⟨h1, rF, (hr rfl) ▸ h2⟩
    | some _ => exact fun ⟨h1, _⟩ => hcl (by simp) h1
  have hprom' : t'.prom = cx'.prom := (finishInstr_relKey ht').1
  refine ⟨σ', t', ⟨{ hE with cl := hcl' }, fun ts hts => ?_, fun ts _ _ hts hpd' _ => ?_⟩, ?_⟩
  · have := E.pend_le (hnew ts hts)
    show ts ≤ cx'.mem.last
    omega_t
  · exact absurd hpd' (hpd ts (hprom' ▸ hts))
  · rw [finishInstr_st ht']; exact hQ'

/-- **`wp`** for phase-2 code: the phase-1 link at phase-1 trees and under an
in-flight release, the multi link at phase-2 trees otherwise. -/
theorem InvG.wp2 (H : LinkHyps2 A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
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
    have h2 : Phase2Shape A tree := (H.shape _ _ hQ tree hex).resolve_left h1
    have hW := H.link (TreeJLive.eraseWPRDM (nodeSimM_envG (A := A) (pl := pl) (iv := instrViews t (I.deps t.st))
      (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS) Q) t.st σ tree hQ hex (fun _ _ h => h)
    exact EvTree.EraseWPRD.mono (InvG.wpPost rF hC ht E hr) tree _ _ _
      (treeJ_envG_eraseWPRDM_start hC.rel (I.deps t.st) hS E hm hW h2.none)

/-- **`InvG.prepay_of_firstStore` for phase-2 code**, with the in-flight
tree's phase-1 shape as a hypothesis (`hsh`) instead of `LinkHyps.shape`: an
instance of the generic `InvG.prepay_of_firstStoreG` (`RuleLink.lean`;
formerly a copy of its proof). -/
theorem InvG.prepay_of_firstStore2 (H : LinkHyps2 A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res}
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

/-- **`prepay`** for phase-2 code: phase-2 trees fulfil no promise with a
live release; phase-1 trees as in `InvG.prepay`. -/
theorem InvG.prepay2 (H : LinkHyps2 A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
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
  have hsh : Phase1Shape A tree ∨ Phase2Shape A tree := by
    obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
    obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
    exact H.shape _ _ (hst ▸ hQ₀) tree hex
  rcases hsh with hsh | hsh
  · exact InvG.prepay_of_firstStore2 H rF t₁ w h he hg ht E hm hnp tree hex hsh
      (relFulfilsLive_firstStore (List.mem_append_right _ (List.mem_singleton_self _)) (Memory.get?_append_last _ _)
        tree _ rfl rfl hsh hrfl)
  · exact absurd hrfl (NoRelWrite.not_relFulfilsLive tree _ hsh.2)

end Rule

/-- **The phase-2 rule link**: a `ThreadRuleRX` from a thread-local
invariant `Q` of `EnvG` whose code may have load-prefix trees
(`LinkHyps2`), with the existing invariant `InvG`. -/
def ThreadRuleRX.ofEnvG2 {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps2 A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid where
  Inv := InvG A tid pl Q
  done h he hg hcl hd := InvG.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvG.wp2 H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvG.prepay2 H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafe` from the phase-2 rule link** (`NPSafe.of_ruleRX`). -/
theorem npSafe_of_envG2 {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps2 A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvG A tid pl Q cl c r g) :
    NPSafe (model I) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofEnvG2 H hB) n m cl c r g h

end Kraken.Promising.SLR.EnvG
