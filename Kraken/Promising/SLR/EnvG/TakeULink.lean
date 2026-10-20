/-
**Part 3: the tree link with the cumulative
take.** ISA-neutral. Adapted from the `EnvGT` instance of
`EnvG/TakeLink.lean` (unchanged); the abstract part (`NodeSimT`,
`TreeJLive.eraseWPRDST`, `treeJ_eraseWPRDST`) is reused as is, since it is
generic in the environment.

- `NodeRel.loadTUG` / `NodeRel.loadTU`: the load transport with the
  cumulative take (`NodeRel.loadTG` with `takeUpTo_spec`: every round's
  timestamp is at or below the message read, hence below the floor after
  the load, `take_floor_acqLoad`).
- `nodeSimTU_envGTU`: the per-node transport of `EnvGTU`;
  `treeJ_envGTU_eraseWPRDS(_start)`: link theorem 1 with cumulatively taking
  loads, the `EvTree.EraseWPRDS` target of `ThreadRuleRXGS.wp`.

Phase-1 limits as `EnvG/TakeLink.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeUEnv
import Kraken.Promising.SLR.EnvG.TakeLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- The env's load keeps its coherence views of the other locations. -/
theorem loadOutTU_getCoh_ne {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc}
    {v : Val} (h : LoadOutTU A tid σ σ' k xcl l v) {l' : Loc} (hne : l' ≠ l) : σ'.vs.getCoh l' = σ.vs.getCoh l' := by
  obtain ⟨-, -, -, -, tr, cx', hx, hvs, -⟩ := h
  rw [hvs, readSuccs_getCoh_ne hx hne]; rfl

/-! ## The load transport with the cumulative take -/

section Transport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}

/-- **Load transport with the cumulative take, exposing the ghost**
(`NodeRel.loadTG` for `LoadOutTU`). -/
theorem NodeRel.loadTUG (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : LoadKind} {xcl : Bool} {l : Loc} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l) (B : Time) :
    ∃ σ' r' g', LoadOutTU A tid σ σ' k xcl l x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' x.2.2 ∧
      RStepS B r g r' g' x.2.2 ∧ PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' x.2.2 ∧ WpPath c tid t r g r' g' x.2.2 ∧
      (g' = g ∨ (Erase (setRes rF tid σ.r) g (fun _ => True) c ∧ g' = (takeUpTo l x.1 σ.r g).g)) := by
  obtain ⟨tr, v, cx₁⟩ := x
  obtain ⟨cxe₁, hx', hc⟩ := h.ctx.read hx
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  simp only at hm1 hp1 ⊢
  have hm : cx₁.mem = c.mem := hm1.trans h.mem
  have hp : cx₁.prom = t.prom := hp1.trans h.prom
  have hr : r = σ.r := by
    rcases h.res with h' | ⟨ts, -, -, h1, h2, -⟩
    · exact h'.1
    · exact absurd h2 (hnp0 ts h1)
  obtain ⟨a, ha⟩ := TakeEffU.exists A k σ.vs l tr σ.r g
  have E0 : Erase (setRes rF tid σ.r) g (fun _ => True) c := hr ▸ h.erase
  have hspec : Erase (setRes rF tid a.r) a.g (fun _ => True) c ∧ RStepS B σ.r g a.r a.g cx₁ ∧
      (∀ x, mayWrite a.r a.g x → mayWrite σ.r g x) ∧ g.Le a.g ∧ a.g.pend = g.pend ∧
      (a.g = g ∨ (Erase (setRes rF tid σ.r) g (fun _ => True) c ∧ a.g = (takeUpTo l tr σ.r g).g)) := by
    by_cases hcnd : TakeCond A k σ.vs l tr
    · rw [ha.1 hcnd]
      have hfl : tr ≤ cx₁.views.wfloor :=
        Nat.le_trans (take_floor_acqLoad hx' hcnd.1 fun f hf ht => hcnd.2 ⟨f, hf, ht⟩) hc.wfloor
      obtain ⟨h1, h2, h3, h4, h5⟩ := takeUpTo_spec (B := B) (lt_size_of_get? h.ht) trivial hfl E0
      exact ⟨h1, h2, h3, h4, h5, .inr ⟨E0, rfl⟩⟩
    · rw [ha.2 hcnd]
      exact ⟨E0, RStepS.refl _ _ _ _, fun _ h => h, Ghost.Le.refl g, rfl, .inl rfl⟩
  obtain ⟨E', hR, hmw, hle, hpend, hgx⟩ := hspec
  refine ⟨{ σ with
      snap := c
      vs := cxe₁.views
      r := a.r
      g := a.g
      cl := (σ.cl ∧ ClAt tid σ.r g c)
      seen := (seenAfter A k σ g l tr).map (renameSeen l a.ren)
      fencedR := false }, a.r, a.g,
    ⟨g, h.anchorOk, ⟨rF, E0⟩, rfl, tr, cxe₁, hx', rfl, a, ha, rfl, rfl, rfl, rfl, rfl⟩, ?_, hr ▸ hR, ?_, ?_, hgx⟩
  · unfold ErAt; rw [withThread_ctx h.ht hm hp]; exact E'
  · refine ⟨?_, Ghost.Le.refl _, ⟨cxe₁, hc, rfl⟩, .inl ⟨rfl, fun ts hts hpd => hnp0 ts (hp ▸ hts) (hpend ▸ hpd)⟩,
      ?_, h.fenced.read hx⟩
    · rw [withThread_ctx h.ht hm hp]; exact SnapLe.refl tid c
    · rintro ⟨h0, hcl⟩
      refine ⟨h.cl h0, ?_⟩
      rw [h.rv, h.g0]; exact hcl
  · exact ⟨hle, fun ts hts _ => hpend ▸ hts, fun ts hts => hpend ▸ hts, fun x hx => hr ▸ hmw x hx,
      fun _ hw => (not_writtenCx_start hm hp hw).elim⟩

/-- **Load transport with the cumulative take** (no release in flight). -/
theorem NodeRel.loadTU (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : LoadKind} {xcl : Bool} {l : Loc} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l) (B : Time) :
    ∃ σ' r' g', LoadOutTU A tid σ σ' k xcl l x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' x.2.2 ∧
      RStepS B r g r' g' x.2.2 ∧ PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' x.2.2 ∧ WpPath c tid t r g r' g' x.2.2 :=
  let ⟨σ', r', g', h1, h2, h3, h4, h5, _⟩ := h.loadTUG hnp0 hx B
  ⟨σ', r', g', h1, h2, h3, h4, h5⟩

end Transport

/-! ## The instance for `EnvGTU` and link theorem 1 -/

section LinkTU

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The per-node transport of `EnvGTU`** (cumulatively taking loads). -/
theorem nodeSimTU_envGTU {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf) :
    NodeSimT A tid iv rF (fun _ => True) c t gS (EnvGTU I A tid pl) (LokS pf) (SokS pf) (RokS A pf) (LokS pf)
      (fun σ r g cx => PreS tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) := by
  have hS := nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst
  refine ⟨hS.pre_post, hS.fence_pre, hS.fence_post, ?_, hS.store, hS.rmw⟩
  rintro k xcl addr n σ r g cx hpf ⟨h, rfl, rfl⟩ - x hx -
  obtain ⟨σ', r', g', ho, E', hR, hp, hw⟩ := h.loadTU (hst.none hpf) hx c.mem.last
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  have hm : x.2.2.mem = c.mem := hm1.trans h.mem
  have hpr : x.2.2.prom = t.prom := hp1.trans h.prom
  refine ⟨σ', r', g', ho, E', hR.toG (Nat.le_refl _), hp, hw, by rw [hm]; exact Nat.le_refl _,
    fun ts hts hpd => hst.none hpf ts (hpr ▸ hts) (hw.2.2.1 ts hpd), fun hne => absurd hpf hne⟩

/-- **Link theorem 1 with cumulatively taking loads.** -/
theorem treeJ_envGTU_eraseWPRDS {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDST (nodeSimTU_envGTU (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀)
      (g₀ := g₀) (cl₀ := cl₀) (rS := rS) hst) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (ha : SingleAccessS (LokS pf) (SokS pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid iv rF (fun _ => True) c t gS
      (PostOf (E := EnvGTU I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDST _ hW ⟨h, rfl, rfl⟩ ha

/-- **Link theorem 1 with cumulatively taking loads at an instruction's
start.** -/
theorem treeJ_envGTU_eraseWPRDS_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDST (nodeSimTU_envGTU (A := A) (pl := pl) (iv := instrViews t d) (rF := rF)
      (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hst) Q).W tree σ)
    (ha : SingleAccessS (LokS pf) (SokS pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid (instrViews t d) rF (fun _ => True) c t g
      (PostOf (E := EnvGTU I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envGTU_eraseWPRDS hst hW (hrel.toNodeRel rF d E hm) ha

end LinkTU

#print axioms NodeRel.loadTU
#print axioms treeJ_envGTU_eraseWPRDS_start

end Kraken.Promising.SLR.EnvG
