/-
**Part 4: the link with taking loads**. ISA-neutral. Adapted from
`EnvG/TreeLinkS.lean` and `EnvG/LinkS.lean`; nothing else changes.

- `NodeRel.loadT`: the **load transport with the take**. The env reads the
  same timestamp and value (`CtxLe.read`); if the load takes (`TakeCond`),
  the actual resource and ghost become the iterated take at the anchor
  `(c, g)` (`takeAll_spec`: erasure by `Erase.take`, K1/K2 by
  `Erase.rStepS_take`, the floor bound `tr ≤ wfloor` from the env's read by
  `take_floor_acqLoad` and `CtxLe.wfloor`), else they are kept.
  `Inflight` commutes trivially: loads are only reached with no release in
  flight (`LokS pf : pf = none`), where `Inflight` is `r = σ.r`.
- `NodeSimT`: `NodeSimS` (`EnvG/TreeLinkS.lean`) whose load field may change
  `(r, g)` with `RStepG g₀` (K2 scoped to the instruction's start ghost
  `g₀`, `SLR/TakeRuleThread.lean`); `TreeJLive.eraseWPRDST`,
  `treeJ_eraseWPRDST`: link theorem 1 (abstract) for
  `EvTree.EraseWPRDS`.
- `nodeSimT_envGT`: the instance for `EnvGT` (store, RMW and fence fields
  are `nodeSimS_envG`'s, `EnvGT` and `EnvG` agreeing on them
  definitionally); `treeJ_envGT_eraseWPRDS(_start)`: **link theorem 1 with
  taking loads**, the `EvTree.EraseWPRDS` target of `ThreadRuleRXGS.wp`.

**Why no `NodeRelT`.** The original plan anticipated relaxing `NodeRel`'s
`g0 : g = g₀` and `rv : σ.r = rv₀`. On single-access trees they are not in
the way: the load starts from `NodeRel` (still at the instruction's start,
`PreS`), and lands in `PostRel`, which has neither field. `NodeRel`,
`PostRel`, `PreS` and `PostS` are reused unchanged.

Phase-1 limits: single-access trees; releases are stores (RMWs not of
release kind); only non-forwarded acquire loads take; no fence-node take;
the take and the use of what is taken are in different instructions.
-/
import Kraken.Promising.SLR.EnvG.TakeEnv
import Kraken.Promising.SLR.EnvG.LinkS

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-! ## Coherence views of other locations (from `EnvG/TicketLink.lean`) -/

/-- The env's load keeps its coherence views of the other locations. -/
theorem loadOutT_getCoh_ne {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc} {v : Val}
    (h : LoadOutT A tid σ σ' k xcl l v) {l' : Loc} (hne : l' ≠ l) : σ'.vs.getCoh l' = σ.vs.getCoh l' := by
  obtain ⟨-, -, -, -, tr, cx', hx, hvs, -⟩ := h
  rw [hvs, readSuccs_getCoh_ne hx hne]; rfl

/-! ## The load transport with the take -/

section Transport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}

/-- **Load transport with the take, exposing the ghost**: the
conclusion of `NodeRel.loadT`, and the ghost after the load is the start
ghost `g` or the iterated take `(takeAll l x.1 σ.r g).g` from the erased
start. Extensions of the erasure kept by the take (e.g. the ticket
dispenser's `TicketInv`, `NodeRel.loadTD`) are transported from it. -/
theorem NodeRel.loadTG (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : LoadKind} {xcl : Bool} {l : Loc} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l) (B : Time) :
    ∃ σ' r' g', LoadOutT A tid σ σ' k xcl l x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' x.2.2 ∧
      RStepS B r g r' g' x.2.2 ∧ PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' x.2.2 ∧ WpPath c tid t r g r' g' x.2.2 ∧
      (g' = g ∨ (Erase (setRes rF tid σ.r) g (fun _ => True) c ∧ g' = (takeAll l x.1 σ.r g).g)) := by
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
  obtain ⟨a, ha⟩ := TakeEff.exists A k σ.vs l tr σ.r g
  have E0 : Erase (setRes rF tid σ.r) g (fun _ => True) c := hr ▸ h.erase
  have hspec : Erase (setRes rF tid a.r) a.g (fun _ => True) c ∧ RStepS B σ.r g a.r a.g cx₁ ∧
      (∀ x, mayWrite a.r a.g x → mayWrite σ.r g x) ∧ g.Le a.g ∧ a.g.pend = g.pend ∧
      (a.g = g ∨ (Erase (setRes rF tid σ.r) g (fun _ => True) c ∧ a.g = (takeAll l tr σ.r g).g)) := by
    by_cases hcnd : TakeCond A k σ.vs l tr
    · rw [ha.1 hcnd]
      have hfl : tr ≤ cx₁.views.wfloor :=
        Nat.le_trans (take_floor_acqLoad hx' hcnd.1 fun f hf ht => hcnd.2 ⟨f, hf, ht⟩) hc.wfloor
      obtain ⟨h1, h2, h3, h4, h5⟩ := takeAll_spec (B := B) (lt_size_of_get? h.ht) trivial hfl E0
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

/-- **Load transport with the take** (no release in flight). -/
theorem NodeRel.loadT (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : LoadKind} {xcl : Bool} {l : Loc} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l) (B : Time) :
    ∃ σ' r' g', LoadOutT A tid σ σ' k xcl l x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' x.2.2 ∧
      RStepS B r g r' g' x.2.2 ∧ PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' x.2.2 ∧ WpPath c tid t r g r' g' x.2.2 :=
  let ⟨σ', r', g', h1, h2, h3, h4, h5, _⟩ := h.loadTG hnp0 hx B
  ⟨σ', r', g', h1, h2, h3, h4, h5⟩

end Transport

/-! ## The per-node transport with taking loads (abstract) -/

/-- **Per-node transport with side conditions and taking loads**:
`NodeSimS` whose load field may change `(r, g)`, with erasure and
`RStepG g₀` (`g₀`: the instruction's start ghost). -/
structure NodeSimT (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res) (T : Nat → Prop) (c : Config I)
    (t : Thread I) (g₀ : Ghost) (E : SharedEnv) (Lok : Prop) (Sok : Loc → Val → Prop) (Rok : RmwKind → Prop)
    (D : Prop) (Pre Post : E.State → Res → Ghost → Ctx → Prop) : Prop where
  pre_post : ∀ {s r g cx}, D → Pre s r g cx → Post s r g cx
  fence_pre : ∀ {k : FenceKind} {s r g cx}, Pre s r g cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Pre s' r g (fenceStep cx k)
  fence_post : ∀ {k : FenceKind} {s r g cx}, Post s r g cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Post s' r g (fenceStep cx k)
  load : ∀ {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {s r g cx}, Lok →
    Pre s r g cx → E.ok (.load k xcl addr n) s →
    ∀ x ∈ readSuccs A iv cx k xcl ⟨addr, n⟩, ErAt rF T c t tid r g x.2.2 →
      ∃ s' r' g', E.step (.load k xcl addr n) s x.2.1 s' ∧ ErAt rF T c t tid r' g' x.2.2 ∧
        RStepG g₀ c.mem.last r g r' g' x.2.2 ∧ Post s' r' g' x.2.2
  store : ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {s r g cx}, Sok ⟨addr, n⟩ v →
    Pre s r g cx → E.ok (.store k xcl addr n v) s →
    (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl ⟨addr, n⟩ v
        (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
      ErAt rF T c t tid r g cx → cx.Inv tid → c.mem.last ≤ cx.mem.last →
      cx'.Overtaken ∨ ∃ r' g' s', E.step (.store k xcl addr n v) s true s' ∧ ErAt rF T c t tid r' g' cx' ∧
        RStep c.mem.last r g r' g' cx' ∧ Post s' r' g' cx') ∧
    (xcl = true → ∃ s', E.step (.store k xcl addr n v) s false s' ∧ Post s' r g (xclFailCtx cx ⟨addr, n⟩))
  rmw : ∀ {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {s r g cx}, Rok k →
    Pre s r g cx → E.ok (.rmw k addr n op) s →
    ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false ⟨addr, n⟩ false,
      (op x.2.1 = none → ∃ s', E.step (.rmw k addr n op) s x.2.1 s' ∧ Post s' r g (fenceOptCtx A x.2.2)) ∧
      ∀ new, op x.2.1 = some new →
        ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true ⟨addr, n⟩ new (some x.1)
            (x.2.2.loadViews.getLastD 0),
          ErAt rF T c t tid r g x.2.2 → cx.Inv tid → c.mem.last ≤ cx.mem.last →
          cx'.Overtaken ∨ ∃ r' g' s', E.step (.rmw k addr n op) s x.2.1 s' ∧ ErAt rF T c t tid r' g' cx' ∧
            RStep c.mem.last r g r' g' (rmwAfter A k false ⟨addr, n⟩ cx') ∧
            Post s' r' g' (rmwAfter A k false ⟨addr, n⟩ cx')

section Link

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {g₀ : Ghost} {E : SharedEnv} {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop}
  {D : Prop} {Pre Post : E.State → Res → Ghost → Ctx → Prop}

/-- **`EraseWPRDS` is a live tree judgment** of any environment with a
per-node transport with taking loads (`TreeJLive.eraseWPRDS` with
`EvTree.EraseWPRDS` at the start ghost `g₀`). -/
def TreeJLive.eraseWPRDST (hs : NodeSimT A tid iv rF T c t g₀ E Lok Sok Rok D Pre Post) {σ : Type}
    (Q : σ → E.State → Prop) : TreeJLive E σ where
  W tree s :=
    (∀ r g cx, Pre s r g cx → SingleAccessS Lok Sok Rok D tree →
      tree.EraseWPRDS A tid iv rF T c t g₀ (PostOf Q Post) r g cx) ∧
    (∀ r g cx, Post s r g cx → AccessFree tree → tree.EraseWPRDS A tid iv rF T c t g₀ (PostOf Q Post) r g cx)
  Post := Q
  done h := ⟨fun _ _ _ hp hd => ⟨_, h, hs.pre_post hd hp⟩, fun _ _ _ hp _ => ⟨_, h, hp⟩⟩
  fault := ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩
  choose h := ⟨fun r g cx hp ha i => (h i).1 r g cx hp (ha i), fun r g cx hp ha i => (h i).2 r g cx hp (ha i)⟩
  fence hok h := by
    refine ⟨fun r g cx hp ha => ?_, fun r g cx hp ha => ?_⟩
    · obtain ⟨s', hst, hp'⟩ := hs.fence_pre hp hok
      exact (h s' hst).1 r g _ hp' ha
    · obtain ⟨s', hst, hp'⟩ := hs.fence_post hp hok
      exact (h s' hst).2 r g _ hp' ha
  load hok h := by
    refine ⟨fun r g cx hp ha x hx Ex => ?_, fun _ _ _ _ ha => ha.elim⟩
    obtain ⟨s', r', g', hst, E', hR, hp'⟩ := hs.load ha.1 hp hok x hx Ex
    exact ⟨r', g', E', hR, (h _ s' hst).2 r' g' _ hp' (ha.2 _)⟩
  store hok h := by
    refine ⟨fun r g cx hp ha => ⟨fun cx' hc E hi hm => ?_, fun hx => ?_⟩, fun _ _ _ _ ha => ha.elim⟩
    · rcases (hs.store ha.1 hp hok).1 cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h true s' hst).2 r' g' cx' hp' (ha.2 true)⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.store ha.1 hp hok).2 hx
      exact (h false s' hst).2 r g _ hp' (ha.2 false)
  rmw := by
    intro k addr n op ret s hok h
    refine ⟨fun r g cx hp ha x hx => ⟨fun hop => ?_, fun new hop cx' hc E hi hm => ?_⟩, fun _ _ _ _ ha => ha.elim⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.rmw ha.1 hp hok x hx).1 hop
      exact (h _ s' hst).2 r g _ hp' (ha.2 _)
    · rcases (hs.rmw ha.1 hp hok x hx).2 new hop cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h _ s' hst).2 r' g' _ hp' (ha.2 _)⟩

/-- **Link theorem 1, abstract form, with taking loads.** -/
theorem treeJ_eraseWPRDST (hs : NodeSimT A tid iv rF T c t g₀ E Lok Sok Rok D Pre Post) {σ : Type}
    {Q : σ → E.State → Prop} {tree : EvTree σ} {s : E.State} (hW : (TreeJLive.eraseWPRDST hs Q).W tree s)
    {r : Res} {g : Ghost} {cx : Ctx} (hp : Pre s r g cx) (ha : SingleAccessS Lok Sok Rok D tree) :
    tree.EraseWPRDS A tid iv rF T c t g₀ (PostOf Q Post) r g cx :=
  hW.1 r g cx hp ha

end Link

/-! ## The instance for `EnvGT` and link theorem 1 with taking loads -/

section LinkT

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The per-node transport of `EnvGT`** (taking loads), at the
instruction's start `(rS, gS)` (the WP's start ghost is `gS`). -/
theorem nodeSimT_envGT {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf) :
    NodeSimT A tid iv rF (fun _ => True) c t gS (EnvGT I A tid pl) (LokS pf) (SokS pf) (RokS A pf) (LokS pf)
      (fun σ r g cx => PreS tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) := by
  have hS := nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst
  refine ⟨hS.pre_post, hS.fence_pre, hS.fence_post, ?_, hS.store, hS.rmw⟩
  rintro k xcl addr n σ r g cx hpf ⟨h, rfl, rfl⟩ - x hx -
  obtain ⟨σ', r', g', ho, E', hR, hp, hw⟩ := h.loadT (hst.none hpf) hx c.mem.last
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  have hm : x.2.2.mem = c.mem := hm1.trans h.mem
  have hpr : x.2.2.prom = t.prom := hp1.trans h.prom
  refine ⟨σ', r', g', ho, E', hR.toG (Nat.le_refl _), hp, hw, by rw [hm]; exact Nat.le_refl _,
    fun ts hts hpd => hst.none hpf ts (hpr ▸ hts) (hw.2.2.1 ts hpd), fun hne => absurd hpf hne⟩

/-- **Link theorem 1 with taking loads**: as `treeJ_envG_eraseWPRDS`, for
`EnvGT`, with target `EvTree.EraseWPRDS` at the start ghost. -/
theorem treeJ_envGT_eraseWPRDS {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDST (nodeSimT_envGT (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀)
      (g₀ := g₀) (cl₀ := cl₀) (rS := rS) hst) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (ha : SingleAccessS (LokS pf) (SokS pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid iv rF (fun _ => True) c t gS
      (PostOf (E := EnvGT I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDST _ hW ⟨h, rfl, rfl⟩ ha

/-- **Link theorem 1 with taking loads at an instruction's start**: from
`EnvRel` and the hypotheses of `ThreadRuleRXGS.wp`, at `ctx₀`. -/
theorem treeJ_envGT_eraseWPRDS_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDST (nodeSimT_envGT (A := A) (pl := pl) (iv := instrViews t d) (rF := rF) (rv₀ := σ.r)
      (g₀ := g) (cl₀ := cl) (rS := r) hst) Q).W tree σ)
    (ha : SingleAccessS (LokS pf) (SokS pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid (instrViews t d) rF (fun _ => True) c t g
      (PostOf (E := EnvGT I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envGT_eraseWPRDS hst hW (hrel.toNodeRel rF d E hm) ha

end LinkT

#print axioms NodeRel.loadT
#print axioms treeJ_envGT_eraseWPRDS_start

end Kraken.Promising.SLR.EnvG
