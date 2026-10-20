/-
Whole-thread environment (`EnvG`), phase 2 (the multi-access link prototype): **the
concrete link for trees with a load prefix**. ISA-neutral.

Phase 1 relates the actual context of an instruction to `EnvG`'s by
`NodeRel` *before the instruction's single access* (`LinkS.lean`). For a
tree with a load prefix (`MultiAccessS`, `MultiTreeLink.lean`) the relation
before each access is

  `PreM σ r g cx := PreS … (cl₀ ∧ ClAt tid rv₀ g₀ c) rS gS σ r g cx.reset`
                    `∧ cx.stores = 0 ∧ cx.rmwWrote = false ∧ cx.Bnd`:

the phase-1 `PreS` at the actual context **with its instruction-local fields
reset** (`Ctx.reset`, `MultiReset.lean`; a load only appends to `loadViews`),
at the knowledge `cl₀ ∧ ClAt tid rv₀ g₀ c`: after a load the env's `cl` has
gained the clean erasure at the anchor, which is the instruction's start `c`
(a load writes nothing), and that is exactly the conjunct `ThreadRuleRX.wp`
adds to the new `cl`. Every access is answered by the phase-1 transport at the
reset context (`nodeSimS_envG`), whose outcome is carried back to the actual
context (`Ctx.Same.read`/`.write`, `PostS.same`).

**Scope** (stated in `nodeSimM_envG`'s side conditions): no release in
flight (`pf = none`; loads are not allowed under an in-flight release in
phase 1 either, `LokS`), RMWs not of release kind (`RokS`). Releases as the
final access of a load-prefix tree and in-flight releases after loads are
the open part.

- `PreM`, `PostS.same`, `NodeRel.toReset`, `PostRel.toNodeRelLoad`;
- `nodeSimM_envG`: the `NodeSimM` instance;
- `treeJ_envG_eraseWPRDM(_start)`: **link theorem 1** for trees with a load
  prefix, with the phase-1 post relation `PostS` at the instruction's `cl`.
-/
import Kraken.Promising.SLR.EnvG.LinkS
import Kraken.Promising.SLR.EnvG.MultiTreeLink
import Kraken.Promising.SLR.EnvG.MultiReset

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

section Rel

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

theorem _root_.Kraken.Promising.Ctx.Same.reset_eq {cx cy : Ctx} (h : cx.Same cy) : cx.reset = cy.reset := by
  unfold Ctx.reset; rw [h.views, h.prom, h.mem]

/-- `NodeRel` moves to the reset of a `Same` context (the relation reads the
actual context's views, promises and memory only, once its local fields are
the environment's defaults). -/
theorem NodeRel.toReset {σ : State I} {r : Res} {g : Ghost} {cx cy : Ctx}
    (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cy) (hs : cx.Same cy) :
    NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx.reset where
  ht := h.ht
  mach := h.mach
  mem := hs.mem.trans h.mem
  prom := hs.prom.trans h.prom
  erase := h.erase
  g0 := h.g0
  rv := h.rv
  snap := h.snap
  ghost := h.ghost
  ctx := by
    rw [hs.reset_eq]
    exact h.ctx.reset.congrT rfl rfl rfl rfl rfl rfl rfl
  res := h.res
  cl := h.cl
  fenced := by
    show FencedInv _ _ cx.views
    rw [hs.views]; exact h.fenced

/-- **After a load, the node relation again** (at the reset of the load's
context): the load kept the resource, the ghost, the memory and the promises;
the env's new `cl` is implied by the knowledge `cl` when `cl` includes the
clean erasure at the start. -/
theorem PostRel.toNodeRelLoad {σ σ' : State I} {r : Res} {g : Ghost} {cx cy : Ctx}
    (hp : PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r g cy) (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx)
    (hm : cy.mem = c.mem) (hpr : cy.prom = t.prom) (hr : σ'.r = σ.r) (hcl : cl₀ → ClAt tid rv₀ g₀ c) :
    NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ' r g cy.reset where
  ht := h.ht
  mach := h.mach
  mem := hm
  prom := hpr
  erase := h.erase
  g0 := h.g0
  rv := hr.trans h.rv
  snap := by
    have := hp.snap; rw [withThread_ctx h.ht hm hpr] at this; exact this
  ghost := hp.ghost
  ctx := by
    obtain ⟨cxe, hc, hv⟩ := hp.ctx
    refine hc.reset.congrT hv.symm ?_ ?_ rfl rfl rfl rfl
    · show ownProm tid c = cxe.prom; rw [ownProm_eq h.ht, hc.prom, hpr]
    · show c.mem = cxe.mem; rw [hc.mem, hm]
  res := hp.res.congr hpr.symm hm.symm
  cl h0 := hp.cl ⟨h0, hcl h0⟩
  fenced := hp.fenced

/-- **`PostS` moves to a `Same` context** whose load views and success view
are bounded (the environment's `loadViews`/`succView` re-chosen,
`CtxLe.transfer`). -/
theorem PostS.same {pf : Option (Loc × Val)} {rS : Res} {gS : Ghost} {σ : State I} {r : Res} {g : Ghost}
    {cx cy : Ctx} (hp : PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cy) (hs : cx.Same cy)
    (hlv : ∀ ν ∈ cx.loadViews, ν ≤ cx.mem.last) (hsv : cx.succView ≤ cx.mem.last) :
    PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx := by
  obtain ⟨⟨h1, h2, ⟨cxe, hc, hv⟩, h4, h5, h6⟩, hw, hl, hpd, hcl⟩ := hp
  have hb : cx.Bnd := ⟨by rw [hs.views, hs.mem]; exact hc.sim.bnd.views, hlv, hsv⟩
  refine ⟨⟨?_, h2, ⟨_, hc.transfer hs hb, hv⟩, ?_, h5, ?_⟩, hw.congr hs.mem hs.prom, ?_, ?_, hcl⟩
  · rw [hs.prom, hs.mem]; exact h1
  · exact h4.congr hs.prom hs.mem
  · rw [hs.views]; exact h6
  · rw [hs.mem]; exact hl
  · rw [hs.prom]; exact hpd

/-- `PostS` at stronger start knowledge, without a release in flight, is
`PostS` at the start knowledge `cl₀` when the extra conjunct is the clean
erasure at the start that `PostRel.cl` assumes anyway. -/
theorem PostS.of_clM {rS : Res} {gS : Ghost} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}
    (hp : PostS tid pl iv c t rv₀ g₀ (cl₀ ∧ ClAt tid rv₀ g₀ c) none rS gS σ r g cx) :
    PostS tid pl iv c t rv₀ g₀ cl₀ none rS gS σ r g cx := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hw, hl, hpd, -⟩ := hp
  exact ⟨⟨h1, h2, h3, h4, fun ⟨h0, hc⟩ => h5 ⟨⟨h0, hc⟩, hc⟩, h6⟩, hw, hl, hpd, fun h => absurd rfl h⟩

end Rel

/-! ## The relation before each access, and the transport -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **Before each access of a tree with a load prefix**: the phase-1 `PreS`
at the reset context, at the knowledge `cl₀ ∧ ClAt tid rv₀ g₀ c`; no local
write yet; the actual context bounded. -/
def PreM (tid : Nat) (pl : Plan) (iv : InstrViews) (rF : Nat → Res) (c : Config I) (t : Thread I) (rv₀ : Res)
    (g₀ : Ghost) (cl₀ : Prop) (rS : Res) (gS : Ghost) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx) : Prop :=
  PreS tid pl iv rF c t rv₀ g₀ (cl₀ ∧ ClAt tid rv₀ g₀ c) rS gS σ r g cx.reset ∧ cx.stores = 0 ∧
    cx.rmwWrote = false ∧ cx.Bnd

/-- **The per-node transport of `EnvG` for trees with a load prefix**
(no release in flight). -/
theorem nodeSimM_envG {rS : Res} {gS : Ghost} (hst : StartS tid c t gS none) :
    NodeSimM A tid iv rF (fun _ => True) c t (EnvG I A tid pl) (LokS none) (SokS none) (RokS A none) (LokS none)
      (fun σ r g cx => PreM tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostS tid pl iv c t rv₀ g₀ (cl₀ ∧ ClAt tid rv₀ g₀ c) none rS gS σ r g cx) := by
  have H := nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀)
    (cl₀ := cl₀ ∧ ClAt tid rv₀ g₀ c) (rS := rS) hst
  exact {
  pre_post := by
    rintro σ r g cx hd ⟨hpre, hs, hw, hb⟩
    exact (H.pre_post hd hpre).same (Ctx.Same.reset hs hw) hb.loadViews hb.succView
  fence_pre := by
    rintro k σ r g cx ⟨hpre, hs, hw, hb⟩ hok
    obtain ⟨σ', hst', hp'⟩ := H.fence_pre hpre hok
    have hS : (fenceStep cx k).Same (fenceStep cx.reset k) := (Ctx.Same.reset hs hw).fence k
    refine ⟨σ', hst', ⟨⟨hp'.1.toReset hS, hp'.2⟩, ?_, ?_, fenceStep_bnd hb k⟩⟩
    · rw [hS.stores]; cases k <;> rfl
    · rw [hS.rmwWrote]; cases k <;> rfl
  fence_post := H.fence_post
  load := by
    rintro k xcl addr n σ r g cx hpf ⟨⟨h, rfl, rfl⟩, hs, hw, hb⟩ hok x hx
    obtain ⟨y, hy, -, hv, hS, -⟩ := (Ctx.Same.reset hs hw).read hx
    obtain ⟨σ', ho, hp⟩ := h.load hy
    obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hy
    have hm : y.2.2.mem = c.mem := hm1.trans h.mem
    have hpr : y.2.2.prom = t.prom := hp1.trans h.prom
    have hN := hp.toNodeRelLoad h hm hpr ho.2.1 And.right
    rw [← hS.reset_eq] at hN
    obtain ⟨tr', v', rfl, -⟩ := (mem_readSuccs A).mp hx
    refine ⟨σ', hv ▸ ho, ⟨hN, rfl, rfl⟩, ?_, ?_, (readSuccs_bnd A iv hb h.ctx.sim.ivb hx).1⟩
    · show cx.stores = 0; exact hs
    · show cx.rmwWrote = false; exact hw
  store := by
    rintro k xcl addr n v σ r g cx hS ⟨hpre, hs, hw, hb⟩ hok
    obtain rfl : xcl = false := hok.1
    refine ⟨fun cx' hc E hi hm => ?_, fun hx => absurd hx Bool.false_ne_true⟩
    have hR := Ctx.Same.reset hs hw
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    rw [hs] at hc
    obtain ⟨cy', hcy, hS'⟩ := hR.write hc
    have hb' := writeSuccs_bnd A tid _ hb (hpre.1.ctx.sim.ivb.forStore 0) (Nat.zero_le _) hc
    rcases (H.store hS hpre hok).1 cy' (by simpa using hcy) (hR.symm.erAt E) (hR.inv hi) hm with
      ho | ⟨r', g', σ', hst', E', hRS, hp'⟩
    · exact .inl (hS'.overtaken ho)
    · exact .inr ⟨r', g', σ', hst', hS'.erAt E', hS'.rStep hRS, hp'.same hS' hb'.1.loadViews hb'.1.succView⟩
  rmw := by
    rintro k addr n op σ r g cx hRk ⟨hpre, hs, hw, hb⟩ hok x hx
    have hR := Ctx.Same.reset hs hw
    obtain ⟨y, hy, hy1, hv, hS, hlast⟩ := (hR.fenceOpt A).read hx
    have H' := H.rmw hRk hpre hok y hy
    have hivb := hpre.1.ctx.sim.ivb
    obtain ⟨hbo, hmo⟩ := fenceOpt_bnd hb A.rmwFence .sy
    have hb1 := readSuccs_bnd A iv hbo (by rw [hmo]; exact hivb) hx
    refine ⟨fun hop => ?_, fun new hop cx' hc E hi hm => ?_⟩
    · obtain ⟨σ', hst', hp'⟩ := H'.1 (hv ▸ hop)
      have hS2 := hS.fenceOpt A
      obtain ⟨hb2, -⟩ := fenceOpt_bnd hb1.1 A.rmwFence .sy
      exact ⟨σ', hv ▸ hst', hp'.same hS2 hb2.loadViews hb2.succView⟩
    · rw [hlast] at hc
      obtain ⟨cy', hcy, hS'⟩ := hS.write hc
      have hb2 := writeSuccs_bnd A tid iv hb1.1 (by rw [hb1.2.2, hmo]; exact hivb)
        (getLastD_le' hb1.1.loadViews) (hlast ▸ hc)
      rcases H'.2 new (hv ▸ hop) cy' (hy1 ▸ hcy) (hS.symm.erAt E) (hR.inv hi) hm with ho | ⟨r', g', σ', hst', E', hRS, hp'⟩
      · exact .inl (hS'.overtaken ho)
      · have hS3 := hS'.rmwAfter A k false ⟨addr, n⟩
        obtain ⟨hb3, -⟩ := fenceOpt_bnd (rmwPost_bnd A hb2.1 k false ⟨addr, n⟩).1 A.rmwFence .sy
        exact .inr ⟨r', g', σ', hv ▸ hst', hS'.erAt E', hS3.rStep hRS, hp'.same hS3 hb3.loadViews hb3.succView⟩ }

/-- **Link theorem 1 for `EnvG`, trees with a load prefix**: from the
phase-1 node relation at the instruction's start (no local field written
yet), the erasure WP with the phase-1 post relation at the start knowledge
`cl₀`. -/
theorem treeJ_envG_eraseWPRDM {rS : Res} {gS : Ghost} (hst : StartS tid c t gS none)
    {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDM (nodeSimM_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀)
      (cl₀ := cl₀) (rS := rS) hst) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx) (hs : cx.stores = 0) (hw : cx.rmwWrote = false)
    (ha : MultiAccessS (LokS none) (SokS none) (RokS A none) (LokS none) tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ none rS gS σ' r' g' cx')) rS gS cx := by
  have hN : NodeRel tid pl iv rF c t rv₀ g₀ (cl₀ ∧ ClAt tid rv₀ g₀ c) σ rS gS cx.reset :=
    { h.toReset (Ctx.Same.refl cx) with cl := fun h0 => h.cl h0.1 }
  refine EvTree.EraseWPRD.mono (fun _ _ _ _ ⟨s, hq, hp⟩ => ⟨s, hq, hp.of_clM⟩) tree _ _ _
    (treeJ_eraseWPRDM _ hW ⟨⟨hN, rfl, rfl⟩, hs, hw, h.ctx.sim.bnd⟩ ha)

/-- **Link theorem 1 at an instruction's start, trees with a load prefix**:
from `EnvRel` and the hypotheses of `ThreadRuleRX.wp`, at `ctx₀`, without a
release in flight. -/
theorem treeJ_envG_eraseWPRDM_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) (hst : StartS tid c t g none)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDM (nodeSimM_envG (A := A) (pl := pl) (iv := instrViews t d) (rF := rF) (rv₀ := σ.r)
      (g₀ := g) (cl₀ := cl) (rS := r) hst) Q).W tree σ)
    (ha : MultiAccessS (LokS none) (SokS none) (RokS A none) (LokS none) tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g cl none r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envG_eraseWPRDM hst hW (hrel.toNodeRel rF d E hm) rfl rfl ha

end Link

end Kraken.Promising.SLR.EnvG
