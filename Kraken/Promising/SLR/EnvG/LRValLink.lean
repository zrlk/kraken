/-
Whole-thread environment: **the
concrete link of `EnvGLRV` for load-prefix trees, with an in-flight release
after the loads**. ISA-neutral. Additive: `LRLink.lean`'s link with one
changed case.

**Why `ClAtV` is justifiable** (the obstacle `EnvGLR` avoids). `EnvG`'s load
conjunct `ClAt tid σ.r g c` fails with a release in flight because the
actual resource at the load is `Plan.after … σ.r`. `ClAtV` asks for clean
erasure at *some* resource related to `σ.r` by `Inflight`, which the node
relation records (`NodeRel.res`); the actual start resource `rS` is one. So
the load is justified whenever the node relation's knowledge parameter
`cl₀` implies `ClAt tid rS g₀ c` (`hK`). The instruction-level link runs the
tree at `cl₀ := cl ∧ Erase (setRes rF tid rS) g ⊥ c` (exactly the knowledge
`ThreadRuleRX.wp` hands to `WpPostR`), so `hK` is the second conjunct
(`treeJ_envGLRV_eraseWPRDM_start`). The other cases are `nodeSimS_envG`'s,
as in `nodeSimLR_envGLR`.

- `NodeRel.loadLRV`: the load transport;
- `nodeSimLRV_envGLRV`: the `NodeSimM` instance;
- `treeJ_envGLRV_eraseWPRDM`, `treeJ_envGLRV_eraseWPRDM_start`: link
  theorem 1 for `EnvGLRV`.

**Rule-level note (not done here).** A rule link `ThreadRuleRX.ofEnvGLRV`
is `LRRule.lean` with `EnvGLR` replaced, with two changes: `InvGLR.wp`'s
`hcl'` now follows from `PostS` at `cl₀ := cl ∧ Erase …` (both branches),
and `InvGLR.prepay`'s walk answers loads by `NodeRel.loadLRV` at `cl₀ :=
False` (so `hK` is vacuous). The walk's store state then has a *stronger*
`cl` than the start (the loads add `ClAtV`), so the in-flight relation's
`∃ P, (σ.cl → P) ∧ r = Plan.after … P σ.r` needs `P` independent of the
knowledge: whole plan entries (`Plan.Whole`, as `RmwOk` already asks of
release RMWs).
-/
import Kraken.Promising.SLR.EnvG.LRValEnv
import Kraken.Promising.SLR.EnvG.LRLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

section Transport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}

/-- **Load transport of `EnvGLRV`**: as `NodeRel.loadLR`, with `ClAtV` added
to the env's `cl`; the node relation's knowledge `cl₀` must give clean
erasure at the actual resource `r` (`hK`). -/
theorem NodeRel.loadLRV (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hK : cl₀ → ClAt tid r g c)
    {k : LoadKind} {xcl : Bool} {l : Loc} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l) :
    ∃ σ', LoadOutLRV A tid pl σ σ' k xcl l x.2.1 ∧ NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ' r g x.2.2.reset := by
  obtain ⟨tr, v, cx₁⟩ := x
  obtain ⟨cxe₁, hx', hc⟩ := h.ctx.read hx
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  simp only at hm1 hp1 ⊢
  refine ⟨{ σ with
      snap := c, g := g, vs := cxe₁.views
      cl := σ.cl ∧ ClAtV tid pl σ.cl σ.r g c
      seen := seenAfter A k σ g l tr, fencedR := false }, ⟨h.anchorOk, rfl, rfl, tr, cxe₁, hx', rfl, rfl, rfl, rfl⟩,
    ?_⟩
  exact {
    ht := h.ht
    mach := h.mach
    mem := hm1.trans h.mem
    prom := hp1.trans h.prom
    erase := h.erase
    g0 := h.g0
    rv := h.rv
    snap := SnapLe.refl tid c
    ghost := Ghost.Le.refl g
    ctx := by
      refine hc.reset.congrT rfl ?_ ?_ rfl rfl rfl rfl
      · show ownProm tid c = cxe₁.prom; rw [ownProm_eq h.ht, hc.prom, hp1, h.prom]
      · show c.mem = cxe₁.mem; rw [hc.mem, hm1, h.mem]
    res := h.res.mono_cl fun hc => hc.1
    cl := fun hc => ⟨h.cl hc, r, hK hc, h.res.congr (ownProm_eq h.ht) rfl⟩
    fenced := h.fenced.read hx }

end Transport

/-! ## The per-node transport and link theorem 1 -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The per-node transport of `EnvGLRV` for load-prefix trees**
(`nodeSimLR_envGLR` with the load case by `NodeRel.loadLRV`), given that the
knowledge parameter gives clean erasure at the start resource (`hK`). -/
theorem nodeSimLRV_envGLRV {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    (hK : cl₀ → ClAt tid rS g₀ c) :
    NodeSimM A tid iv rF (fun _ => True) c t (EnvGLRV I A tid pl) True (SokLR pf) (RokS A pf) (LokS pf)
      (fun σ r g cx => PreLR tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) := by
  have H := nodeSimLR_envGLR (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst
  exact {
  pre_post := H.pre_post
  fence_pre := H.fence_pre
  fence_post := H.fence_post
  load := by
    rintro k xcl addr n σ r g cx - ⟨⟨h, rfl, rfl⟩, hs, hw, hb⟩ - x hx
    obtain ⟨y, hy, -, hv, hS, -⟩ := (Ctx.Same.reset hs hw).read hx
    obtain ⟨σ', ho, hN⟩ := h.loadLRV (fun hc => h.g0 ▸ hK hc) hy
    rw [← hS.reset_eq] at hN
    obtain ⟨tr', v', rfl, -⟩ := (mem_readSuccs A).mp hx
    refine ⟨σ', hv ▸ ho, ⟨hN, rfl, rfl⟩, ?_, ?_, (readSuccs_bnd A iv hb h.ctx.sim.ivb hx).1⟩
    · show cx.stores = 0; exact hs
    · show cx.rmwWrote = false; exact hw
  store := H.store
  rmw := H.rmw }

/-- **Link theorem 1 for `EnvGLRV`, load-prefix trees, with or without a
release in flight** (`treeJ_envGLR_eraseWPRDM` at `EnvGLRV`). -/
theorem treeJ_envGLRV_eraseWPRDM {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    (hK : cl₀ → ClAt tid rS g₀ c) {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDM (nodeSimLRV_envGLRV (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀)
      (g₀ := g₀) (cl₀ := cl₀) (rS := rS) hst hK) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx) (hs : cx.stores = 0) (hw : cx.rmwWrote = false)
    (ha : MultiAccessS True (SokLR pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvGLRV I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDM _ hW ⟨⟨h.toReset (Ctx.Same.refl cx), rfl, rfl⟩, hs, hw, h.ctx.sim.bnd⟩ ha

/-- **Link theorem 1 for `EnvGLRV` at an instruction's start**, at the
knowledge `ThreadRuleRX.wp` gives the post: `cl ∧ Erase (setRes rF tid r) g ⊥ c`. -/
theorem treeJ_envGLRV_eraseWPRDM_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf) (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDM (nodeSimLRV_envGLRV (A := A) (pl := pl) (iv := instrViews t d) (rF := rF)
      (rv₀ := σ.r) (g₀ := g) (cl₀ := cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (rS := r) hst
      (fun hc => ⟨rF, hc.2⟩)) Q).W tree σ)
    (ha : MultiAccessS True (SokLR pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvGLRV I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g
          (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  have hN := hrel.toNodeRel rF d E hm
  treeJ_envGLRV_eraseWPRDM hst (fun hc => ⟨rF, hc.2⟩) hW { hN with cl := fun hc => hN.cl hc.1 } rfl rfl ha

end Link

end Kraken.Promising.SLR.EnvG
