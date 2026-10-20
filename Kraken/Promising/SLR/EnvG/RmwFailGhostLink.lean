/-
Part 1: **the per-tree link of the claim-conditional
environment with failing in-flight release RMWs** (F × C). ISA-neutral. New
file, additive beside `EnvG/RmwGhostLink.lean` (C: `EnvGC`, no
`RelRmwGiveOk`, but `RokR`: an in-flight release RMW never fails) and
`EnvG/RmwFailLink.lean` (F: `RokF`/`PostSF`, but `EnvG` with `RelRmwGiveOk`).

`nodeSimS2F_envGC` is `nodeSimS2_envGC` with `RmwFailLink`'s failing branch:

- side condition `RokF` (an in-flight RMW of the in-flight location, any
  operation);
- post relation `PostSF`: a failing outcome of the in-flight RMW keeps the
  prepaid promise outstanding (`Alive`), which the rule passes to
  `WpPostRF`'s left disjunct and `NPSafeF`'s step guard excludes;
- the failing outcome is `NodeRel.rmwFail` (an `EnvG` outcome, an `EnvGC`
  one by `RmwOut.toC_none`); the succeeding in-flight outcome is
  `NodeRel.rmwRelC` (give from own resource, no `RelRmwGiveOk`), without a
  release in flight `NodeRel.rmwC'`.

This is the link a Treiber stack needs (`treiber_pp.kl`): a `casal` push
that gives the node away and may fail, and a `casal` pop that may fail.

Contents: `nodeSimS2F_envGC`, `treeJ_envGC_eraseWPRDSF(_start)`;
`nodeSimS2F_envGCAdj` (the adjacency version, moved here from
`EnvG/AdjSpikeLink.lean`), of which `nodeSimS2F_envGC` is the instance.
-/
import Kraken.Promising.SLR.EnvG.RmwGhostLink
import Kraken.Promising.SLR.EnvG.RmwFailLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The per-node transport of `EnvGCAdj` with failing in-flight RMWs**
(moved here from `EnvG/AdjSpikeLink.lean`; the RMW case
through `rmwCAdj'`/`rmwRelCAdj`). The generic form: `nodeSimS2F_envGC` is
its instance (`NodeSimS2.ofCAdj`). -/
theorem nodeSimS2F_envGCAdj {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf) :
    NodeSimS2 A tid iv rF (fun _ => True) c t (EnvGCAdj I A tid pl) (LokS pf) (SokS pf) (RokF pf) (LokS pf)
      (fun σ r g cx => PreS tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostSF tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) where
  pre_post hd hp := ((nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst).pre_post hd hp).toF
  fence_pre := (nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst).fence_pre
  fence_post {k} {σ} _ _ cx h _ := by
    have hm := fenceStep_mem cx k; have hp := fenceStep_prom cx k
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨fenceState σ k, fenceOut_fenceState σ k, h1.fence k, h2.congr hm hp, hm ▸ h3, ?_, h5⟩
    rcases h4 with h4 | ⟨ts, h1, h2, h3⟩
    · exact .inl (hp ▸ h4)
    · exact .inr ⟨ts, h1, h2, hp ▸ h3⟩
  load hL hp hok x hx := by
    obtain ⟨s', hs, hp'⟩ := (nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀)
      (cl₀ := cl₀) (rS := rS) hst).load hL hp hok x hx
    exact ⟨s', hs, hp'.toF⟩
  store hS hp hok := by
    obtain ⟨h1, h2⟩ := (nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀)
      (cl₀ := cl₀) (rS := rS) hst).store hS hp hok
    refine ⟨fun cx' hc E hi hm => ?_, fun hx => ?_⟩
    · rcases h1 cx' hc E hi hm with ho | ⟨r', g', s', hs, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', s', hs, E', hR, hp'.toF⟩
    · obtain ⟨s', hs, hp'⟩ := h2 hx
      exact ⟨s', hs, hp'.toF⟩
  rmw := by
    rintro k addr n op σ r g cx hR ⟨h, rfl, rfl⟩ hok x hx
    have hfail : op x.2.1 = none → ∃ σ', (EnvGCAdj I A tid pl).step (.rmw k addr n op) σ x.2.1 σ' ∧
        PostSF tid pl iv c t rv₀ g₀ cl₀ pf r g σ' r g (fenceOptCtx A x.2.2) := fun hop => by
      obtain ⟨σ', ho, hp⟩ := h.rmwFail hx hop
      obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
      obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
      obtain ⟨hm2, hp2⟩ := fenceOptCtx_memProm (A := A) x.2.2
      have hm : (fenceOptCtx A x.2.2).mem = c.mem := hm2.trans (hm1.trans (hm0.trans h.mem))
      have hpr : (fenceOptCtx A x.2.2).prom = t.prom := hp2.trans (hp1.trans (hp0.trans h.prom))
      obtain ⟨-, -, -, -, -, hcl, -⟩ := id ho
      refine ⟨σ', (ho.toC_none hop :), hp, WpPath.refl hm hpr, by rw [hm]; exact Nat.le_refl _, ?_,
        fun _ hc0 => hcl ▸ h.cl hc0⟩
      cases pf with
      | none => exact .inl fun ts hts => hst.none rfl ts (hpr ▸ hts)
      | some p =>
        obtain ⟨ts, hts, hpd, -, -⟩ := hst.some p.1 p.2 rfl
        exact .inr ⟨ts, hts, hpd, hpr ▸ hts⟩
    rcases hR with hpf | ⟨v, hpf⟩
    · refine ⟨hfail, fun new hop cx' hc E hi _ => ?_⟩
      rcases h.rmwCAdj' (hst.none hpf) hok hx hop hc E hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, -⟩
      · exact .inl ho
      · exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, .inl hpd, fun hne => absurd hpf hne⟩
    · subst hpf
      refine ⟨hfail, fun new hop cx' hc E hi _ => ?_⟩
      rcases h.rmwRelCAdj hst hok hx hop hc E hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, hcl⟩
      · exact .inl ho
      · exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, .inl hpd, fun _ hc0 => hcl ▸ h.cl hc0⟩

/-- **The per-node transport of `EnvGC` with failing in-flight RMWs**
(`nodeSimS2_envGC` with `RokF` and `PostSF`). -/
theorem nodeSimS2F_envGC {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf) :
    NodeSimS2 A tid iv rF (fun _ => True) c t (EnvGC I A tid pl) (LokS pf) (SokS pf) (RokF pf) (LokS pf)
      (fun σ r g cx => PreS tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostSF tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) :=
  (nodeSimS2F_envGCAdj hst).ofCAdj

/-- **Link theorem 1 for `EnvGC` with failing in-flight RMWs** (as
`treeJ_envGC_eraseWPRDSR`, with `RokF` and `PostSF`). -/
theorem treeJ_envGC_eraseWPRDSF {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDS2 (nodeSimS2F_envGC (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀)
      (g₀ := g₀) (cl₀ := cl₀) (rS := rS) hst) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokF pf) (LokS pf) tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvGC I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostSF tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDS2 _ hW ⟨h, rfl, rfl⟩ ha

/-- **Link theorem 1 for `EnvGC` with failing in-flight RMWs at an
instruction's start.** -/
theorem treeJ_envGC_eraseWPRDSF_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDS2 (nodeSimS2F_envGC (A := A) (pl := pl) (iv := instrViews t d) (rF := rF)
      (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hst) Q).W tree σ)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokF pf) (LokS pf) tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvGC I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostSF tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envGC_eraseWPRDSF hst hW (hrel.toNodeRel rF d E hm) ha

end Link

end Kraken.Promising.SLR.EnvG
