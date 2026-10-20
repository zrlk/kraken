/-
Whole-thread environment: **the concrete link of
`EnvGLR` for load-prefix trees, with an in-flight release after the loads**.
ISA-neutral.

`MultiLink.lean` links load-prefix trees of `EnvG` without a release in
flight only (`pf = none`): an `EnvG` load adds `ClAt tid σ.r …` to `cl`, which
the link justifies by the instruction's start knowledge, and that needs the
actual resource to be the virtual one. In `EnvGLR` (`LREnv.lean`) a load
leaves `cl` alone, so the node relation after a load is the node relation
before it at the *same* knowledge `cl₀`, whether a release is in flight or
not (`NodeRel.loadLR`). With a release of `⟨l, v⟩` in flight the tree's
single write must be a store to `l`; a store of `v` fulfils the pending
promise (`NodeRel.storeS`, existing), a store of another value is overtaken on
every outcome (`NodeRel.storeOther`: coherence, as `overtaken_of_inflight`).

- `PreLR`: `MultiLink.PreM` at the knowledge `cl₀` (no `ClAt`);
- side conditions by in-flight message `pf`: loads always; a store to any
  location without a release in flight, else to the in-flight location
  (`SokLR`); RMWs only without one and not of release kind (`RokS`);
  write-free leaves only without one (`LokS`);
- `nodeSimLR_envGLR`: the `NodeSimM` instance (`MultiTreeLink.lean`);
- `treeJ_envGLR_eraseWPRDM(_start)`: **link theorem 1 for `EnvGLR`**, ending
  in the phase-1 post relation `PostS` (unchanged).
-/
import Kraken.Promising.SLR.EnvG.LREnv
import Kraken.Promising.SLR.EnvG.MultiLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

section Transport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}

/-- **Load transport of `EnvGLR`**: the node relation after the load, at the
reset of the load's context and the same knowledge `cl₀` (the load keeps the
resource, the ghost, the memory and the promises; the env's `cl` is
unchanged). No condition on an in-flight release. -/
theorem NodeRel.loadLR (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {k : LoadKind} {xcl : Bool} {l : Loc}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l) :
    ∃ σ', LoadOutLR A tid σ σ' k xcl l x.2.1 ∧ NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ' r g x.2.2.reset := by
  obtain ⟨tr, v, cx₁⟩ := x
  obtain ⟨cxe₁, hx', hc⟩ := h.ctx.read hx
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  simp only at hm1 hp1 ⊢
  refine ⟨{ σ with
      snap := c, g := g, vs := cxe₁.views
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
    res := h.res
    cl := h.cl
    fenced := h.fenced.read hx }

/-- **Every write of the in-flight location overtakes the pending promise**
when it lands above it (`overtaken_of_inflight` for any written value). -/
theorem overtaken_of_inflightV {cx cx' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v v₀ : Val}
    {trOpt : Option Time} {extra : View} {tw ts : Time} {ivs : InstrViews}
    (hc : cx' ∈ writeSuccs A tid ivs cx k xcl l v trOpt extra) (hev : WriteEv tid cx cx' l v trOpt tw)
    (hts : ts ∈ cx.prom) (hget : cx.mem.get? ts = some ⟨l, v₀, tid⟩) (hlt : ts < tw) : cx'.Overtaken := by
  have hne : ts ≠ tw := by omega_t
  refine ⟨ts, by rw [hev.prom]; exact (List.mem_erase_of_ne hne).mpr hts, ⟨l, v₀, tid⟩, ?_,
    Nat.le_trans (Nat.le_of_lt hlt) (writeSuccs_coh_tw' hc hev)⟩
  rcases hev.cases with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm]; exact hget
  · rw [hm, Memory.get?_append_of_le _ _ _ (cx.mem.last_le_of_get?_eq_some hget)]; exact hget

/-- **A store of another value to the in-flight location is overtaken** on
every outcome: it cannot fulfil the pending promise (other message), and it
lands above it (fresh, or on an own promise to `l`, which lies above the
pending one, `StartS`). -/
theorem NodeRel.storeOther (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {l : Loc} {v₀ : Val}
    (hst : StartS tid c t g (some (l, v₀))) {k : StoreKind} {v : Val} (hne : v ≠ v₀) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none) (hi : cx.Inv tid) : cx'.Overtaken := by
  obtain ⟨ts, hts, -, hgts, habove⟩ := hst.some l v₀ rfl
  obtain ⟨-, tw, -, hev, -, -⟩ := h.ctx.write (A := A) hi (ivLe_envIv _ (iv.forStore cx.stores))
    (h.ctx.sim.ivb.forStore cx.stores) (Nat.le_refl 0) (Nat.zero_le _) hc
  have hpc : cx.prom = t.prom := h.prom
  have hmc : cx.mem = c.mem := h.mem
  refine overtaken_of_inflightV hc hev (hpc ▸ hts) (hmc ▸ hgts) ?_
  rcases hev.cases with ⟨-, htp, hget⟩ | ⟨-, rfl⟩
  · by_cases e : tw = ts
    · subst e
      rw [hmc, hgts] at hget
      simp only [Option.some.injEq, Msg.mk.injEq] at hget
      exact absurd hget.2.1.symm hne
    · exact habove tw (hpc ▸ htp) e _ (hmc ▸ hget) rfl
  · have := cx.mem.last_le_of_get?_eq_some (hmc ▸ hgts : cx.mem.get? ts = _)
    omega_t

end Transport

/-! ## The relation before each access, and the transport -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **Before each access of a load-prefix tree of `EnvGLR`**: the phase-1
`PreS` at the reset context, at the start knowledge `cl₀`; no local write
yet; the actual context bounded. -/
def PreLR (tid : Nat) (pl : Plan) (iv : InstrViews) (rF : Nat → Res) (c : Config I) (t : Thread I) (rv₀ : Res)
    (g₀ : Ghost) (cl₀ : Prop) (rS : Res) (gS : Ghost) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx) : Prop :=
  PreS tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx.reset ∧ cx.stores = 0 ∧ cx.rmwWrote = false ∧ cx.Bnd

/-- The store side condition of the `EnvGLR` link: any store without a
release in flight, else a store to the in-flight location (any value). -/
abbrev SokLR (pf : Option (Loc × Val)) (l : Loc) (_v : Val) : Prop := pf = none ∨ ∃ v₀, pf = some (l, v₀)

/-- **The per-node transport of `EnvGLR` for load-prefix trees**, with an
in-flight release allowed after the loads. -/
theorem nodeSimLR_envGLR {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf) :
    NodeSimM A tid iv rF (fun _ => True) c t (EnvGLR I A tid pl) True (SokLR pf) (RokS A pf) (LokS pf)
      (fun σ r g cx => PreLR tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) := by
  have H := nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst
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
  fence_post := by
    intro k σ r g cx hp hok
    obtain ⟨σ', hst', hp'⟩ := H.fence_post hp hok
    exact ⟨σ', hst', hp'⟩
  load := by
    rintro k xcl addr n σ r g cx - ⟨⟨h, rfl, rfl⟩, hs, hw, hb⟩ - x hx
    obtain ⟨y, hy, -, hv, hS, -⟩ := (Ctx.Same.reset hs hw).read hx
    obtain ⟨σ', ho, hN⟩ := h.loadLR hy
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
    by_cases hSS : SokS pf ⟨addr, n⟩ v
    · rcases (H.store hSS hpre hok).1 cy' (by simpa using hcy) (hR.symm.erAt E) (hR.inv hi) hm with
        ho | ⟨r', g', σ', hst', E', hRS, hp'⟩
      · exact .inl (hS'.overtaken ho)
      · exact .inr ⟨r', g', σ', hst', hS'.erAt E', hS'.rStep hRS, hp'.same hS' hb'.1.loadViews hb'.1.succView⟩
    · rcases hS with hS | ⟨v₀, rfl⟩
      · exact absurd (.inl hS) hSS
      · have hne : v ≠ v₀ := fun e => hSS (.inr (by rw [e]))
        have hc0 : cy' ∈ writeSuccs A tid (iv.forStore cx.reset.stores) cx.reset k false ⟨addr, n⟩ v none := by
          simpa using hcy
        obtain ⟨h1, -, rfl⟩ := hpre
        exact .inl (hS'.overtaken (h1.storeOther hst hne hc0 (hR.inv hi)))
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

/-- **Link theorem 1 for `EnvGLR`, load-prefix trees, with or without a
release in flight**: from the phase-1 node relation at the instruction's
start (no local field written yet), the erasure WP with the phase-1 post
relation `PostS` at the start knowledge `cl₀`. -/
theorem treeJ_envGLR_eraseWPRDM {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDM (nodeSimLR_envGLR (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀)
      (g₀ := g₀) (cl₀ := cl₀) (rS := rS) hst) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx) (hs : cx.stores = 0) (hw : cx.rmwWrote = false)
    (ha : MultiAccessS True (SokLR pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvGLR I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDM _ hW ⟨⟨h.toReset (Ctx.Same.refl cx), rfl, rfl⟩, hs, hw, h.ctx.sim.bnd⟩ ha

/-- **Link theorem 1 for `EnvGLR` at an instruction's start**: from
`EnvRel` and the hypotheses of `ThreadRuleRX.wp`, at `ctx₀`. -/
theorem treeJ_envGLR_eraseWPRDM_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf) (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDM (nodeSimLR_envGLR (A := A) (pl := pl) (iv := instrViews t d) (rF := rF)
      (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hst) Q).W tree σ)
    (ha : MultiAccessS True (SokLR pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvGLR I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envGLR_eraseWPRDM hst hW (hrel.toNodeRel rF d E hm) rfl rfl ha

end Link

end Kraken.Promising.SLR.EnvG
