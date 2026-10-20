/-
The failing-RMW route, part 2: **the link with failing in-flight
release RMWs**. ISA-neutral. Additive beside `EnvG/LinkR.lean`.

`LinkR`'s side condition `RokR` asks an in-flight RMW (`pf = some (l, v)`)
never to fail (`∀ x, op x ≠ none`), because a failing outcome leaves the
pending promise outstanding and `PostS` asks for no own pending promise after
the instruction. Here:

- `RokF pf k l op`: `pf = none`, or the RMW writes the in-flight location
  (`pf = some (l, v)`), with any operation;
- `PostSF`: `PostS` whose "no own pending promise" conjunct may instead be
  the **in-flight escape** `Alive`: an own promise pending at the
  instruction's start is still outstanding. Only the failing outcome of the
  in-flight RMW produces it (`NodeRel.rmwFail` at the in-flight resource: the
  env's failing outcome is a read, the actual resource keeps the prepaid
  release); the rule passes it to `WpPostRF`'s left disjunct, which
  `NPSafeF`'s step guard excludes (`EnvG/RmwFailRule.lean`).
- the succeeding outcome is `NodeRel.rmwRelS` unchanged: it never used
  totality.

Contents: `Alive`, `PostSF`, `PostS.toF`, `RokF`, `RokR.toF`,
`nodeSimS2F_envG`, `treeJ_envG_eraseWPRDSF(_start)`.
-/
import Kraken.Promising.SLR.EnvG.LinkR

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The in-flight escape**: an own promise pending at the instruction's
start (`t`, ghost `gS`) is still outstanding in context `cx`. -/
def Alive (t : Thread I) (gS : Ghost) (cx : Ctx) : Prop :=
  ∃ ts ∈ t.prom, ts ∈ gS.pend ∧ ts ∈ cx.prom

/-- **Post relation with the in-flight escape** (`PostS` whose "no own
pending promise" conjunct may be `Alive`). -/
def PostSF (tid : Nat) (pl : Plan) (iv : InstrViews) (c : Config I) (t : Thread I) (rv₀ : Res) (g₀ : Ghost)
    (cl₀ : Prop) (pf : Option (Loc × Val)) (rS : Res) (gS : Ghost) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx) :
    Prop :=
  PostRel tid pl iv c t rv₀ g₀ cl₀ σ r g cx ∧ WpPath c tid t rS gS r g cx ∧ c.mem.last ≤ cx.mem.last ∧
    ((∀ ts ∈ cx.prom, ts ∉ g.pend) ∨ Alive t gS cx) ∧ (pf ≠ none → cl₀ → σ.cl)

theorem PostS.toF {pf : Option (Loc × Val)} {rS : Res} {gS : Ghost} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}
    (h : PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) : PostSF tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx :=
  ⟨h.1, h.2.1, h.2.2.1, .inl h.2.2.2.1, h.2.2.2.2⟩

/-- **RMW side condition with failing in-flight RMWs**: any RMW without a
release in flight; with one in flight, an RMW of its location, any
operation. -/
abbrev RokF (pf : Option (Loc × Val)) (_k : RmwKind) (l : Loc) (_op : Val → Option Val) : Prop :=
  pf = none ∨ ∃ v, pf = some (l, v)

theorem RokR.toF {pf : Option (Loc × Val)} {k : RmwKind} {l : Loc} {op : Val → Option Val} (h : RokR pf k l op) :
    RokF pf k l op := by
  rcases h with h | ⟨v, h, -⟩
  · exact .inl h
  · exact .inr ⟨v, h⟩

/-- **The per-node transport of `EnvG` with failing in-flight RMWs**
(`nodeSimS2_envG` with `RokF` and `PostSF`). -/
theorem nodeSimS2F_envG {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    (hG : RelRmwGiveOk I pl gS.rel) :
    NodeSimS2 A tid iv rF (fun _ => True) c t (EnvG I A tid pl) (LokS pf) (SokS pf) (RokF pf) (LokS pf)
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
    have hfail : op x.2.1 = none → ∃ σ', (EnvG I A tid pl).step (.rmw k addr n op) σ x.2.1 σ' ∧
        PostSF tid pl iv c t rv₀ g₀ cl₀ pf r g σ' r g (fenceOptCtx A x.2.2) := fun hop => by
      obtain ⟨σ', ho, hp⟩ := h.rmwFail hx hop
      obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
      obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
      obtain ⟨hm2, hp2⟩ := fenceOptCtx_memProm (A := A) x.2.2
      have hm : (fenceOptCtx A x.2.2).mem = c.mem := hm2.trans (hm1.trans (hm0.trans h.mem))
      have hpr : (fenceOptCtx A x.2.2).prom = t.prom := hp2.trans (hp1.trans (hp0.trans h.prom))
      obtain ⟨-, -, -, -, -, hcl, -⟩ := id ho
      refine ⟨σ', ho, hp, WpPath.refl hm hpr, by rw [hm]; exact Nat.le_refl _, ?_,
        fun _ hc0 => hcl ▸ h.cl hc0⟩
      cases pf with
      | none => exact .inl fun ts hts => hst.none rfl ts (hpr ▸ hts)
      | some p =>
        obtain ⟨ts, hts, hpd, -, -⟩ := hst.some p.1 p.2 rfl
        exact .inr ⟨ts, hts, hpd, hpr ▸ hts⟩
    rcases hR with hpf | ⟨v, hpf⟩
    · refine ⟨hfail, fun new hop cx' hc E hi _ => ?_⟩
      rcases h.rmwS' (hst.none hpf) hok hx hop hc E hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, -⟩
      · exact .inl ho
      · exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, .inl hpd, fun hne => absurd hpf hne⟩
    · subst hpf
      refine ⟨hfail, fun new hop cx' hc E hi _ => ?_⟩
      rcases h.rmwRelS hst hG hok hx hop hc E hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, hcl⟩
      · exact .inl ho
      · exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, .inl hpd, fun _ hc0 => hcl ▸ h.cl hc0⟩

/-- **Link theorem 1 for `EnvG` with failing in-flight RMWs** (as
`treeJ_envG_eraseWPRDSR`, with `RokF` and `PostSF`). -/
theorem treeJ_envG_eraseWPRDSF {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    (hG : RelRmwGiveOk I pl gS.rel) {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDS2 (nodeSimS2F_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀)
      (cl₀ := cl₀) (rS := rS) hst hG) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokF pf) (LokS pf) tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostSF tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDS2 _ hW ⟨h, rfl, rfl⟩ ha

/-- **Link theorem 1 with failing in-flight RMWs at an instruction's
start.** -/
theorem treeJ_envG_eraseWPRDSF_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf) (hG : RelRmwGiveOk I pl g.rel)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDS2 (nodeSimS2F_envG (A := A) (pl := pl) (iv := instrViews t d) (rF := rF)
      (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hst hG) Q).W tree σ)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokF pf) (LokS pf) tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostSF tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envG_eraseWPRDSF hst hG hW (hrel.toNodeRel rF d E hm) ha

end Link

end Kraken.Promising.SLR.EnvG
