/-
**Part 1: the link with taking loads and
release-kind RMWs** (`ThreadRuleRXGS.ofEnvGTR`). ISA-neutral. Additive: it
composes the take link with taking loads (`EnvG/TakeLink.lean`,
`EnvG/TakeRuleLink.lean`) and the release-RMW extension's link with release-kind RMWs
(`EnvG/LinkR.lean`, `EnvG/RuleLink.lean` § release-kind RMWs); nothing else changes.

- `NodeSimT2`: the per-node transport whose load field may take (as
  `NodeSimT`) and whose RMW side condition sees the RMW's kind, location and
  operation (as `NodeSimS2`); `TreeJLive.eraseWPRDST2`, `treeJ_eraseWPRDST2`:
  link theorem 1 (abstract) for `EvTree.EraseWPRDS`.
- `nodeSimT2_envGT`: the instance for `EnvGT` (the load field is
  `nodeSimT_envGT`'s, the others are `nodeSimS2_envG`'s, `EnvGT` and `EnvG`
  agreeing on stores, RMWs and fences definitionally);
  `treeJ_envGT_eraseWPRDSR(_start)`.
- `LinkHypsTR` (`LinkHypsR` for the judgments of `EnvGT`), `InvGR.wpTR`,
  `InvGR.prepayTR` (`InvGR.prepay` with the `EnvGT` judgments
  `TreeJLive.storeOkT`/`TreeJLive.rmwOkT`; both from `InvGR.prepay_of_okAt`), **`ThreadRuleRXGS.ofEnvGTR :
  ThreadRuleRXGS G₀`**, `npSafeP_of_envGTR` (frame `K2Scope AllocIds`).
- `envGT_step_rel`, `link_relFixT`: every `EnvGT` step keeps the env's
  release predicates (a take allocates an acquire id and renames slots, never
  touching `rel`), so a program-specific `RelRmwGiveOk I pl rel₀` discharges
  `LinkHypsTR.giveOk`.

Phase-1 limits: the union of both routes' limits. Single-access trees
(`Phase1ShapeR`); an in-flight release RMW never fails; planned-release RMWs
claim nothing they give away (`RelRmwGiveOk`, so **a release RMW cannot
forward what it claims**, which rules out the `ldaddal` ticket lock's token
chain); release RMWs are whole; only
non-forwarded acquire loads take (no take at an RMW or a fence node); the
take and the use of what is taken are in different instructions; the frame
is option (S)'s `K2Scope AllocIds`.
-/
import Kraken.Promising.SLR.EnvG.TakeRuleLink
import Kraken.Promising.SLR.EnvG.LinkR

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The per-node transport (abstract) -/

/-- **Per-node transport with taking loads and RMW side conditions on kind,
location and operation** (`NodeSimT` with `NodeSimS2`'s RMW field). -/
structure NodeSimT2 (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res) (T : Nat → Prop) (c : Config I)
    (t : Thread I) (g₀ : Ghost) (E : SharedEnv) (Lok : Prop) (Sok : Loc → Val → Prop)
    (Rok : RmwKind → Loc → (Val → Option Val) → Prop) (D : Prop)
    (Pre Post : E.State → Res → Ghost → Ctx → Prop) : Prop where
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
  rmw : ∀ {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {s r g cx}, Rok k ⟨addr, n⟩ op →
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
  {t : Thread I} {g₀ : Ghost} {E : SharedEnv} {Lok : Prop} {Sok : Loc → Val → Prop}
  {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} {Pre Post : E.State → Res → Ghost → Ctx → Prop}

/-- **`EraseWPRDS` is a live tree judgment** of any environment with a
`NodeSimT2` (`TreeJLive.eraseWPRDST` with `SingleAccessS2`). -/
def TreeJLive.eraseWPRDST2 (hs : NodeSimT2 A tid iv rF T c t g₀ E Lok Sok Rok D Pre Post) {σ : Type}
    (Q : σ → E.State → Prop) : TreeJLive E σ where
  W tree s :=
    (∀ r g cx, Pre s r g cx → SingleAccessS2 Lok Sok Rok D tree →
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

/-- **Link theorem 1, abstract form, with taking loads and RMW side
conditions on location and operation.** -/
theorem treeJ_eraseWPRDST2 (hs : NodeSimT2 A tid iv rF T c t g₀ E Lok Sok Rok D Pre Post) {σ : Type}
    {Q : σ → E.State → Prop} {tree : EvTree σ} {s : E.State} (hW : (TreeJLive.eraseWPRDST2 hs Q).W tree s)
    {r : Res} {g : Ghost} {cx : Ctx} (hp : Pre s r g cx) (ha : SingleAccessS2 Lok Sok Rok D tree) :
    tree.EraseWPRDS A tid iv rF T c t g₀ (PostOf Q Post) r g cx :=
  hW.1 r g cx hp ha

end Link

/-! ## The instance for `EnvGT` -/

section LinkTR

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The per-node transport of `EnvGT` with release-kind RMWs**: taking
loads (`nodeSimT_envGT`) and the RMW side condition `RokR`
(`nodeSimS2_envG`). -/
theorem nodeSimT2_envGT {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    (hG : RelRmwGiveOk I pl gS.rel) :
    NodeSimT2 A tid iv rF (fun _ => True) c t gS (EnvGT I A tid pl) (LokS pf) (SokS pf) (RokR pf) (LokS pf)
      (fun σ r g cx => PreS tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) :=
  have hT := nodeSimT_envGT (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst
  have hS := nodeSimS2_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst hG
  ⟨hS.pre_post, hS.fence_pre, hS.fence_post, hT.load, hS.store, hS.rmw⟩

/-- **Link theorem 1 with taking loads and release-kind RMWs**. -/
theorem treeJ_envGT_eraseWPRDSR {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    (hG : RelRmwGiveOk I pl gS.rel) {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDST2 (nodeSimT2_envGT (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀)
      (g₀ := g₀) (cl₀ := cl₀) (rS := rS) hst hG) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid iv rF (fun _ => True) c t gS
      (PostOf (E := EnvGT I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDST2 _ hW ⟨h, rfl, rfl⟩ ha

/-- **Link theorem 1 with taking loads and release-kind RMWs at an
instruction's start**: from `EnvRel` and the hypotheses of
`ThreadRuleRXGS.wp`, at `ctx₀`. -/
theorem treeJ_envGT_eraseWPRDSR_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf) (hG : RelRmwGiveOk I pl g.rel)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDST2 (nodeSimT2_envGT (A := A) (pl := pl) (iv := instrViews t d) (rF := rF)
      (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hst hG) Q).W tree σ)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid (instrViews t d) rF (fun _ => True) c t g
      (PostOf (E := EnvGT I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envGT_eraseWPRDSR hst hG hW (hrel.toNodeRel rF d E hm) ha

end LinkTR

/-! ## The rule link -/

/-- **`RmwOkAt` is a live tree judgment of `EnvGT`** (`TreeJLive.rmwOk` for
`EnvGT`, which agrees with `EnvG` on RMWs and fences). -/
def TreeJLive.rmwOkT (A : Arch) (tid : Nat) (pl : Plan) (σ : Type) : TreeJLive (EnvGT I A tid pl) σ where
  W := RmwOkAt A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store _ _ := trivial
  rmw hok _ := ⟨rfl, hok⟩
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- **The hypotheses of the rule link with taking loads and release-kind
RMWs**: `LinkHypsR` for the judgments of `EnvGT`. -/
structure LinkHypsTR (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeR A tree
  giveOk : ∀ st σ, Q st σ → RelRmwGiveOk I pl σ.g.rel
  link : ∀ (J : TreeJLive (EnvGT I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- The hypotheses with taking loads and the give-away side condition
(`LinkHyps.toR` for `EnvGT`). -/
theorem LinkHypsT.toR {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop} (H : LinkHypsT A tid pl Q)
    (hG : ∀ st σ, Q st σ → RelRmwGiveOk I pl σ.g.rel) : LinkHypsTR A tid pl Q :=
  ⟨H.valid, fun st σ hQ tree hex => (H.shape st σ hQ tree hex).toR, hG, H.link⟩

section RuleTR

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`wp` with taking loads and release-kind RMWs** (`InvGR.wp` with
`EraseWPRDS` at the start ghost). -/
theorem InvGR.wpTR (H : LinkHypsTR A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvGR tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRDS A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t g
      (WpPostR (InvGR tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start (A := A)
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hG : RelRmwGiveOk I pl g.rel := by rw [hC.rel.ghost.rel]; exact H.giveOk _ _ hQ
  have hW := H.link (TreeJLive.eraseWPRDST2 (nodeSimT2_envGT (A := A) (pl := pl)
    (iv := instrViews t (I.deps t.st)) (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS hG) Q)
    t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envGT_eraseWPRDSR_start hC.rel (I.deps t.st) hS hG E hm hW ha
  refine EvTree.EraseWPRDS.mono ?_ tree _ _ _ hwp
  rintro st r' g' cx' ⟨σ', hQ', hP, ⟨hg', hkeep, hnew, hacq, hown⟩, hlast, hpd, hcl⟩
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

/-- **`prepay` with taking loads and release-kind RMWs** (`InvGR.prepay`
with the `EnvGT` judgments `TreeJLive.storeOkT`/`TreeJLive.rmwOkT`; loads
never precede the in-flight access). Proved, as `InvGR.prepay`, from the
shared body `InvGR.prepay_of_okAt` (`EnvG/RuleLink.lean`). -/
theorem InvGR.prepayTR (H : LinkHypsTR A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvGR tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvGR tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) :=
  InvGR.prepay_of_okAt H.valid H.shape H.giveOk
    (fun st σ tree hQ hex =>
      ⟨H.link (TreeJLive.storeOkT A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial),
        H.link (TreeJLive.rmwOkT A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial)⟩)
    rF t₁ w h he hg ht E hm hnp hrel

end RuleTR

/-! ### Fixing the release predicates -/

/-- The iterated take keeps the release predicates. -/
theorem takeAll_rel (l : Loc) (tr : Time) (r : Res) (g : Ghost) : (takeAll l tr r g).g.rel = g.rel := by
  unfold takeAll
  suffices ∀ (L : List PredId) (a : TakeAcc), (L.foldl (takeStep l tr) a).g.rel = a.g.rel from this _ _
  intro L
  induction L with
  | nil => intro a; rfl
  | cons ι L ih =>
    intro a
    rw [List.foldl_cons, ih]
    unfold takeStep
    split <;> rfl

/-- **Every `EnvGT` step keeps the env's release predicates** (`envG_step_rel`
for `EnvGT`: a take never touches `rel`). -/
theorem envGT_step_rel {A : Arch} {tid : Nat} {pl : Plan} {a : SharedAccess} {σ σ' : State I}
    {ret : a.Ret} (h : (EnvGT I A tid pl).step a σ ret σ') : σ'.g.rel = σ.g.rel := by
  cases a with
  | load k xcl addr n =>
    obtain ⟨ga, hanc, -, -, tr, -, -, -, a, ha, -, hg, -⟩ := h
    rw [hg]
    by_cases hc : TakeCond A k σ.vs ⟨addr, n⟩ tr
    · rw [ha.1 hc, takeAll_rel]; exact hanc.ghost.rel
    · rw [ha.2 hc]; exact hanc.ghost.rel
  | store => exact envG_step_rel (I := I) (A := A) (tid := tid) (pl := pl) (ret := ret) h
  | rmw => exact envG_step_rel (I := I) (A := A) (tid := tid) (pl := pl) (ret := ret) h
  | fence => exact envG_step_rel (I := I) (A := A) (tid := tid) (pl := pl) (ret := ret) h

/-- A live tree judgment of `EnvGT` read at env states with release
predicates `rel₀` (`TreeJLive.relFix` for `EnvGT`). -/
def TreeJLive.relFixT {A : Arch} {tid : Nat} {pl : Plan} {σT : Type} (J : TreeJLive (EnvGT I A tid pl) σT)
    (rel₀ : Loc → Pred) : TreeJLive (EnvGT I A tid pl) σT where
  W t s := s.g.rel = rel₀ → J.W t s
  Post st s := s.g.rel = rel₀ → J.Post st s
  done h e := J.done (h e)
  fault _ := J.fault
  choose h e := J.choose fun i => h i e
  load h₁ h₂ e := J.load h₁ fun v g' hs => h₂ v g' hs ((envGT_step_rel hs).trans e)
  store h₁ h₂ e := J.store h₁ fun b g' hs => h₂ b g' hs ((envGT_step_rel hs).trans e)
  rmw h₁ h₂ e := J.rmw h₁ fun v g' hs => h₂ v g' hs ((envGT_step_rel hs).trans e)
  fence h₁ h₂ e := J.fence h₁ fun g' hs => h₂ g' hs ((envGT_step_rel hs).trans e)

/-- **A link of `EnvGT` for `Q` is a link for `Q` with fixed release
predicates** (`link_relFix` for `EnvGT`). -/
theorem link_relFixT {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop} (rel₀ : Loc → Pred)
    (hlink : ∀ (J : TreeJLive (EnvGT I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
      (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ) :
    ∀ (J : TreeJLive (EnvGT I A tid pl) I.State) st σ tree, (Q st σ ∧ σ.g.rel = rel₀) → I.exec st = some tree →
      (∀ st' σ', (Q st' σ' ∧ σ'.g.rel = rel₀) → J.Post st' σ') → J.W tree σ :=
  fun J st σ tree hQ hex hJ =>
    hlink (J.relFixT rel₀) st σ tree hQ.1 hex
      (fun st' σ' hQ' => show (J.relFixT rel₀).Post st' σ' from fun e => hJ st' σ' ⟨hQ', e⟩) hQ.2

/-- **The rule link with taking loads and release-kind RMWs**: a
`ThreadRuleRXGS G₀` from a thread-local invariant `Q` of `EnvGT`
(`LinkHypsTR`) and the postcondition at halted threads (`hB`). -/
def ThreadRuleRXGS.ofEnvGTR {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsTR A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid where
  Inv := InvGR tid pl Q
  done h he hg hcl hd := InvGR.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvGR.wpTR H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvGR.prepayTR H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafeP` with option (S)'s frame from the rule link with taking loads
and release-kind RMWs** (`NPSafeP.of_ruleRXGS`); its Theorem 1′ is
`theorem1IIPure_G₀_S`. -/
theorem npSafeP_of_envGTR {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsTR A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvGR tid pl Q cl c r g) :
    NPSafeP (model I) A B tid G₀ (K2Scope (model I) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofEnvGTR H hB) n m cl c r g h

#print axioms ThreadRuleRXGS.ofEnvGTR
#print axioms npSafeP_of_envGTR

end Kraken.Promising.SLR.EnvG
