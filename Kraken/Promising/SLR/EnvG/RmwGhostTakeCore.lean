/-
Whole-thread environment, **Claim-conditional RMWs** part 6a: the ISA-neutral half of
`EnvG/RmwGhostTake.lean` (split; moved verbatim, names
unchanged): the claim-conditional environment **with taking loads**,
`EnvGTC` (`EnvGC`, `EnvG/RmwGhost.lean`, with `EnvGT`'s taking load step,
`EnvG/TakeEnv.lean`), and its ISA-neutral link.

- `EnvGTC`: state, permissions and store/RMW/fence steps of `EnvGC`
  (definitionally), load step `LoadOutT`.
- `nodeSimT2_envGTC`: the load field is `nodeSimT_envGT`'s, the others are
  `nodeSimS2_envGC`'s (the fields agree definitionally);
  `treeJ_envGTC_eraseWPRDSR(_start)`.
- `TreeJLive.storeOkTC`, `TreeJLive.rmwOkTC`, `LinkHypsTRC`,
  `InvGR.wpTRC`, `InvGR.prepayTRC` (from `InvGR.prepay_of_okAtC`),
  **`ThreadRuleRXGS.ofEnvGTRC : ThreadRuleRXGS G₀`**, `npSafeP_of_envGTRC`
  (frame `K2Scope AllocIds`).

The AArch64 instance stays in `EnvG/RmwGhostTake.lean`; the x64 one is in
`EnvG/X64RmwGhostLink.lean`, whose former copies (`EnvGTCI`,
`nodeSimT2_envGTCI`, …, `ThreadRuleRXGS.ofEnvGTRCI`) are now
statement-preserving aliases of these names.

Phase-1 limits: as `EnvG/TakeRLink.lean` except that release RMWs may give
away (from the thread's own resource) and release-only RMWs claim nothing;
a release RMW still cannot forward what it claims in the same instruction.
-/
import Kraken.Promising.SLR.EnvG.RmwGhostRule
import Kraken.Promising.SLR.EnvG.TakeRLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- **The claim-conditional environment with taking loads** of thread `tid`
under the plan `pl`: `EnvGC` with `EnvGT`'s load step. -/
def _root_.Kraken.Promising.SLR.EnvGTC (I : ISA) (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv where
  State := State I
  ok a σ := (EnvGC I A tid pl).ok a σ
  step a σ ret σ' := match a, ret with
    | .load k xcl addr n, v => LoadOutT A tid σ σ' k xcl ⟨addr, n⟩ v
    | .store k xcl addr n v, b => StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b
    | .rmw k addr n op, old => RmwOutC A tid pl σ σ' k ⟨addr, n⟩ op old
    | .fence k, _ => FenceOut σ σ' k

/-! ## The per-tree link -/

section LinkTRC

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The per-node transport of `EnvGTC`**: taking loads (`nodeSimT_envGT`)
and claim-conditional RMWs (`nodeSimS2_envGC`); no give-away side condition. -/
theorem nodeSimT2_envGTC {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf) :
    NodeSimT2 A tid iv rF (fun _ => True) c t gS (EnvGTC I A tid pl) (LokS pf) (SokS pf) (RokR pf) (LokS pf)
      (fun σ r g cx => PreS tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) :=
  have hT := nodeSimT_envGT (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst
  have hS := nodeSimS2_envGC (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst
  ⟨hS.pre_post, hS.fence_pre, hS.fence_post, hT.load, hS.store, hS.rmw⟩

/-- **Link theorem 1 for `EnvGTC`**. -/
theorem treeJ_envGTC_eraseWPRDSR {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDST2 (nodeSimT2_envGTC (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀)
      (g₀ := g₀) (cl₀ := cl₀) (rS := rS) hst) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid iv rF (fun _ => True) c t gS
      (PostOf (E := EnvGTC I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDST2 _ hW ⟨h, rfl, rfl⟩ ha

/-- **Link theorem 1 for `EnvGTC` at an instruction's start**. -/
theorem treeJ_envGTC_eraseWPRDSR_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDST2 (nodeSimT2_envGTC (A := A) (pl := pl) (iv := instrViews t d) (rF := rF)
      (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hst) Q).W tree σ)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid (instrViews t d) rF (fun _ => True) c t g
      (PostOf (E := EnvGTC I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envGTC_eraseWPRDSR hst hW (hrel.toNodeRel rF d E hm) ha

end LinkTRC

/-! ## The rule link -/

/-- The judgment yielding `StoreOkAt` (`EnvGTC` stores are `EnvG`'s). -/
def TreeJLive.storeOkTC (A : Arch) (tid : Nat) (pl : Plan) (σ : Type) : TreeJLive (EnvGTC I A tid pl) σ where
  W := StoreOkAt A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store hok _ := hok
  rmw _ _ := trivial
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- The judgment yielding `RmwOkAtC` (`EnvGTC` RMWs are `EnvGC`'s). -/
def TreeJLive.rmwOkTC (A : Arch) (tid : Nat) (pl : Plan) (σ : Type) : TreeJLive (EnvGTC I A tid pl) σ where
  W := RmwOkAtC A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store _ _ := trivial
  rmw hok _ := ⟨rfl, hok⟩
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- **The hypotheses of the rule link of `EnvGTC`**: `LinkHypsTR` over
`EnvGTC`, without the give-away side condition. -/
structure LinkHypsTRC (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeR A tree
  link : ∀ (J : TreeJLive (EnvGTC I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

section RuleTRC

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`wp` for `EnvGTC`** (`InvGR.wpTR` without the give-away side
condition). -/
theorem InvGR.wpTRC (H : LinkHypsTRC A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
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
  have hW := H.link (TreeJLive.eraseWPRDST2 (nodeSimT2_envGTC (A := A) (pl := pl)
    (iv := instrViews t (I.deps t.st)) (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS) Q)
    t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envGTC_eraseWPRDSR_start hC.rel (I.deps t.st) hS E hm hW ha
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

/-- **`prepay` for `EnvGTC`** (`InvGR.prepay_of_okAtC` with the `EnvGTC`
judgments; loads never precede the in-flight access). -/
theorem InvGR.prepayTRC (H : LinkHypsTRC A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
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
  InvGR.prepay_of_okAtC H.valid H.shape
    (fun st σ tree hQ hex =>
      ⟨H.link (TreeJLive.storeOkTC A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial),
        H.link (TreeJLive.rmwOkTC A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial)⟩)
    rF t₁ w h he hg ht E hm hnp hrel

end RuleTRC

/-- **The rule link of `EnvGTC`**: a `ThreadRuleRXGS G₀` from a thread-local
invariant `Q` of `EnvGTC` (`LinkHypsTRC`) and the postcondition at halted
threads (`hB`). -/
def ThreadRuleRXGS.ofEnvGTRC {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsTRC A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid where
  Inv := InvGR tid pl Q
  done h he hg hcl hd := InvGR.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvGR.wpTRC H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvGR.prepayTRC H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafeP` with option (S)'s frame from the rule link of `EnvGTC`**
(`NPSafeP.of_ruleRXGS`). -/
theorem npSafeP_of_envGTRC {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsTRC A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvGR tid pl Q cl c r g) :
    NPSafeP (model I) A B tid G₀ (K2Scope (model I) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofEnvGTRC H hB) n m cl c r g h

end Kraken.Promising.SLR.EnvG
