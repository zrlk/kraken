/-
**Part 1 of 4: the value-restricted environment and its
rule link** (route (c2) of the value-bridge design). ISA-neutral.

The chain answers a load in `EnvGCAdj` with any value of a message of an
admissible re-anchor: the erasure constrains values only through the ghost's
protocols, so a thread proof cannot use a *global value fact* (e.g. the private-stack layer's
`PtrsInHeap`). Route (c2) lets the thread assume that load answers satisfy `G`
(`valsEnv`), paid for by a per-thread value specification (the tree law
`J st → exec st = some tree → tree.AllInv G J`), which the token
(`EnvG/ValsToken.lean`) and the chain (`EnvG/ValsChain.lean`) consume.

Contents: `LoadVal`, **`valsEnv E G`** (the stack-frame pilot's definitions; reducible, `ok`
unchanged, `FenceMono` instance `E`'s), **`NodeSimS2.vals`** (per-node
simulations transport to `valsEnv` when the node precondition pins a
`MemInv G` memory), `LinkHypsFCAdjV`, **`InvGF.wpFCAdjV`**,
`InvGF.prepayFCAdjV`, `InvGF.mono_cl`. `valsEnv` restricts loads only (not an
RMW's old value); the F link's phase-1 limits apply unchanged.
-/
import Kraken.Promising.SLR.EnvG.AdjSpikeRule
import Kraken.Promising.SLR.EnvG.VCGenCommon
import Kraken.Promising.InvLink

namespace Kraken.Promising.SLR.EnvG.Vals

open Kraken Kraken.Promising Kraken.Promising.Sim Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The value-restricted environment -/

/-- The value condition of an access's answer: a load's value satisfies `G`
at its location; other answers are unconstrained. -/
@[simp] def LoadVal (G : Loc → Val → Prop) : (a : SharedAccess) → a.Ret → Prop
  | .load _ _ addr n, v => G ⟨addr, n⟩ v
  | _, _ => True

/-- **`E` with value-restricted load answers**: the same permissions, and only
the outcomes whose load values satisfy `G`. Reducible, so that `E`'s
`@[simp]` lemmas (typed at `E.State`) apply to its states. -/
@[reducible] def valsEnv (E : SharedEnv) (G : Loc → Val → Prop) : SharedEnv where
  State := E.State
  ok := E.ok
  step a σ r σ' := E.step a σ r σ' ∧ LoadVal G a r

/-- Fences are `E`'s (also serves x64's alias `FenceMonoX`). -/
instance (E : SharedEnv) [E.FenceMono] (G : Loc → Val → Prop) : (valsEnv E G).FenceMono where
  le := SharedEnv.FenceMono.le (env := E)
  refl := SharedEnv.FenceMono.refl (env := E)
  fenceInv σ k g hg :=
    ⟨(SharedEnv.FenceMono.fenceInv (env := E) σ k g hg).1,
      fun g' hs => (SharedEnv.FenceMono.fenceInv (env := E) σ k g hg).2 g' hs.1⟩

@[simp] theorem fenceMono_le_valsEnv (E : SharedEnv) [E.FenceMono] (G : Loc → Val → Prop) :
    (SharedEnv.FenceMono.le (env := valsEnv E G)) = SharedEnv.FenceMono.le (env := E) := rfl

/-! ## Link transport -/

/-- **Transport of a per-node simulation to the value-restricted env**, given
that the node precondition pins a memory satisfying `MemInv G`: a load answer
of the simulation is a message of that memory (`readSuccs_read`), hence in
`G` (`MemInv.read?`); the other accesses carry `LoadVal`'s `True`. The `W`
of `TreeJLive.eraseWPRDS2 (hs.vals hm) Q` is that of `hs`, by `rfl`. -/
theorem NodeSimS2.vals {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop}
    {c : Config I} {t : Thread I} {E : SharedEnv} {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} {Pre Post : E.State → Res → Ghost → Ctx → Prop}
    {G : Loc → Val → Prop}
    (hs : NodeSimS2 A tid iv rF T c t E Lok Sok Rok D Pre Post)
    (hm : ∀ {s r g cx}, Pre s r g cx → MemInv G cx.mem) :
    NodeSimS2 A tid iv rF T c t (valsEnv E G) Lok Sok Rok D Pre Post where
  pre_post := hs.pre_post
  fence_pre hp hok := let ⟨s', h1, h2⟩ := hs.fence_pre hp hok; ⟨s', ⟨h1, trivial⟩, h2⟩
  fence_post hp hok := let ⟨s', h1, h2⟩ := hs.fence_post hp hok; ⟨s', ⟨h1, trivial⟩, h2⟩
  load hL hp hok x hx :=
    let ⟨s', h1, h2⟩ := hs.load hL hp hok x hx
    ⟨s', ⟨h1, (hm hp).read? (Kraken.Promising.readSuccs_read A iv hx).1⟩, h2⟩
  store hS hp hok := by
    obtain ⟨h1, h2⟩ := hs.store hS hp hok
    refine ⟨fun cx' hc E hi hl => ?_, fun hx => ?_⟩
    · rcases h1 cx' hc E hi hl with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', s', ⟨hst, trivial⟩, E', hR, hp'⟩
    · obtain ⟨s', hst, hp'⟩ := h2 hx
      exact ⟨s', ⟨hst, trivial⟩, hp'⟩
  rmw hR hp hok x hx := by
    obtain ⟨h1, h2⟩ := hs.rmw hR hp hok x hx
    refine ⟨fun hop => ?_, fun new hop cx' hc E hi hl => ?_⟩
    · obtain ⟨s', hst, hp'⟩ := h1 hop
      exact ⟨s', ⟨hst, trivial⟩, hp'⟩
    · rcases h2 new hop cx' hc E hi hl with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', s', ⟨hst, trivial⟩, E', hR, hp'⟩

/-! ## The rule link over `valsEnv (EnvGCAdj …) G` -/

/-- **`LinkHypsFCAdj` with the judgment in the value-restricted env.** -/
structure LinkHypsFCAdjV (A : Arch) (tid : Nat) (pl : Plan) (G : Loc → Val → Prop)
    (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeF tree
  link : ∀ (J : TreeJLive (valsEnv (EnvGCAdj I A tid pl) G) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

section RuleFCAdjV

variable {A : Arch} {tid : Nat} {pl : Plan} {G : Loc → Val → Prop} {Q : I.State → State I → Prop}

/-- **`wp` over the value-restricted env**, given `MemInv G` of the
configuration's memory (the extension of the erasure). `InvGF.wpFCAdj`
verbatim but for `NodeSimS2.vals` (the node precondition's `NodeRel.mem`
pins `c.mem`). -/
theorem InvGF.wpFCAdjV (H : LinkHypsFCAdjV A tid pl G Q) {cl : Prop} {c₀ c : Config I} {r : Res}
    {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvGF tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) (hX : MemInv G c.mem)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostRF (InvGF tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hW := H.link (TreeJLive.eraseWPRDS2 (NodeSimS2.vals (G := G) (nodeSimS2F_envGCAdj (A := A) (pl := pl)
    (iv := instrViews t (I.deps t.st)) (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS)
      (fun hp => hp.1.mem ▸ hX)) Q)
    t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envGCAdj_eraseWPRDSF_start hC.rel (I.deps t.st) hS E hm hW ha
  refine EvTree.EraseWPRD.mono ?_ tree _ _ _ hwp
  rintro st r' g' cx' ⟨σ', hQ', hP, ⟨hg', hkeep, hnew, hacq, hown⟩, hlast, hpd, hcl⟩
  rcases hpd with hpd | halive
  case inr => exact .inl halive
  refine .inr ⟨hg', hkeep, hnew, hacq, hown, fun t' ht' _ => ?_⟩
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

/-- The judgment yielding `StoreOkAt`, over the value-restricted env
(`TreeJLive.storeOkCAdj`). -/
def TreeJLive.storeOkCAdjV (A : Arch) (tid : Nat) (pl : Plan) (G : Loc → Val → Prop) (σ : Type) :
    TreeJLive (valsEnv (EnvGCAdj I A tid pl) G) σ where
  W := StoreOkAt A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store hok _ := hok
  rmw _ _ := trivial
  fence _ h := h _ ⟨fenceOut_fenceState _ _, trivial⟩

/-- The judgment yielding `RmwOkAtCAdj`, over the value-restricted env
(`TreeJLive.rmwOkCAdj`). -/
def TreeJLive.rmwOkCAdjV (A : Arch) (tid : Nat) (pl : Plan) (G : Loc → Val → Prop) (σ : Type) :
    TreeJLive (valsEnv (EnvGCAdj I A tid pl) G) σ where
  W := RmwOkAtCAdj A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store _ _ := trivial
  rmw hok _ := ⟨rfl, hok⟩
  fence _ h := h _ ⟨fenceOut_fenceState _ _, trivial⟩

/-- **`prepay` over the value-restricted env**: the existing
`InvGF.prepay_of_okAtFCAdj`, fed by the two judgments above. -/
theorem InvGF.prepayFCAdjV (H : LinkHypsFCAdjV A tid pl G Q) {cl : Prop} {c₀ c : Config I} {r : Res}
    {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvGF tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvGF tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) :=
  InvGF.prepay_of_okAtFCAdj H.valid H.shape
    (fun st σ tree hQ hex =>
      ⟨H.link (TreeJLive.storeOkCAdjV A tid pl G I.State) st σ tree hQ hex (fun _ _ _ => trivial),
        H.link (TreeJLive.rmwOkCAdjV A tid pl G I.State) st σ tree hQ hex (fun _ _ _ => trivial)⟩)
    rF t₁ w h he hg ht E hm hnp hrel

end RuleFCAdjV

/-- `InvGF` is antitone in the closure flag. -/
theorem InvGF.mono_cl {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop} {cl cl' : Prop} {c : Config I}
    {r : Res} {g : Ghost} (hcl : cl' → cl) (h : InvGF tid pl Q cl c r g) : InvGF tid pl Q cl' c r g :=
  let ⟨σ, t, hC, hQ⟩ := h
  ⟨σ, t, { hC with rel := { hC.rel with cl := fun h => hC.rel.cl (hcl h) } }, hQ⟩

end Kraken.Promising.SLR.EnvG.Vals

#print axioms Kraken.Promising.SLR.EnvG.Vals.InvGF.wpFCAdjV
