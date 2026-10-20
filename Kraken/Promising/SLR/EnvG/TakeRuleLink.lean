/-
**Part 5: the rule link with taking loads**. ISA-neutral. Adapted from
`EnvG/RuleLink.lean` (whose `LinkHyps`, `InvG`, `ThreadRuleRX.ofEnvG`
are frozen and unchanged).

`Q st σ` relates the thread's ISA state to an `EnvGT` state (the env whose
non-forwarded acquire loads take their exposed slots, `EnvG/TakeEnv.lean`).
`LinkHypsT` is `LinkHyps` with the judgments of `EnvGT`. The invariant is the
existing `InvG` (it does not mention the environment: the core `CoreAt` and
`Q`).

- `InvG.wpT`: link theorem 1 with taking loads
  (`treeJ_envGT_eraseWPRDS_start`) into `WpPostR`, the
  `EvTree.EraseWPRDS` obligation of `ThreadRuleRXGS.wp`.
- `InvG.prepayT`: `InvG.prepay` verbatim, with `TreeJLive.storeOkT` (the
  first store's permission is read off an `EnvGT` judgment; loads never
  precede the in-flight store).
- `ThreadRuleRXGS.ofEnvGT : ThreadRuleRXGS G₀ A B tid` and
  `npSafeP_of_envGT : NPSafeP … G₀ (K2Scope (model I) AllocIds) …` (by
  `NPSafeP.of_ruleRXGS`), whose Theorem 1′ is `theorem1IIPure_G₀_S`.

Phase-1 limits: single-access trees (`Phase1Shape`); releases are stores;
only non-forwarded acquire loads take; no fence-node take; the take and the
use of what is taken are in different instructions. The frame of the
conclusion is option (S)'s `K2Scope AllocIds`, not the full `K2₀` of
`ofEnvG`.
-/
import Kraken.Promising.SLR.EnvG.TakeLink
import Kraken.Promising.SLR.EnvG.RuleLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

section Mono

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {g₀ : Ghost} {σ : Type}

/-- `EraseWPRDS` is monotone in its postcondition. -/
theorem _root_.Kraken.Promising.EvTree.EraseWPRDS.mono {Post Q : σ → Res → Ghost → Ctx → Prop}
    (hQ : ∀ s r g cx, Post s r g cx → Q s r g cx) (tree : EvTree σ) :
    ∀ r g cx, tree.EraseWPRDS A tid iv rF T c t g₀ Post r g cx → tree.EraseWPRDS A tid iv rF T c t g₀ Q r g cx := by
  induction tree with
  | done s => exact fun r g cx h => hQ s r g cx h
  | fault _ => exact fun _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx h i => ih i r g cx (h i)
  | load k xcl l ret ih =>
    refine fun r g cx h x hx E => ?_
    obtain ⟨r', g', E', hR, hw⟩ := h x hx E
    exact ⟨r', g', E', hR, ih x.2.1 r' g' x.2.2 hw⟩
  | store k xcl l v ret ih =>
    refine fun r g cx h => ⟨fun cx' hc E hi hm => ?_, fun hx => ih false r g _ (h.2 hx)⟩
    rcases h.1 cx' hc E hi hm with ho | ⟨r', g', E', hR, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', E', hR, ih true r' g' cx' hw⟩
  | fence k ret ih => exact fun r g cx h => ih () r g _ h
  | rmw k noRet l op ret ih =>
    refine fun r g cx h x hx => ⟨fun hop => ih x.2.1 r g _ ((h x hx).1 hop), fun new hop cx' hc E hi hm => ?_⟩
    rcases (h x hx).2 new hop cx' hc E hi hm with ho | ⟨r', g', E', hR, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', E', hR, ih x.2.1 r' g' _ hw⟩

end Mono

/-- **`StoreOkAt` is a live tree judgment of `EnvGT`** (`TreeJLive.storeOk`
for `EnvGT`, which agrees with `EnvG` on stores and fences). -/
def TreeJLive.storeOkT (A : Arch) (tid : Nat) (pl : Plan) (σ : Type) : TreeJLive (EnvGT I A tid pl) σ where
  W := StoreOkAt A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store hok _ := hok
  rmw _ _ := trivial
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- **The hypotheses of the rule link with taking loads**: `LinkHyps` for
the judgments of `EnvGT`. -/
structure LinkHypsT (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1Shape A tree
  link : ∀ (J : TreeJLive (EnvGT I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`wp` with taking loads**: link theorem 1 with taking loads into
`WpPostR` (`InvG.wp` with `EraseWPRDS` at the start ghost). -/
theorem InvG.wpT (H : LinkHypsT A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res)
    (t : Thread I) (tree : EvTree I.State) (h : InvG A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g)
    (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRDS A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t g
      (WpPostR (InvG A tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hW := H.link (TreeJLive.eraseWPRDST (nodeSimT_envGT (A := A) (pl := pl) (iv := instrViews t (I.deps t.st))
    (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS) Q) t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envGT_eraseWPRDS_start hC.rel (I.deps t.st) hS E hm hW ha
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

/-- **`prepay` with taking loads** (`InvG.prepay` with the `EnvGT`
judgment `TreeJLive.storeOkT`; an instance of
`InvG.prepay_of_firstStoreG`). -/
theorem InvG.prepayT (H : LinkHypsT A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvG A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvG A tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨tree, hex, hrfl⟩ := hrel
  have hsh : Phase1Shape A tree := by
    obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
    obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
    exact H.shape _ _ (hst ▸ hQ₀) tree hex
  exact InvG.prepay_of_firstStoreG H.valid
    (fun st σ tree hQ hex => H.link (TreeJLive.storeOkT A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial))
    rF t₁ w h he hg ht E hm hnp tree hex hsh
    (relFulfilsLive_firstStore (List.mem_append_right _ (List.mem_singleton_self _)) (Memory.get?_append_last _ _)
      tree _ rfl rfl hsh hrfl)

end Rule

/-- **The rule link with taking loads**: a `ThreadRuleRXGS G₀` from a
thread-local invariant `Q` of `EnvGT` (`LinkHypsT`) and the postcondition at
halted threads (`hB`). -/
def ThreadRuleRXGS.ofEnvGT {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsT A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid where
  Inv := InvG A tid pl Q
  done h he hg hcl hd := InvG.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvG.wpT H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvG.prepayT H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafeP` with option (S)'s frame from the rule link with taking
loads** (`NPSafeP.of_ruleRXGS`); its Theorem 1′ is `theorem1IIPure_G₀_S`. -/
theorem npSafeP_of_envGT {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsT A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvG A tid pl Q cl c r g) :
    NPSafeP (model I) A B tid G₀ (K2Scope (model I) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofEnvGT H hB) n m cl c r g h

#print axioms ThreadRuleRXGS.ofEnvGT
#print axioms npSafeP_of_envGT

end Kraken.Promising.SLR.EnvG
