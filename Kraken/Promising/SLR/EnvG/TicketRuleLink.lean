/-
**Layer L, part 4: the ticket rule link.**
ISA-neutral. Adapted from `EnvG/TakeRuleLink.lean` and
`EnvG/Prepay.lean` (nothing else changes).

`Q st σ` relates the thread's ISA state to an `EnvGTD` state (the ticket
environment, `EnvG/TicketEnv.lean`). `LinkHypsTD` is `LinkHypsT` with the
judgments of `EnvGTD`. The invariant `InvGTD` is `InvG` (the core `CoreAt`
and `Q`) plus the **`coh x` transfer** `OwnX`: when the env's `coh x` is `0`,
so is the thread's (the env's views only bound the thread's from below; the
ticket RMW needs the thread's, `NodeRel.rmwTD`).

- `prepayGenericTD`: `prepayGeneric` for a store to a location other than
  `x`, with `TX` after the promise (`TicketInv.grow` for `prepayGhost`,
  `CountInv.append`); from the ghost-exposing `prepayGenericG`.
- `StoreOkAtD` / `TreeJLive.storeOkTD` / `FirstStore.storeOkD`: the first
  store's permission read off an `EnvGTD` judgment, with its location not
  `x` (so every promise is to another location).
- `InvGTD.wp`, `InvGTD.prepay`: `InvG.wpT` / `InvG.prepayT` for `EnvGTD`,
  into `ThreadRuleRXGSXE`'s obligations with `X = TX D` (`wp` verbatim;
  `prepay` via the generic `CoreAt.prepay_of_firstStoreGX`).
- `ThreadRuleRXGSXE.ofEnvGTD : ThreadRuleRXGSXE G₀ D.TX A B tid` and
  `npSafeP_of_envGTD` (by `NPSafeP.of_ruleRXGSXE`), whose Theorem 1′ is
  `theorem1IIPureX_G₀_S` with the promise law `tx_promiseLaw`.
- `NoFaultRuleSXE` / `NoFaultRuleSXE.ofNoFault`: `NoFaultRuleS`
  (`EnvG/TakeNoFault.lean`) for `ThreadRuleRXGSXE`, same field;
  `InvGTD.q_at`: `Q` at the current thread state (`InvG.q_at`).
-/
import Kraken.Promising.SLR.EnvG.TicketLink
import Kraken.Promising.SLR.EnvG.TakeRuleLink
import Kraken.Promising.SLR.EnvG.Prepay

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Prepay keeping `TX` -/

/-- **The generic prepay theorem at a store to a location other than `x`,
keeping `TX`** (`prepayGenericG`, with `TX` after the promise). -/
theorem prepayGenericTD {A : Arch} {D : Dispenser} (tid : Nat) (pl : Plan) (σ : State I) (k : StoreKind) (l : Loc)
    (v : Val) (c : Config I) (g : Ghost) (rF : Nat → Res) (t₁ : Thread I) (_ : pl.Valid)
    (hok : StoreOk A tid pl σ k false l v) (hanc : AnchorOk tid σ c g) (ht : c.threads[tid]? = some t₁)
    (E : Erase (setRes rF tid σ.r) g (fun _ => True) c) (hwb : WriteBound A σ.vs k l (c.mem.last + 1))
    (hX : D.TX g c) (hlx : l ≠ D.x) :
    ∃ (r' : Res) (g' : Ghost),
      Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ ⟨l, v, tid⟩) ∧ g.Le g' ∧
      (c.mem.append ⟨l, v, tid⟩).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append ⟨l, v, tid⟩).2) ∧
      r' = pl.after l v (c.mem.last + 1) σ.cl σ.r ∧
      (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB σ.r g x b) ∧
      D.TX g' (PromisedBy c tid t₁ ⟨l, v, tid⟩) := by
  obtain ⟨r', ss, E', hle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩ :=
    prepayGenericG (A := A) tid pl σ k l v c g rF t₁ ‹pl.Valid› hok hanc ht E hwb
  -- `TX` after the promise: no message to `x`
  have hsz := Config.withThread_size c tid { t₁ with prom := t₁.prom ++ [(c.mem.append ⟨l, v, tid⟩).2] }
    (c.mem.append ⟨l, v, tid⟩).1
  have hC : D.CountInv (PromisedBy c tid t₁ ⟨l, v, tid⟩) :=
    hX.2.append (w := ⟨l, v, tid⟩) rfl (fun h => absurd h hlx) hsz (fun h => absurd h hlx)
  exact ⟨r', _, E', hle, hpend, hkeep, hnew, hr', hacq, hK2, hK1,
    ⟨Dispenser.TicketInv.grow E hX.1 (Memory.Prefix.append _ _) hC.monoX rfl rfl rfl
      (fun s hs => List.mem_append_left _ hs), hC⟩⟩

/-! ## The first store's permission in the ticket environment -/

/-- `StoreOk` at the first store reached by fences, to a location other than
`x` (`StoreOkAt` for `EnvGTD`). -/
def StoreOkAtD (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) {σ : Type} : EvTree σ → State I → Prop
  | .fence k ret, s => StoreOkAtD A tid pl D (ret ()) (fenceState s k)
  | .store k xcl l v _, s => StoreOk A tid pl s k xcl l v ∧ l ≠ D.x
  | _, _ => True

/-- **`StoreOkAtD` is a live tree judgment of `EnvGTD`.** -/
def TreeJLive.storeOkTD (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (σ : Type) :
    TreeJLive (EnvGTD I A tid pl D) σ where
  W := StoreOkAtD A tid pl D
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store hok _ := hok
  rmw _ _ := trivial
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- The env state at the first store (`FirstStore.storeOk` for
`StoreOkAtD`): its location is not `x`. -/
theorem FirstStore.storeOkD {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser}
    {P : StoreKind → Bool → Loc → Val → Prop} {Φ : State I → Prop} (hΦ : ∀ s k, Φ s → Φ (fenceState s k))
    {σ : Type} :
    ∀ (tree : EvTree σ) (s : State I), FirstStore P tree → StoreOkAtD A tid pl D tree s → Φ s →
      ∃ s' k xcl l v, P k xcl l v ∧ StoreOk A tid pl s' k xcl l v ∧ l ≠ D.x ∧ Φ s'
  | .fence k ret, s, h, hs, hp => FirstStore.storeOkD hΦ (ret ()) (fenceState s k) h hs (hΦ s k hp)
  | .store k xcl l v _, s, h, hs, hp => ⟨s, k, xcl, l, v, h, hs.1, hs.2, hp⟩
  | .done _, _, h, _, _ => h.elim
  | .fault _, _, h, _, _ => h.elim
  | .choose _ _, _, h, _, _ => h.elim
  | .load .., _, h, _, _ => h.elim
  | .rmw .., _, h, _, _ => h.elim

/-! ## The rule link -/

/-- **The hypotheses of the ticket rule link**: `LinkHypsT` for the
judgments of `EnvGTD`. -/
structure LinkHypsTD (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1Shape A tree
  link : ∀ (J : TreeJLive (EnvGTD I A tid pl D) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- **The invariant of the ticket rule link**: `InvG` and the `coh x`
transfer `OwnX` (the env's `coh x = 0` gives the thread's). -/
def InvGTD (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (Q : I.State → State I → Prop) (cl : Prop)
    (c : Config I) (r : Res) (g : Ghost) : Prop :=
  ∃ σ t, CoreAt A tid pl cl c r g σ t ∧ Q t.st σ ∧ (σ.vs.getCoh D.x = 0 → t.views.getCoh D.x = 0)

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {Q : I.State → State I → Prop}

/-- The thread's views are kept along environment extension. -/
theorem envExt_views {c₀ c : Config I} {t₀ t : Thread I} (he : EnvExt tid c₀ c) (ht₀ : c₀.threads[tid]? = some t₀)
    (ht : c.threads[tid]? = some t) : t.views = t₀.views := by
  obtain ⟨ps, ht', -⟩ := he.2.2 t₀ ht₀
  rw [ht] at ht'
  cases ht'
  rfl

/-- **`wp` of the ticket rule link**: link theorem 1 for `EnvGTD` into
`WpPostRX D.TX` (`InvG.wpT` with `TX` and `OwnX`). -/
theorem InvGTD.wp (H : LinkHypsTD A tid pl D Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvGTD A tid pl D Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hX : D.TX g c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRDS A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t g
      (WpPostRX D.TX (InvGTD A tid pl D Q) (cl ∧ (Erase (setRes rF tid r) g (fun _ => False) c ∧ D.TX g c)) c tid
        r g t) r g (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀, hown₀⟩ := h
  have hv := envExt_views he hC₀.rel.ht ht
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  have hown : σ.vs.getCoh D.x = 0 → t.views.getCoh D.x = 0 := fun h0 => hv ▸ hown₀ h0
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hW := H.link (TreeJLive.eraseWPRDST (nodeSimTD (A := A) (pl := pl) (iv := instrViews t (I.deps t.st))
    (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS hX) Q) t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envGTD_eraseWPRDS_start hC.rel (I.deps t.st) hS hX hown E hm hW ha
  refine EvTree.EraseWPRDS.mono ?_ tree _ _ _ hwp
  rintro st r' g' cx' ⟨σ', hQ', ⟨hP, ⟨hg', hkeep, hnew, hacq, hown'⟩, hlast, hpd, hcl⟩, hX', hco⟩
  refine ⟨⟨hg', hkeep, hnew, hacq, hown', fun t' ht' _ => ?_⟩, fun t' _ _ =>
    Dispenser.TX.congr hX' rfl (by simp only [Config.withThread_size])⟩
  obtain ⟨cxe, hcx, -⟩ := hP.ctx
  have hE := hP.finish (pl := pl) ht hcx.sim.bnd hcx.sim.ivb (hC.rel.bnd.regs.mono hlast) ht'
  have hcl' : (cl ∧ (Erase (setRes rF tid r) g (fun _ => False) c ∧ D.TX g c)) → σ'.cl := by
    cases pf with
    | none => exact fun ⟨h1, h2, _⟩ => hP.cl ⟨h1, rF, (hr rfl) ▸ h2⟩
    | some _ => exact fun ⟨h1, _⟩ => hcl (by simp) h1
  have hprom' : t'.prom = cx'.prom := (finishInstr_relKey ht').1
  have hcoh : t'.views.getCoh D.x = cx'.views.getCoh D.x := by
    have := congrArg (fun v : Views => v.getCoh D.x) (finishInstr_relKey ht').2
    exact this
  refine ⟨σ', t', ⟨{ hE with cl := hcl' }, fun ts hts => ?_, fun ts _ _ hts hpd' _ => ?_⟩, ?_,
    fun h0 => hcoh.trans (hco h0)⟩
  · have := E.pend_le (hnew ts hts)
    show ts ≤ cx'.mem.last
    omega_t
  · exact absurd hpd' (hpd ts (hprom' ▸ hts))
  · rw [finishInstr_st ht']; exact hQ'

/-- **`prepay` of the ticket rule link** (`InvG.prepayT` with the `EnvGTD`
judgment `TreeJLive.storeOkTD`, `prepayGenericTD` and `TX`; an
instance of `CoreAt.prepay_of_firstStoreGX` with `Ex = (· ≠ D.x)`,
`Y = TX`). -/
theorem InvGTD.prepay (H : LinkHypsTD A tid pl D Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvGTD A tid pl D Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hX : D.TX g c) (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧
      D.TX g' (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvGTD A tid pl D Q (cl ∧ (Erase (setRes rF tid r) g (fun _ => False) c ∧ D.TX g c)) (PromisedBy c tid t₁ w)
        r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨σ, t₀, hC₀, hQ₀, hown₀⟩ := h
  have hv := envExt_views he hC₀.rel.ht ht
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t₁.st σ := hst ▸ hQ₀
  obtain ⟨tree, hex, hrfl⟩ := hrel
  have hsh := H.shape _ _ hQ tree hex
  have hFS := relFulfilsLive_firstStore (List.mem_append_right _ (List.mem_singleton_self _))
    (Memory.get?_append_last _ _) tree _ rfl rfl hsh hrfl
  -- the env state at the store, and its permission
  have hJ : StoreOkAtD A tid pl D tree σ :=
    H.link (TreeJLive.storeOkTD A tid pl D I.State) t₁.st σ tree hQ hex (fun _ _ _ => trivial)
  obtain ⟨σ', k, xcl, l, v, hP, hok, hlx, hΦ⟩ :=
    FirstStore.storeOkD (Φ := fun s => s.r = σ.r ∧ s.g = σ.g ∧ s.snap = σ.snap ∧ WBnd s.vs c.mem.last ∧ s.cl = σ.cl)
      (fun s k ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4.fence k, h5⟩) tree σ hFS hJ
      ⟨rfl, rfl, rfl, WBnd.of_viewsLe hC.rel.views, rfl⟩
  obtain ⟨r', g', E', hX', hgle, hpend, hkeep, hnew, hCo, hacq, hK2, hK1⟩ :=
    hC.prepay_of_firstStoreGX (Ex := (· ≠ D.x)) (Y := D.TX) H.valid rF w And.left ht E hm tree hex hsh hFS
      ⟨σ', k, xcl, l, v, hP, hok, hlx, hΦ⟩
      (fun σ' k l v hok hlx hanc E0 hwb => by
        obtain ⟨r', g', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
          prepayGenericTD (D := D) tid pl σ' k l v c g rF t₁ H.valid hok hanc ht E0 hwb hX hlx
        exact ⟨r', g', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩)
  exact ⟨r', g', E', hX', hgle, hpend, hkeep, hnew, ⟨σ, _, hCo, hQ, fun h0 => hv ▸ hown₀ h0⟩, hacq, hK2, hK1⟩

end Rule

/-- **The ticket rule link**: a `ThreadRuleRXGSXE G₀ D.TX` from a
thread-local invariant `Q` of `EnvGTD` (`LinkHypsTD`) and the postcondition
at halted threads (`hB`). -/
def ThreadRuleRXGSXE.ofEnvGTD {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {Q : I.State → State I → Prop}
    {B : Config I → (modelX I D.TX).R → (modelX I D.TX).Ghost → Prop} (H : LinkHypsTD A tid pl D Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGSXE G₀ D.TX A B tid where
  Inv := InvGTD A tid pl D Q
  done h he hg hcl hd := by
    obtain ⟨σ, t₀, hC, hQ, -⟩ := h
    exact InvG.done hB ⟨σ, t₀, hC, hQ⟩ he hg hcl hd
  wp rF t tree h he hg ht hex E hX hm _ hnp := InvGTD.wp H rF t tree h he hg ht hex E hX hm hnp
  prepay rF t₁ w h he hg ht E hX hm hnp hrel := InvGTD.prepay H rF t₁ w h he hg ht E hX hm hnp hrel

/-- **`NPSafeP` over `Erase ∧ TX` with option (S)'s frame from the ticket
rule link** (`NPSafeP.of_ruleRXGSXE`); its Theorem 1′ is
`theorem1IIPureX_G₀_S` with `tx_promiseLaw`. -/
theorem npSafeP_of_envGTD {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {Q : I.State → State I → Prop}
    {B : Config I → (modelX I D.TX).R → (modelX I D.TX).Ghost → Prop} (H : LinkHypsTD A tid pl D Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvGTD A tid pl D Q cl c r g) :
    NPSafeP (modelX I D.TX) A B tid G₀ (K2Scope (model I) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGSXE (ThreadRuleRXGSXE.ofEnvGTD H hB) n m cl c r g h

/-! ## No fault -/

/-- **A no-fault rule over `Erase ∧ X` with `X` at instruction boundaries**
(`NoFaultRuleS` for `ThreadRuleRXGSXE`), same field. -/
structure _root_.Kraken.Promising.SLR.NoFaultRuleSXE {G : PrepayGuard I} {X : Ghost → Config I → Prop} {A : Arch}
    {B : Config I → (modelX I X).R → (modelX I X).Ghost → Prop} {tid : Nat} (R : ThreadRuleRXGSXE G X A B tid) :
    Prop where
  noFault : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), R.Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.NoFaultRun A tid (instrViews t (I.deps t.st)) (ctx₀ t tid c.mem)

/-- `NoFaultRuleSXE` from fault-free trees (`NoFaultRuleS.ofNoFault`). -/
theorem _root_.Kraken.Promising.SLR.NoFaultRuleSXE.ofNoFault {G : PrepayGuard I} {X : Ghost → Config I → Prop}
    {A : Arch} {B : Config I → (modelX I X).R → (modelX I X).Ghost → Prop} {tid : Nat}
    {R : ThreadRuleRXGSXE G X A B tid}
    (h : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
      (tree : EvTree I.State), R.Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
      c.threads[tid]? = some t → I.exec t.st = some tree →
      Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
      (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) → tree.NoFault) :
    NoFaultRuleSXE R :=
  ⟨fun rF t tree hI he hg ht hex E hinv hwf hnp =>
    (h rF t tree hI he hg ht hex E hinv hwf hnp).run A tid _ _⟩

/-- `Q` at the current thread state from `InvGTD` (`InvG.q_at`). -/
theorem InvGTD.q_at {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {Q : I.State → State I → Prop} {cl : Prop}
    {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (h : InvGTD A tid pl D Q cl c₀ r g₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    ∃ σ, Q t.st σ := by
  obtain ⟨σ, t₀, hC₀, hQ₀, -⟩ := h
  obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
  exact ⟨σ, hst ▸ hQ₀⟩

#print axioms prepayGenericTD
#print axioms ThreadRuleRXGSXE.ofEnvGTD
#print axioms npSafeP_of_envGTD

end Kraken.Promising.SLR.EnvG
