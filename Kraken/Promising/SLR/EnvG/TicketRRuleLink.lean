/-
**Item 1, part 3: the ticket rule link with a
release-kind ticket RMW.** ISA-neutral. Adapted from
`EnvG/TicketRuleLink.lean` (`InvGTD`) and `EnvG/RuleLink.lean` § release-kind RMWs
(`InvGR.prepay_of_okAt`); nothing else changes.

`LinkHypsTDR` is `LinkHypsTD` with `Phase1ShapeR` trees and the judgments of
`EnvGTDR` (`EnvG/TicketREnv.lean`). The invariant `InvGTDR` is `InvGTD` with
the core `CoreAtR` (the in-flight instruction may be the ticket RMW).

- `wp` (`InvGTDR.wp`): link theorem 1 for `EnvGTDR`
  (`treeJ_envGTDR_eraseWPRDS_start`, `EnvG/TicketRLink.lean`).
- `prepay` (`InvGTDR.prepay`): the live fulfilment is the tree's first access
  (`relFulfilsLive_firstAccessA`, `relFulfilsLive_firstAccess` with the
  fulfilling write's atomicity). A store (to a location other than `x`) is
  prepaid by `prepayGenericTD`. The ticket RMW (on `x`, whose writes the plan
  never releases) is prepaid as a pure write (`prepayGenericRmwTDR`, by
  `prepayGenericG`); `TX` after the promise needs the promised message to be
  `XFresh`, which the live fulfilment gives: the fulfilling RMW reads `(x,
  tr)` atomically up to the promise (`atomic_of_append`), the thread has no
  other message to `x` (its `coh x` is `0`, so each would be an outstanding
  promise, and the fulfilment leaves every other own promise to `x` above the
  new one, `AboveAt`), so `CountInv.xFresh_of_atomic` applies.
- `ThreadRuleRXGSXE.ofEnvGTDR : ThreadRuleRXGSXE G₀ D.TX A B tid`,
  `npSafeP_of_envGTDR` (by `NPSafeP.of_ruleRXGSXE`, Theorem 1′ is
  `theorem1IIPureX_G₀_S`), `InvGTDR.q_at`.

Phase-1 limits: single-access trees (`Phase1ShapeR`); an in-flight release
RMW never fails; only non-forwarded acquire loads take. No `RelRmwGiveOk` is
needed: the only RMW is the ticket RMW, whose writes are never planned
releases.
-/
import Kraken.Promising.SLR.EnvG.TicketRLink
import Kraken.Promising.SLR.EnvG.FulfilAtomic
import Kraken.Promising.SLR.EnvG.TicketRuleLink
import Kraken.Promising.SLR.EnvG.RuleLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Atomicity of the live fulfilment

`atomic_of_append` and `fulfil_write_atomicTR` are in `EnvG/FulfilAtomic.lean`
(same names and statements). -/

/-- **`relFulfilsLive_firstAccess` with the fulfilling RMW's atomicity**: as
`relFulfilsLive_firstAccess`, and the read of the fulfilling path precedes
`ts` and passes the atomicity check up to `ts`. -/
theorem relFulfilsLive_firstAccessA {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {prom : List Time}
    {mem : Memory} {w : Msg} (hts : ts ∈ prom) (hget : mem.get? ts = some w) {σ : Type} :
    ∀ (tree : EvTree σ) (cx : Ctx), cx.prom = prom → cx.mem = mem → Phase1ShapeR A tree →
      tree.RelFulfilsLive A tid iv ts cx →
      FirstAccess (fun _ _ l v => l = w.loc ∧ v = w.val ∧ AboveAt prom mem ts l)
        (fun cxN k noRet l op => l = w.loc ∧ effRelRmw A k ∧ (∀ x, op x ≠ none) ∧ AboveAt prom mem ts l ∧
          ∃ x ∈ readSuccs A iv (fenceOptCtx A cxN) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
            op x.2.1 = some w.val ∧ x.1 < ts ∧ mem.atomic l tid x.1 ts = true) cx tree
  | .done _, _, _, _, _, h => h
  | .fault _, _, _, _, _, h => h
  | .choose _ k, cx, _, _, hs, ⟨i, h⟩ => AccessFree.not_relFulfilsLive (k i) cx (hs.1 i) h
  | .fence k ret, cx, hp, hm, hs, h =>
    relFulfilsLive_firstAccessA hts hget (ret ()) (fenceStep cx k) (by rw [fenceStep_prom]; exact hp)
      (by rw [fenceStep_mem]; exact hm) hs h
  | .load _ _ _ ret, _, _, _, hs, ⟨x, _, h⟩ => AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h
  | .rmw k noRet l op ret, cx, hp, hm, hs, ⟨x, hx, h⟩ => by
    rcases h with h | ⟨new, hop, c', hc', h⟩
    · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h).elim
    · rcases h with ⟨⟨hk, htc, htc'⟩, hnd⟩ | h
      · obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
        obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
        have hmx : x.2.2.mem = mem := hm1.trans (hm0.trans hm)
        obtain ⟨hl, hv, hab⟩ := fulfil_write_facts hts hget (hp1.trans (hp0.trans hp)) hmx hc' htc htc' hnd
        subst hv
        obtain ⟨htr, hat⟩ := fulfil_write_atomicTR hc' htc htc'
          (by rw [hmx]; exact mem.last_le_of_get?_eq_some hget)
        rw [hmx] at hat
        exact ⟨hl, hk, hs.2.1 hk, hab, x, hx, hop, htr, hat⟩
      · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h).elim
  | .store k xcl l v ret, cx, hp, hm, hs, h => by
    rcases h with ⟨c', hc', ⟨⟨-, htc, htc'⟩, hnd⟩ | h⟩ | h
    · exact fulfil_write_facts hts hget hp hm hc' htc htc' hnd
    · exact (AccessFree.not_relFulfilsLive (ret true) _ (hs.2.2 true) h).elim
    · exact (AccessFree.not_relFulfilsLive (ret false) _ (hs.2.2 false) h).elim

/-! ## The prepay of the ticket RMW -/

/-- **The prepay of the ticket RMW, keeping `TX`**: an RMW on `l` whose
written value the plan does not release is prepaid as a pure write
(`prepayGenericG` with the store permission read off `RmwOk`), and an
`XFresh` promised message keeps `TX` (`TicketInv.grow`, `CountInv.append`). -/
theorem prepayGenericRmwTDR {A : Arch} {D : Dispenser} (tid : Nat) (pl : Plan) (σ : State I) (k : RmwKind) (l : Loc)
    (op : Val → Option Val) (c : Config I) (g : Ghost) (rF : Nat → Res) (t₁ : Thread I) (tr : Time) (old new : Val)
    (hv : pl.Valid) (hok : RmwOk A tid pl σ k l op) (hanc : AnchorOk tid σ c g) (ht : c.threads[tid]? = some t₁)
    (E : Erase (setRes rF tid σ.r) g (fun _ => True) c)
    (hrd : ReadAt A tid (rmwReadViews A σ.vs) c (A.rmwKind k).loadKind l tr old) (hop : op old = some new)
    (hrl : pl.rel l new = false) (hwb : WriteBound A σ.vs (A.rmwKind k).storeKind l (c.mem.last + 1))
    (hX : D.TX g c) (hf : D.XFresh c.mem ⟨l, new, tid⟩) :
    ∃ (r' : Res) (g' : Ghost),
      Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ ⟨l, new, tid⟩) ∧ g.Le g' ∧
      (c.mem.append ⟨l, new, tid⟩).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append ⟨l, new, tid⟩).2) ∧
      r' = pl.after l new (c.mem.last + 1) σ.cl σ.r ∧
      (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB σ.r g x b) ∧
      D.TX g' (PromisedBy c tid t₁ ⟨l, new, tid⟩) := by
  obtain ⟨-, hpure, -⟩ := hok.2 c g tr old new hanc hrd hop
  have hS : StoreOk A tid pl σ (A.rmwKind k).storeKind false l new :=
    ⟨rfl, hok.1, fun _ => hpure hrl, fun h => absurd (hrl.symm.trans h) Bool.false_ne_true⟩
  obtain ⟨r', ss, E', hle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩ :=
    prepayGenericG (A := A) tid pl σ _ l new c g rF t₁ hv hS hanc ht E hwb
  have hsz := Config.withThread_size c tid { t₁ with prom := t₁.prom ++ [(c.mem.append ⟨l, new, tid⟩).2] }
    (c.mem.append ⟨l, new, tid⟩).1
  have hC : D.CountInv (PromisedBy c tid t₁ ⟨l, new, tid⟩) :=
    hX.2.append (w := ⟨l, new, tid⟩) rfl hf hsz (fun _ => lt_size_of_get? ht)
  exact ⟨r', _, E', hle, hpend, hkeep, hnew, hr', hacq, hK2, hK1,
    ⟨Dispenser.TicketInv.grow E hX.1 (Memory.Prefix.append _ _) hC.monoX rfl rfl rfl
      (fun s hs => List.mem_append_left _ hs), hC⟩⟩

/-! ## The first access's permission in `EnvGTDR` -/

/-- `RmwOkTDR` at the first RMW reached by fences, which is live
(`RmwOkAt` for `EnvGTDR`). -/
def RmwOkAtDR (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) {σ : Type} : EvTree σ → State I → Prop
  | .fence k ret, s => RmwOkAtDR A tid pl D (ret ()) (fenceState s k)
  | .rmw k noRet l op _, s => noRet = false ∧ RmwOkTDR A tid pl D s k l op
  | _, _ => True

/-- **`RmwOkAtDR` is a live tree judgment of `EnvGTDR`.** -/
def TreeJLive.rmwOkTDR (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (σ : Type) :
    TreeJLive (EnvGTDR I A tid pl D) σ where
  W := RmwOkAtDR A tid pl D
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store _ _ := trivial
  rmw hok _ := ⟨rfl, hok⟩
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- **`StoreOkAtD` is a live tree judgment of `EnvGTDR`** (`EnvGTDR` agrees
with `EnvGTD` on stores). -/
def TreeJLive.storeOkTDR (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (σ : Type) :
    TreeJLive (EnvGTDR I A tid pl D) σ where
  W := StoreOkAtD A tid pl D
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store hok _ := hok
  rmw _ _ := trivial
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- **The env state at the first access in `EnvGTDR`** (`FirstAccess.accessOk`
for `StoreOkAtD` / `RmwOkAtDR`). -/
theorem FirstAccess.accessOkDR {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser}
    {S : StoreKind → Bool → Loc → Val → Prop} {R : Ctx → RmwKind → Bool → Loc → (Val → Option Val) → Prop}
    {Φ : State I → Ctx → Prop} (hΦ : ∀ s cx k, Φ s cx → Φ (fenceState s k) (fenceStep cx k)) {σ : Type} :
    ∀ (tree : EvTree σ) (s : State I) (cx : Ctx), FirstAccess S R cx tree → StoreOkAtD A tid pl D tree s →
      RmwOkAtDR A tid pl D tree s → Φ s cx →
      (∃ s' cx' k xcl l v, S k xcl l v ∧ StoreOk A tid pl s' k xcl l v ∧ l ≠ D.x ∧ Φ s' cx') ∨
        (∃ s' cx' k l op, R cx' k false l op ∧ RmwOkTDR A tid pl D s' k l op ∧ Φ s' cx')
  | .fence k ret, s, cx, h, hs, hr, hp =>
    FirstAccess.accessOkDR hΦ (ret ()) (fenceState s k) (fenceStep cx k) h hs hr (hΦ s cx k hp)
  | .store k xcl l v _, s, cx, h, hs, _, hp => .inl ⟨s, cx, k, xcl, l, v, h, hs.1, hs.2, hp⟩
  | .rmw k noRet l op _, s, cx, h, _, ⟨hn, hr⟩, hp => by
    subst hn; exact .inr ⟨s, cx, k, l, op, h, hr, hp⟩
  | .done _, _, _, h, _, _, _ => h.elim
  | .fault _, _, _, h, _, _, _ => h.elim
  | .choose _ _, _, _, h, _, _, _ => h.elim
  | .load .., _, _, h, _, _, _ => h.elim

/-! ## The rule link -/

/-- **The hypotheses of the ticket rule link with a release-kind ticket
RMW**: `LinkHypsTD` with `Phase1ShapeR` trees and the judgments of
`EnvGTDR`. -/
structure LinkHypsTDR (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeR A tree
  link : ∀ (J : TreeJLive (EnvGTDR I A tid pl D) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- **The invariant of the ticket rule link with a release-kind ticket RMW**:
`InvGTD` with the core `CoreAtR`. -/
def InvGTDR (tid : Nat) (pl : Plan) (D : Dispenser) (Q : I.State → State I → Prop) (cl : Prop) (c : Config I)
    (r : Res) (g : Ghost) : Prop :=
  ∃ σ t, CoreAtR tid pl cl c r g σ t ∧ Q t.st σ ∧ (σ.vs.getCoh D.x = 0 → t.views.getCoh D.x = 0)

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {Q : I.State → State I → Prop}

/-- **`wp` of the ticket rule link with a release-kind ticket RMW**: link
theorem 1 for `EnvGTDR` into `WpPostRX D.TX` (`InvGTD.wp` with `CoreAtR`). -/
theorem InvGTDR.wp (H : LinkHypsTDR A tid pl D Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvGTDR tid pl D Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hX : D.TX g c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRDS A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t g
      (WpPostRX D.TX (InvGTDR tid pl D Q) (cl ∧ (Erase (setRes rF tid r) g (fun _ => False) c ∧ D.TX g c)) c tid
        r g t) r g (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀, hown₀⟩ := h
  have hv := envExt_views he hC₀.rel.ht ht
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  have hown : σ.vs.getCoh D.x = 0 → t.views.getCoh D.x = 0 := fun h0 => hv ▸ hown₀ h0
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start (A := A)
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hW := H.link (TreeJLive.eraseWPRDST2 (nodeSimTDR (A := A) (pl := pl) (iv := instrViews t (I.deps t.st))
    (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS hX) Q) t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envGTDR_eraseWPRDS_start hC.rel (I.deps t.st) hS hX hown E hm hW ha
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

/-- **`prepay` of the ticket rule link with a release-kind ticket RMW**:
the generic prepay theorem at the in-flight instruction's first access, a
store to another location (`prepayGenericTD`) or the ticket RMW
(`prepayGenericRmwTDR`, its message `XFresh` by the live fulfilment's
atomic read). -/
theorem InvGTDR.prepay (H : LinkHypsTDR A tid pl D Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvGTDR tid pl D Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hX : D.TX g c) (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧
      D.TX g' (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvGTDR tid pl D Q (cl ∧ (Erase (setRes rF tid r) g (fun _ => False) c ∧ D.TX g c)) (PromisedBy c tid t₁ w)
        r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨σ, t₀, hC₀, hQ₀, hown₀⟩ := h
  have hv := envExt_views he hC₀.rel.ht ht
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t₁.st σ := hst ▸ hQ₀
  have hown : σ.vs.getCoh D.x = 0 → t₁.views.getCoh D.x = 0 := fun h0 => hv ▸ hown₀ h0
  have hn := lt_size_of_get? ht
  obtain ⟨tree, hex, hrfl⟩ := hrel
  have hsh := H.shape _ _ hQ tree hex
  have hts_eq : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  have hget : (c.mem.append { w with tid }).1.get? (c.mem.append { w with tid }).2 = some { w with tid } :=
    Memory.get?_append_last _ _
  have hFA := relFulfilsLive_firstAccessA (List.mem_append_right _ (List.mem_singleton_self _)) hget tree _ rfl rfl
    hsh hrfl
  -- the tree's single access is the new in-flight release's
  have hSA : SingleAccessS2 (LokS (some (w.loc, w.val))) (SokS (some (w.loc, w.val))) (RokR (some (w.loc, w.val)))
      (LokS (some (w.loc, w.val))) tree :=
    hFA.singleAccessS2 (fun _ _ _ _ ⟨e1, e2, _⟩ => .inr (by rw [e1, e2]))
      (fun _ _ _ _ _ ⟨e1, _, htot, _⟩ => .inr ⟨w.val, by rw [e1], htot⟩) hsh.2.singleAccess
  -- no release is in flight
  obtain ⟨hr, hn0⟩ : r = σ.r ∧ ∀ ts ∈ t₁.prom, ts ∉ g.pend := by
    rcases hC.rel.res with h' | ⟨ts₁, l₁, v₁, h1, h2, h3, -, -⟩
    · exact h'
    · exfalso
      obtain ⟨htree, -, -⟩ := hC.infl ts₁ l₁ v₁ h1 h2 h3
      have habove : AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
          (c.mem.append { w with tid }).2 l₁ := by
        rcases (hFA.and_ok (htree tree hex)).exists with ⟨-, -, l, v, ⟨-, -, hab⟩, hS⟩ |
            ⟨_, _, _, l, _, ⟨-, -, -, hab, -⟩, hR⟩
        · rcases hS with e | e
          · cases e
          · simp only [Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, -⟩ := e
            exact hab
        · rcases hR with e | ⟨_, e, -⟩
          · cases e
          · simp only [Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, -⟩ := e
            exact hab
      have hle := hC.pendLe ts₁ h2
      have hne : ts₁ ≠ (c.mem.append { w with tid }).2 := by rw [hts_eq]; omega_t
      have := habove ts₁ (List.mem_append_left _ h1) hne _
        (by rw [Memory.get?_append_of_le _ _ _ hle]; exact h3) rfl
      rw [hts_eq] at this
      omega_t
  -- the env state at the first access, with the node relation at the unpromised context
  have hJs : StoreOkAtD A tid pl D tree σ :=
    H.link (TreeJLive.storeOkTDR A tid pl D I.State) t₁.st σ tree hQ hex (fun _ _ _ => trivial)
  have hJr : RmwOkAtDR A tid pl D tree σ :=
    H.link (TreeJLive.rmwOkTDR A tid pl D I.State) t₁.st σ tree hQ hex (fun _ _ _ => trivial)
  have hN0 := hC.rel.toNodeRel rF (I.deps t₁.st) E hm
  let Φ : State I → Ctx → Prop := fun s P => WBnd s.vs c.mem.last ∧ s.cl = σ.cl ∧
    s.vs.getCoh D.x = σ.vs.getCoh D.x ∧
    ∃ cxu, NodeRel tid pl (instrViews t₁ (I.deps t₁.st)) rF c t₁ σ.r g cl s r g cxu ∧ P.views = cxu.views ∧
      P.prom = cxu.prom ++ [c.mem.last + 1] ∧ P.mem = (c.mem.append { w with tid }).1
  have hΦ : ∀ s P k, Φ s P → Φ (fenceState s k) (fenceStep P k) := by
    rintro s P k ⟨hb, hcs, hco, cxu, hN, hv, hp, hm'⟩
    exact ⟨hb.fence k, hcs, (fenceViews_getCoh s.vs k D.x).trans hco, _, hN.fence k,
      by rw [fenceStep_views, fenceStep_views, hv], by rw [fenceStep_prom, fenceStep_prom, hp],
      by rw [fenceStep_mem, hm']⟩
  obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, hX', habove, hq⟩ :
      ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
        (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
        (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
        r' = pl.after w.loc w.val (c.mem.last + 1) σ.cl σ.r ∧
        (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
        (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
        (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
          ∀ x, reachB r' g' x b → reachB σ.r g x b) ∧
        D.TX g' (PromisedBy c tid t₁ w) ∧
        AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
          (c.mem.append { w with tid }).2 w.loc ∧ 0 < (σ.r.wr w.loc).q := by
    rcases hFA.accessOkDR hΦ tree σ _ hJs hJr ⟨WBnd.of_viewsLe hC.rel.views, rfl, rfl, _, hN0, rfl, rfl, rfl⟩ with
        ⟨s', -, k, xcl, l, v, ⟨hl, hv, hab⟩, hok, hlx, hwb, hcs, -, cxu, hN, -⟩ |
        ⟨s', P', k, l, op, ⟨hl, -, -, hab, x, hx, hop, htr, hat⟩, hok, hwb, hcs, hco, cxu, hN, hv, hp, hm'⟩
    · obtain rfl : xcl = false := hok.1
      subst hl hv
      have E0 : Erase (setRes rF tid s'.r) g (fun _ => True) c := by rw [hN.rv, ← hr]; exact E
      obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, hX'⟩ :=
        prepayGenericTD (D := D) tid pl s' k _ _ c g rF t₁ H.valid hok hN.anchorOk ht E0 (hwb.writeBound A k _)
          hX hlx
      rw [hN.rv, hcs] at hr'
      rw [hN.rv] at hacq hK1
      exact ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, hX', hab, hN.rv ▸ hok.2.1⟩
    · subst hl
      obtain ⟨hok, hlD, hTO, hrl0, hco0⟩ := hok
      have E0 : Erase (setRes rF tid s'.r) g (fun _ => True) c := by rw [hN.rv, ← hr]; exact E
      have hrd := hN.readAt_promised (w := { w with tid }) hv hp hm' hx
      -- the thread has no message to `x`: each would be an outstanding promise below the new one
      have ht0 : t₁.views.getCoh D.x = 0 := hown (hco.symm.trans hco0)
      have hown' : ∀ ts w', c.mem.get? ts = some w' → w'.loc = D.x → w'.tid ≠ tid := by
        intro ts w' hw' hl' htid
        have htp := own_x_prom hm ht ht0 hw' hl' htid
        have hle := c.mem.last_le_of_get?_eq_some hw'
        have hne : ts ≠ (c.mem.append { w with tid }).2 := by rw [hts_eq]; omega_t
        have := hab ts (List.mem_append_left _ htp) hne w' (by rw [Memory.get?_append_of_le _ _ _ hle]; exact hw')
          (hl'.trans hlD.symm)
        rw [hts_eq] at this
        omega_t
      -- the read is atomic up to the promise, so the promised message is `XFresh`
      have hrdv : c.mem.read? D.x x.1 = some x.2.1 := hlD ▸ hrd.val
      have hat' : c.mem.atomic D.x tid x.1 (c.mem.last + 1) = true :=
        atomic_of_append (w := { w with tid }) (by rw [hts_eq] at htr; omega_t) (hlD ▸ hat)
      have hlt := (hX.2.old_lt hrdv hn fun ts w' _ hw' hl' => hown' ts w' hw' hl').1
      obtain ⟨-, hf⟩ := hX.2.xFresh_of_atomic hrdv hat' hown' hn (hTO.2 _ _ hlt hop)
      have hf' : D.XFresh c.mem ⟨w.loc, w.val, tid⟩ := by rw [hlD]; exact hf
      obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, hX'⟩ :=
        prepayGenericRmwTDR (D := D) tid pl s' k w.loc op c g rF t₁ x.1 x.2.1 w.val H.valid hok hN.anchorOk ht E0
          hrd hop (hlD ▸ hrl0 w.val) (hwb.writeBound A _ _) hX hf'
      rw [hN.rv, hcs] at hr'
      rw [hN.rv] at hacq hK1
      exact ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, hX', hab, hN.rv ▸ hok.1⟩
  rw [← hr] at hacq hK1
  refine ⟨r', g', E', hX', hgle, hpend, hkeep, hnew, ?_, hacq, hK2, hK1⟩
  -- the invariant after the promise: the release is in flight
  have hExt := EnvExt.promise (tid := tid) (w := w) ht
  have ht' : (PromisedBy c tid t₁ w).threads[tid]? =
      some { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] } := by
    rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl]
  have h1 := hC.rel.ext hExt ht' (fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · exact h'
    · rw [List.mem_singleton] at h'
      have := E.pend_le hpd
      rw [h', hts_eq] at this
      omega_t)
  have huniq : ∀ ts ∈ t₁.prom ++ [(c.mem.append { w with tid }).2], ts ∈ g'.pend →
      ts = (c.mem.append { w with tid }).2 := fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · rcases hnew ts hpd with h'' | h''
      · exact absurd h'' (hn0 ts h')
      · exact h''
    · exact List.mem_singleton.mp h'
  refine ⟨σ, { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] },
    ⟨{ h1 with ghost := h1.ghost.trans hgle,
               res := .inr ⟨_, w.loc, w.val, List.mem_append_right _ (List.mem_singleton_self _), hpend, hget,
                 ⟨σ.cl, id, hr'⟩, huniq⟩,
               cl := fun hc => hC.rel.cl hc.1 }, fun ts hpd => ?_, fun ts l' v' hts hpd hget' => ?_⟩, hQ, hown⟩
  · show ts ≤ (c.mem.append { w with tid }).1.last
    rw [Memory.last_append]
    rcases hnew ts hpd with h' | h'
    · have := E.pend_le h'; omega_t
    · rw [h', hts_eq]; exact Nat.le_refl _
  · obtain rfl := huniq ts hts hpd
    have e : (⟨l', v', tid⟩ : Msg) = { w with tid } := Option.some.inj (hget'.symm.trans hget)
    simp only [Msg.mk.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    refine ⟨fun tree' hex' => ?_, habove, ?_⟩
    · rw [show tree' = tree from Option.some.inj (hex'.symm.trans hex)]
      exact hSA
    · rw [hr']; exact pl.after_q_pos H.valid _ _ _ _ _ hq

end Rule

/-- **The ticket rule link with a release-kind ticket RMW**: a
`ThreadRuleRXGSXE G₀ D.TX` from a thread-local invariant `Q` of `EnvGTDR`
(`LinkHypsTDR`) and the postcondition at halted threads (`hB`). -/
def ThreadRuleRXGSXE.ofEnvGTDR {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {Q : I.State → State I → Prop}
    {B : Config I → (modelX I D.TX).R → (modelX I D.TX).Ghost → Prop} (H : LinkHypsTDR A tid pl D Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGSXE G₀ D.TX A B tid where
  Inv := InvGTDR tid pl D Q
  done h he hg hcl hd := by
    obtain ⟨σ, t₀, hC, hQ, -⟩ := h
    exact InvGR.done hB ⟨σ, t₀, hC, hQ⟩ he hg hcl hd
  wp rF t tree h he hg ht hex E hX hm _ hnp := InvGTDR.wp H rF t tree h he hg ht hex E hX hm hnp
  prepay rF t₁ w h he hg ht E hX hm hnp hrel := InvGTDR.prepay H rF t₁ w h he hg ht E hX hm hnp hrel

/-- **`NPSafeP` over `Erase ∧ TX` with option (S)'s frame from the ticket
rule link with a release-kind ticket RMW** (`NPSafeP.of_ruleRXGSXE`). -/
theorem npSafeP_of_envGTDR {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {Q : I.State → State I → Prop}
    {B : Config I → (modelX I D.TX).R → (modelX I D.TX).Ghost → Prop} (H : LinkHypsTDR A tid pl D Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvGTDR tid pl D Q cl c r g) :
    NPSafeP (modelX I D.TX) A B tid G₀ (K2Scope (model I) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGSXE (ThreadRuleRXGSXE.ofEnvGTDR H hB) n m cl c r g h

/-- `Q` at the current thread state from `InvGTDR` (`InvGTD.q_at`). -/
theorem InvGTDR.q_at {tid : Nat} {pl : Plan} {D : Dispenser} {Q : I.State → State I → Prop} {cl : Prop}
    {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (h : InvGTDR tid pl D Q cl c₀ r g₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    ∃ σ, Q t.st σ := by
  obtain ⟨σ, t₀, hC₀, hQ₀, -⟩ := h
  obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
  exact ⟨σ, hst ▸ hQ₀⟩

#print axioms prepayGenericRmwTDR
#print axioms InvGTDR.prepay
#print axioms ThreadRuleRXGSXE.ofEnvGTDR
#print axioms npSafeP_of_envGTDR

end Kraken.Promising.SLR.EnvG
