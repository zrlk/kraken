/-
Whole-thread environment, **Claim-conditional RMWs** part 3: the **rule link** of the
claim-conditional environment `EnvGC` (`EnvG/RmwGhost.lean`,
`EnvG/RmwGhostLink.lean`), additively beside `RuleLink.lean`'s `R` part.
ISA-neutral; nothing imports this file.

`LinkHypsRC` is `LinkHypsR` over `EnvGC` **without** `giveOk`
(`RelRmwGiveOk`): the invariant `InvGR` and the core `CoreAtR` are reused
unchanged (they do not mention the environment). `InvGR.wpC` is `InvGR.wp`
through `treeJ_envGC_eraseWPRDSR_start`; `InvGR.prepayC` is
`InvGR.prepay_of_okAt` with `RmwOkC` at the first access and
`prepayGenericRmwC`. The result `ThreadRuleRX.ofEnvGRC` is an existing
`ThreadRuleRX` (frozen interface), so everything downstream (NPSafe,
`theorem1IIPure'`) applies unchanged.
-/
import Kraken.Promising.SLR.EnvG.RmwGhostLink
import Kraken.Promising.SLR.EnvG.RuleLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## First-access judgments for `EnvGC` -/

/-- `RmwOkAt` for `EnvGC`: the permission `RmwOkC` of the tree's first RMW. -/
def RmwOkAtC (A : Arch) (tid : Nat) (pl : Plan) {σ : Type} : EvTree σ → State I → Prop
  | .fence k ret, s => RmwOkAtC A tid pl (ret ()) (fenceState s k)
  | .rmw k noRet l op _, s => noRet = false ∧ RmwOkC A tid pl s k l op
  | _, _ => True

/-- The judgment yielding `StoreOkAt` (`EnvGC` stores are `EnvG`'s). -/
def TreeJLive.storeOkC (A : Arch) (tid : Nat) (pl : Plan) (σ : Type) : TreeJLive (EnvGC I A tid pl) σ where
  W := StoreOkAt A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store hok _ := hok
  rmw _ _ := trivial
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- The judgment yielding `RmwOkAtC`. -/
def TreeJLive.rmwOkC (A : Arch) (tid : Nat) (pl : Plan) (σ : Type) : TreeJLive (EnvGC I A tid pl) σ where
  W := RmwOkAtC A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store _ _ := trivial
  rmw hok _ := ⟨rfl, hok⟩
  fence _ h := h _ (fenceOut_fenceState _ _)

theorem FirstAccess.accessOkC {A : Arch} {tid : Nat} {pl : Plan} {S : StoreKind → Bool → Loc → Val → Prop}
    {R : Ctx → RmwKind → Bool → Loc → (Val → Option Val) → Prop} {Φ : State I → Ctx → Prop}
    (hΦ : ∀ s cx k, Φ s cx → Φ (fenceState s k) (fenceStep cx k)) {σ : Type} :
    ∀ (tree : EvTree σ) (s : State I) (cx : Ctx), FirstAccess S R cx tree → StoreOkAt A tid pl tree s →
      RmwOkAtC A tid pl tree s → Φ s cx →
      (∃ s' cx' k xcl l v, S k xcl l v ∧ StoreOk A tid pl s' k xcl l v ∧ Φ s' cx') ∨
        (∃ s' cx' k l op, R cx' k false l op ∧ RmwOkC A tid pl s' k l op ∧ Φ s' cx')
  | .fence k ret, s, cx, h, hs, hr, hp =>
    FirstAccess.accessOkC hΦ (ret ()) (fenceState s k) (fenceStep cx k) h hs hr (hΦ s cx k hp)
  | .store k xcl l v _, s, cx, h, hs, _, hp => .inl ⟨s, cx, k, xcl, l, v, h, hs, hp⟩
  | .rmw k noRet l op _, s, cx, h, _, ⟨hn, hr⟩, hp => by
    subst hn; exact .inr ⟨s, cx, k, l, op, h, hr, hp⟩
  | .done _, _, _, h, _, _, _ => h.elim
  | .fault _, _, _, h, _, _, _ => h.elim
  | .choose _ _, _, _, h, _, _, _ => h.elim
  | .load .., _, _, h, _, _, _ => h.elim

/-! ## The rule link -/

/-- **The hypotheses of the rule link of `EnvGC`**: `LinkHypsR` over `EnvGC`,
without the give-away side condition. -/
structure LinkHypsRC (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeR A tree
  link : ∀ (J : TreeJLive (EnvGC I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

section RuleRC

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`wp`** for `EnvGC` (`InvGR.wp` without the give-away side condition). -/
theorem InvGR.wpC (H : LinkHypsRC A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvGR tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvGR tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start (A := A)
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hW := H.link (TreeJLive.eraseWPRDS2 (nodeSimS2_envGC (A := A) (pl := pl)
    (iv := instrViews t (I.deps t.st)) (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS) Q)
    t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envGC_eraseWPRDSR_start hC.rel (I.deps t.st) hS E hm hW ha
  refine EvTree.EraseWPRD.mono ?_ tree _ _ _ hwp
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

/-- **`prepay` for `EnvGC`, from the first-access judgments**: `InvGR.prepay_of_okAt`
with `RmwOkC` at the first access and `prepayGenericRmwC` (no give-away side
condition). -/
theorem InvGR.prepay_of_okAtC (hvalid : pl.Valid)
    (hshape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeR A tree)
    (hok : ∀ st σ tree, Q st σ → I.exec st = some tree → StoreOkAt A tid pl tree σ ∧ RmwOkAtC A tid pl tree σ)
    {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
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
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t₁.st σ := hst ▸ hQ₀
  have hn := lt_size_of_get? ht
  obtain ⟨tree, hex, hrfl⟩ := hrel
  have hsh := hshape _ _ hQ tree hex
  have hts_eq : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  have hget : (c.mem.append { w with tid }).1.get? (c.mem.append { w with tid }).2 = some { w with tid } :=
    Memory.get?_append_last _ _
  have hFA := relFulfilsLive_firstAccess (List.mem_append_right _ (List.mem_singleton_self _)) hget tree _ rfl rfl
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
  obtain ⟨hJs, hJr⟩ := hok t₁.st σ tree hQ hex
  have hN0 := hC.rel.toNodeRel rF (I.deps t₁.st) E hm
  let Φ : State I → Ctx → Prop := fun s P => WBnd s.vs c.mem.last ∧ s.cl = σ.cl ∧
    ∃ cxu, NodeRel tid pl (instrViews t₁ (I.deps t₁.st)) rF c t₁ σ.r g cl s r g cxu ∧ P.views = cxu.views ∧
      P.prom = cxu.prom ++ [c.mem.last + 1] ∧ P.mem = (c.mem.append { w with tid }).1
  have hΦ : ∀ s P k, Φ s P → Φ (fenceState s k) (fenceStep P k) := by
    rintro s P k ⟨hb, hcs, cxu, hN, hv, hp, hm'⟩
    exact ⟨hb.fence k, hcs, _, hN.fence k, by rw [fenceStep_views, fenceStep_views, hv],
      by rw [fenceStep_prom, fenceStep_prom, hp], by rw [fenceStep_mem, hm']⟩
  obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, habove, hq⟩ :
      ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
        (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
        (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
        r' = pl.after w.loc w.val (c.mem.last + 1) σ.cl σ.r ∧
        (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
        (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
        (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
          ∀ x, reachB r' g' x b → reachB σ.r g x b) ∧
        AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
          (c.mem.append { w with tid }).2 w.loc ∧ 0 < (σ.r.wr w.loc).q := by
    rcases hFA.accessOkC hΦ tree σ _ hJs hJr ⟨WBnd.of_viewsLe hC.rel.views, rfl, _, hN0, rfl, rfl, rfl⟩ with
        ⟨s', -, k, xcl, l, v, ⟨hl, hv, hab⟩, hok, hwb, hcs, cxu, hN, -⟩ |
        ⟨s', P', k, l, op, ⟨hl, -, -, hab, x, hx, hop⟩, hok, hwb, hcs, cxu, hN, hv, hp, hm'⟩
    · obtain rfl : xcl = false := hok.1
      subst hl hv
      have E0 : Erase (setRes rF tid s'.r) g (fun _ => True) c := by rw [hN.rv, ← hr]; exact E
      obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩ :=
        prepayGeneric tid pl s' k _ _ c g rF t₁ hvalid hok hN.anchorOk ht E0 (hwb.writeBound A k _)
      rw [hN.rv, hcs] at hr'
      rw [hN.rv] at hacq hK1
      exact ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, hab, hN.rv ▸ hok.2.1⟩
    · subst hl
      have E0 : Erase (setRes rF tid s'.r) g (fun _ => True) c := by rw [hN.rv, ← hr]; exact E
      have hrd := hN.readAt_promised (w := { w with tid }) hv hp hm' hx
      obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩ :=
        prepayGenericRmwC tid pl s' _ _ _ c g rF t₁ _ _ _ hvalid hok hN.anchorOk ht E0 hrd hop (hwb.writeBound A _ _)
      rw [hN.rv, hcs] at hr'
      rw [hN.rv] at hacq hK1
      exact ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, hab, hN.rv ▸ hok.1⟩
  rw [← hr] at hacq hK1
  refine ⟨r', g', E', hgle, hpend, hkeep, hnew, ?_, hacq, hK2, hK1⟩
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
               cl := fun hc => hC.rel.cl hc.1 }, fun ts hpd => ?_, fun ts l' v' hts hpd hget' => ?_⟩, hQ⟩
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
    · rw [hr']; exact pl.after_q_pos hvalid _ _ _ _ _ hq

/-- **`prepay`** for `EnvGC`. -/
theorem InvGR.prepayC (H : LinkHypsRC A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
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
      ⟨H.link (TreeJLive.storeOkC A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial),
        H.link (TreeJLive.rmwOkC A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial)⟩)
    rF t₁ w h he hg ht E hm hnp hrel

end RuleRC

/-- **The rule link of `EnvGC`**: a `ThreadRuleRX` from a
thread-local invariant `Q` of `EnvG` (`LinkHypsR`) and the postcondition at
halted threads (`hB`). -/
def ThreadRuleRX.ofEnvGRC {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsRC A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid where
  Inv := InvGR tid pl Q
  done h he hg hcl hd := InvGR.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvGR.wpC H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvGR.prepayC H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafe` from the rule link of `EnvGC`**
(`NPSafe.of_ruleRX`). -/
theorem npSafe_of_envGRC {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsRC A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvGR tid pl Q cl c r g) :
    NPSafe (model I) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofEnvGRC H hB) n m cl c r g h

end Kraken.Promising.SLR.EnvG
