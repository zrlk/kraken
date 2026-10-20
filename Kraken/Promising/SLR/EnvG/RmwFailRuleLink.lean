/-
The failing-RMW route, part 3: **the rule link with failing
in-flight release RMWs**. ISA-neutral. Copies of the release-RMW rule
link (`EnvG/Phase1.lean` § release-kind RMWs, `EnvG/RuleLink.lean` § release-kind RMWs) with the
totality condition dropped (option (A)-style additive duplication).

- `Phase1ShapeF`: `Phase1ShapeR` without "a release-kind RMW's operation never
  fails": deterministic, at most one access, RMWs of any kind and operation
  (so `casal` and x64 `lock cmpxchg`).
- `relFulfilsLive_firstAccessF`, `InflFactF`/`CoreAtF` (in-flight tree side
  condition `RokF`), `LinkHypsF`, `InvGF`: the `R` versions without totality.
- `InvGF.wp`: `treeJ_envG_eraseWPRDSF_start`; a leaf with the in-flight escape
  (`Alive`: the in-flight RMW failed) goes to `WpPostRF`'s left disjunct.
- `InvGF.prepay`: unchanged proof (`prepayGenericRmw'_of_giveOk` takes the
  read of the fulfilling path, `op old = some new`; it never used totality).
- `ThreadRuleRXF.ofEnvGF`, `npSafeF_of_envGF`: the rule, giving `NPSafeF`
  (Theorem 1′ for it is the open `Theorem1FChain`, `EnvG/RmwFailRule.lean`).
-/
import Kraken.Promising.SLR.EnvG.RmwFailLink
import Kraken.Promising.SLR.EnvG.RmwFailRule
import Kraken.Promising.SLR.EnvG.RuleLink
import Kraken.Promising.SLR.EnvG.TreeMap

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The phase-1 shape with failing release RMWs -/

/-- **The phase-1 tree shape with failing release RMWs**: deterministic
access, at most one access, RMWs of any kind and operation. -/
def Phase1ShapeF {σ : Type} (tree : EvTree σ) : Prop :=
  DetAccess tree ∧ SingleAccessS2 True (fun _ _ => True) (fun _ _ _ => True) True tree

/-- An `R` phase-1 tree is an `F` phase-1 tree. -/
theorem Phase1ShapeR.toF {A : Arch} {σ : Type} {tree : EvTree σ} (h : Phase1ShapeR A tree) : Phase1ShapeF tree :=
  ⟨h.1, SingleAccessS2.mono id (fun _ _ h => h) (fun _ _ _ _ => trivial) id h.2⟩

/-- `F` phase-1 trees satisfy the `F` link's side conditions without a
release in flight. -/
theorem Phase1ShapeF.none {σ : Type} {tree : EvTree σ} (h : Phase1ShapeF tree) :
    SingleAccessS2 (LokS none) (SokS none) (RokF none) (LokS none) tree :=
  SingleAccessS2.mono (fun _ => rfl) (fun _ _ _ => .inl rfl) (fun _ _ _ _ => .inl rfl) (fun _ => rfl) h.2

/-- **The live fulfilment of a promise by a phase-1 tree with release-kind
RMWs is its first access**: a store of the promised message, or a
release-kind RMW (possibly failing on other reads) of the promised location whose read (in the
context it is reached in) gives the promised value; either leaves every other
own promise to the location above the fulfilled one. -/
theorem relFulfilsLive_firstAccessF {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {prom : List Time}
    {mem : Memory} {w : Msg} (hts : ts ∈ prom) (hget : mem.get? ts = some w) {σ : Type} :
    ∀ (tree : EvTree σ) (cx : Ctx), cx.prom = prom → cx.mem = mem → Phase1ShapeF tree →
      tree.RelFulfilsLive A tid iv ts cx →
      FirstAccess (fun _ _ l v => l = w.loc ∧ v = w.val ∧ AboveAt prom mem ts l)
        (fun cxN k noRet l op => l = w.loc ∧ effRelRmw A k ∧ AboveAt prom mem ts l ∧
          ∃ x ∈ readSuccs A iv (fenceOptCtx A cxN) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
            op x.2.1 = some w.val) cx tree
  | .done _, _, _, _, _, h => h
  | .fault _, _, _, _, _, h => h
  | .choose _ k, cx, _, _, hs, ⟨i, h⟩ => AccessFree.not_relFulfilsLive (k i) cx (hs.1 i) h
  | .fence k ret, cx, hp, hm, hs, h =>
    relFulfilsLive_firstAccessF hts hget (ret ()) (fenceStep cx k) (by rw [fenceStep_prom]; exact hp)
      (by rw [fenceStep_mem]; exact hm) hs h
  | .load _ _ _ ret, _, _, _, hs, ⟨x, _, h⟩ => AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h
  | .rmw k noRet l op ret, cx, hp, hm, hs, ⟨x, hx, h⟩ => by
    rcases h with h | ⟨new, hop, c', hc', h⟩
    · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h).elim
    · rcases h with ⟨⟨hk, htc, htc'⟩, hnd⟩ | h
      · obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
        obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
        obtain ⟨hl, hv, hab⟩ := fulfil_write_facts hts hget (hp1.trans (hp0.trans hp)) (hm1.trans (hm0.trans hm))
          hc' htc htc' hnd
        subst hv
        exact ⟨hl, hk, hab, x, hx, hop⟩
      · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h).elim
  | .store k xcl l v ret, cx, hp, hm, hs, h => by
    rcases h with ⟨c', hc', ⟨⟨-, htc, htc'⟩, hnd⟩ | h⟩ | h
    · exact fulfil_write_facts hts hget hp hm hc' htc htc' hnd
    · exact (AccessFree.not_relFulfilsLive (ret true) _ (hs.2.2 true) h).elim
    · exact (AccessFree.not_relFulfilsLive (ret false) _ (hs.2.2 false) h).elim

/-! ## The invariant core -/

/-- **The in-flight facts with failing release RMWs** of the pending own promise
`ts` of `⟨l, v⟩` (`InflFact` with `SingleAccessS2`/`RokF`). -/
def InflFactF (c : Config I) (t : Thread I) (r : Res) (l : Loc) (v : Val) (ts : Time) : Prop :=
  (∀ tree, I.exec t.st = some tree →
      SingleAccessS2 (LokS (some (l, v))) (SokS (some (l, v))) (RokF (some (l, v))) (LokS (some (l, v))) tree) ∧
    (∀ p ∈ t.prom, p ≠ ts → ∀ w, c.mem.get? p = some w → w.loc = l → ts < p) ∧ 0 < (r.wr l).q

/-- **The invariant core with failing release RMWs** (`CoreAt` with
`InflFactF`). -/
structure CoreAtF (tid : Nat) (pl : Plan) (cl : Prop) (c : Config I) (r : Res) (g : Ghost) (σ : State I)
    (t : Thread I) : Prop where
  rel : EnvRel tid pl σ c t r g cl
  pendLe : ∀ ts ∈ g.pend, ts ≤ c.mem.last
  infl : ∀ ts l v, ts ∈ t.prom → ts ∈ g.pend → c.mem.get? ts = some ⟨l, v, tid⟩ → InflFactF c t r l v ts

section CoreR

variable {tid : Nat} {pl : Plan} {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} {σ : State I}
  {t₀ t : Thread I}

/-- **The core with failing release RMWs along environment extension and world
growth** (`CoreAt.transport`). -/
theorem CoreAtF.transport (h : CoreAtF tid pl cl c₀ r g₀ σ t₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g)
    (ht : c.threads[tid]? = some t) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) {rF : Nat → Res}
    {T : Nat → Prop} (E : Erase (setRes rF tid r) g T c) :
    t.st = t₀.st ∧ CoreAtF tid pl cl c r g σ t := by
  obtain ⟨hinit, hmsgs, hth⟩ := he
  obtain ⟨ps, ht', hps⟩ := hth t₀ h.rel.ht
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  have hle : c₀.mem.last ≤ c.mem.last := by
    have := hmsgs.length_le
    simp only [Array.length_toList] at this
    unfold Memory.last; omega_t
  have hpre : c₀.mem.Prefix c.mem := ⟨hinit, hmsgs⟩
  have hnp₀ : ∀ ts ∈ t₀.prom ++ ps, ts ∈ g₀.pend → ts ∈ t₀.prom := fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · exact h'
    · have := hps ts h'; have := h.pendLe ts hpd; omega_t
  have h1 := h.rel.ext ⟨hinit, hmsgs, hth⟩ ht hnp₀
  have hinfl : ∀ ts l v, ts ∈ t₀.prom ++ ps → ts ∈ g₀.pend → c.mem.get? ts = some ⟨l, v, tid⟩ →
      InflFactF c { t₀ with prom := t₀.prom ++ ps } r l v ts := by
    intro ts l v hts hpd hget
    have hts₀ := hnp₀ ts hts hpd
    have hle₀ := h.pendLe ts hpd
    obtain ⟨htree, habove, hq⟩ := h.infl ts l v hts₀ hpd (by rw [← hpre.get? hle₀]; exact hget)
    refine ⟨htree, fun p hp hne w hw hwl => ?_, hq⟩
    by_cases hpl : p ≤ c₀.mem.last
    · rcases List.mem_append.mp hp with hp | hp
      · exact habove p hp hne w (by rw [← hpre.get? hpl]; exact hw) hwl
      · have := hps p hp; omega_t
    · omega_t
  have hiff : ∀ ts ∈ t₀.prom ++ ps, (ts ∈ g.pend ↔ ts ∈ g₀.pend) := by
    intro ts hts
    refine ⟨hnp ts hts, fun hpd₀ => ?_⟩
    rcases h1.res with ⟨-, hn⟩ | ⟨ts₁, l, v, h1', -, h3, h5, h6⟩
    · exact absurd hpd₀ (hn ts hts)
    · obtain rfl := h6 ts hts hpd₀
      obtain ⟨-, -, hq⟩ := hinfl ts l v hts hpd₀ h3
      obtain ⟨P, -, h5⟩ := h5
      have hX : (r.wr l).X (v, ts) := by rw [h5] at hq ⊢; exact pl.after_X_self l v ts P σ.r hq
      exact pend_of_written E ht h1' h3 hX hq
  refine ⟨rfl, h1.ghostLe hg hiff, fun ts hts => E.pend_le hts, fun ts l v hts hpd hget => ?_⟩
  exact hinfl ts l v hts ((hiff ts hts).mp hpd) hget

/-- **The `R` link's start from the core** (`CoreAt.start` with
`Phase1ShapeR` and `RokF`). -/
theorem CoreAtF.start (h : CoreAtF tid pl cl c r g σ t) :
    ∃ pf, StartS tid c t g pf ∧
      (∀ tree, I.exec t.st = some tree → Phase1ShapeF tree →
        SingleAccessS2 (LokS pf) (SokS pf) (RokF pf) (LokS pf) tree) ∧ (pf = none → r = σ.r) := by
  rcases h.rel.res with ⟨hr, hn⟩ | ⟨ts, l, v, h1, h2, h3, -, h6⟩
  · exact ⟨none, ⟨fun _ => hn, fun _ _ e => absurd e (by simp)⟩, fun _ _ hs => hs.none, fun _ => hr⟩
  · obtain ⟨htree, habove, -⟩ := h.infl ts l v h1 h2 h3
    refine ⟨some (l, v), ⟨fun e => absurd e (by simp), fun l' v' e => ?_⟩, fun tree hex _ => htree tree hex,
      fun e => absurd e (by simp)⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨ts, h1, h2, h3, habove⟩

end CoreR

/-! ## The rule link -/

/-- **The hypotheses of the rule link with failing release RMWs**: `LinkHyps`
with `Phase1ShapeR` trees and the give-away side condition. -/
structure LinkHypsF (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeF tree
  giveOk : ∀ st σ, Q st σ → RelRmwGiveOk I pl σ.g.rel
  link : ∀ (J : TreeJLive (EnvG I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- The `R` link's hypotheses are the `F` link's. -/
theorem LinkHypsR.toF {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop} (H : LinkHypsR A tid pl Q) :
    LinkHypsF A tid pl Q :=
  ⟨H.valid, fun st σ hQ tree hex => (H.shape st σ hQ tree hex).toF, H.giveOk, H.link⟩

/-- **The rule's invariant with failing release RMWs**: the core `CoreAtF` and
`Q` at some env state. -/
def InvGF (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) (cl : Prop) (c : Config I) (r : Res)
    (g : Ghost) : Prop :=
  ∃ σ t, CoreAtF tid pl cl c r g σ t ∧ Q t.st σ

section RuleR

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`done`** (`InvG.done`). -/
theorem InvGF.done {B : Config I → Res → Ghost → Prop}
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (h : InvGF tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (hcl : cl) (hd : c.Done tid) : B c r g := by
  obtain ⟨σ, t₀, hC, hQ⟩ := h
  obtain ⟨t, ht, hhalt, hprom⟩ := hd
  obtain ⟨hinit, hmsgs, hth⟩ := he
  obtain ⟨ps, ht', -⟩ := hth t₀ hC.rel.ht
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  have h1 := hC.rel.ext ⟨hinit, hmsgs, hth⟩ ht (fun ts hts _ => absurd (hprom ▸ hts) List.not_mem_nil)
  exact hB c { t₀ with prom := t₀.prom ++ ps } r g cl σ hQ hhalt hprom
    (h1.ghostLe hg fun ts hts => absurd (hprom ▸ hts) List.not_mem_nil) hcl

/-- **`wp`** with failing release RMWs (`InvG.wp`). -/
theorem InvGF.wp (H : LinkHypsF A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvGF tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostRF (InvGF tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hG : RelRmwGiveOk I pl g.rel := by rw [hC.rel.ghost.rel]; exact H.giveOk _ _ hQ
  have hW := H.link (TreeJLive.eraseWPRDS2 (nodeSimS2F_envG (A := A) (pl := pl)
    (iv := instrViews t (I.deps t.st)) (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS hG) Q)
    t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envG_eraseWPRDSF_start hC.rel (I.deps t.st) hS hG E hm hW ha
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

/-- **`prepay`** with failing release RMWs: the generic prepay theorem at the
in-flight instruction's first access, a store (`prepayGeneric`) or a
release-kind RMW (`prepayGenericRmw'_of_giveOk`). -/
theorem InvGF.prepay (H : LinkHypsF A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
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
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t₁.st σ := hst ▸ hQ₀
  have hn := lt_size_of_get? ht
  obtain ⟨tree, hex, hrfl⟩ := hrel
  have hsh := H.shape _ _ hQ tree hex
  have hts_eq : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  have hget : (c.mem.append { w with tid }).1.get? (c.mem.append { w with tid }).2 = some { w with tid } :=
    Memory.get?_append_last _ _
  have hFA := relFulfilsLive_firstAccessF (List.mem_append_right _ (List.mem_singleton_self _)) hget tree _ rfl rfl
    hsh hrfl
  -- the tree's single access is the new in-flight release's
  have hSA : SingleAccessS2 (LokS (some (w.loc, w.val))) (SokS (some (w.loc, w.val))) (RokF (some (w.loc, w.val)))
      (LokS (some (w.loc, w.val))) tree :=
    hFA.singleAccessS2 (fun _ _ _ _ ⟨e1, e2, _⟩ => .inr (by rw [e1, e2]))
      (fun _ _ _ _ _ ⟨e1, _⟩ => .inr ⟨w.val, by rw [e1]⟩) hsh.2.singleAccess
  -- no release is in flight
  obtain ⟨hr, hn0⟩ : r = σ.r ∧ ∀ ts ∈ t₁.prom, ts ∉ g.pend := by
    rcases hC.rel.res with h' | ⟨ts₁, l₁, v₁, h1, h2, h3, -, -⟩
    · exact h'
    · exfalso
      obtain ⟨htree, -, -⟩ := hC.infl ts₁ l₁ v₁ h1 h2 h3
      have habove : AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
          (c.mem.append { w with tid }).2 l₁ := by
        rcases (hFA.and_ok (htree tree hex)).exists with ⟨-, -, l, v, ⟨-, -, hab⟩, hS⟩ |
            ⟨_, _, _, l, _, ⟨-, -, hab, -⟩, hR⟩
        · rcases hS with e | e
          · cases e
          · simp only [Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, -⟩ := e
            exact hab
        · rcases hR with e | ⟨_, e⟩
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
  have hJs : StoreOkAt A tid pl tree σ :=
    H.link (TreeJLive.storeOk A tid pl I.State) t₁.st σ tree hQ hex (fun _ _ _ => trivial)
  have hJr : RmwOkAt A tid pl tree σ :=
    H.link (TreeJLive.rmwOk A tid pl I.State) t₁.st σ tree hQ hex (fun _ _ _ => trivial)
  have hN0 := hC.rel.toNodeRel rF (I.deps t₁.st) E hm
  let Φ : State I → Ctx → Prop := fun s P => WBnd s.vs c.mem.last ∧ s.cl = σ.cl ∧
    ∃ cxu, NodeRel tid pl (instrViews t₁ (I.deps t₁.st)) rF c t₁ σ.r g cl s r g cxu ∧ P.views = cxu.views ∧
      P.prom = cxu.prom ++ [c.mem.last + 1] ∧ P.mem = (c.mem.append { w with tid }).1
  have hΦ : ∀ s P k, Φ s P → Φ (fenceState s k) (fenceStep P k) := by
    rintro s P k ⟨hb, hcs, cxu, hN, hv, hp, hm'⟩
    exact ⟨hb.fence k, hcs, _, hN.fence k, by rw [fenceStep_views, fenceStep_views, hv],
      by rw [fenceStep_prom, fenceStep_prom, hp], by rw [fenceStep_mem, hm']⟩
  have hG : RelRmwGiveOk I pl σ.g.rel := H.giveOk _ _ hQ
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
    rcases hFA.accessOk hΦ tree σ _ hJs hJr ⟨WBnd.of_viewsLe hC.rel.views, rfl, _, hN0, rfl, rfl, rfl⟩ with
        ⟨s', -, k, xcl, l, v, ⟨hl, hv, hab⟩, hok, hwb, hcs, cxu, hN, -⟩ |
        ⟨s', P', k, l, op, ⟨hl, -, hab, x, hx, hop⟩, hok, hwb, hcs, cxu, hN, hv, hp, hm'⟩
    · obtain rfl : xcl = false := hok.1
      subst hl hv
      have E0 : Erase (setRes rF tid s'.r) g (fun _ => True) c := by rw [hN.rv, ← hr]; exact E
      obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩ :=
        prepayGeneric tid pl s' k _ _ c g rF t₁ H.valid hok hN.anchorOk ht E0 (hwb.writeBound A k _)
      rw [hN.rv, hcs] at hr'
      rw [hN.rv] at hacq hK1
      exact ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, hab, hN.rv ▸ hok.2.1⟩
    · subst hl
      have E0 : Erase (setRes rF tid s'.r) g (fun _ => True) c := by rw [hN.rv, ← hr]; exact E
      have hrd := hN.readAt_promised (w := { w with tid }) hv hp hm' hx
      have hG' : RelRmwGiveOk I pl s'.g.rel := by rw [← hN.ghost.rel, hC.rel.ghost.rel]; exact hG
      obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩ :=
        prepayGenericRmw'_of_giveOk hG' H.valid hok hN.anchorOk ht E0 hrd hop (hwb.writeBound A _ _)
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
    · rw [hr']; exact pl.after_q_pos H.valid _ _ _ _ _ hq

end RuleR

/-- **The rule link with failing release RMWs**: a `ThreadRuleRX` from a
thread-local invariant `Q` of `EnvG` (`LinkHypsF`) and the postcondition at
halted threads (`hB`). -/
def ThreadRuleRXF.ofEnvGF {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsF A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid where
  Inv := InvGF tid pl Q
  done h he hg hcl hd := InvGF.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvGF.wp H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvGF.prepay H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafeF` from the rule link with failing release RMWs**
(`NPSafeF.of_ruleRXF`). -/
theorem npSafeF_of_envGF {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsF A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvGF tid pl Q cl c r g) :
    NPSafeF (model I) A B tid n m cl c r g :=
  NPSafeF.of_ruleRXF (ThreadRuleRXF.ofEnvGF H hB) n m cl c r g h

/-! ## No-fault for the `F` rule -/

/-- **`NoFaultRule` for a `ThreadRuleRXF`** (`Sim/NoFault.lean`'s
`NoFaultRule`, which only reads the rule's `Inv`). -/
structure NoFaultRuleF {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRXF A B tid) : Prop where
  noFault : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), R.Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.NoFaultRun A tid (instrViews t (I.deps t.st)) (ctx₀ t tid c.mem)

/-- `NoFaultRule.ofNoFault` for the `F` rule. -/
theorem NoFaultRuleF.ofNoFault {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    {R : ThreadRuleRXF A B tid}
    (h : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
      (tree : EvTree I.State), R.Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
      c.threads[tid]? = some t → I.exec t.st = some tree →
      Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
      (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) → tree.NoFault) :
    NoFaultRuleF R :=
  ⟨fun rF t tree hI he hg ht hex E hinv hwf hnp =>
    (h rF t tree hI he hg ht hex E hinv hwf hnp).run A tid _ _⟩

/-- At the `F` rule's invariant, transported, the thread's state is a
`Q`-state (`InvGR.q_at`). -/
theorem InvGF.q_at {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop} {cl : Prop}
    {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (h : InvGF tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    ∃ σ, Q t.st σ := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
  exact ⟨σ, hst ▸ hQ₀⟩

/-- **The no-fault rule for the `F` link from fault-free trees**
(`noFaultRule_ofEnvGR_struct`). -/
theorem noFaultRuleF_ofEnvGF_struct {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsF A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HS : ∀ st σ tree, Q st σ → I.exec st = some tree → tree.NoFault) :
    NoFaultRuleF (ThreadRuleRXF.ofEnvGF H hB) :=
  NoFaultRuleF.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGF.q_at rF t h he hg ht E hnp
    exact HS t.st σ tree hQ hex

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.AArch64.EnvG

open Kraken.Promising.SLR.EnvG

/-- The phase-1 shape with failing release RMWs is stable under `EvTree.map`
(moved from `EnvG/A64RmwFail.lean`; the name stays in
`AArch64.EnvG`, and `X64.EnvG.phase1ShapeF_map` is its alias). -/
theorem phase1ShapeF_map {σ τ : Type} (f : σ → τ) {t : EvTree σ} (h : Phase1ShapeF t) :
    Phase1ShapeF (t.map f) :=
  ⟨detAccess_map f t h.1, singleAccessS2_map f t h.2⟩

end Kraken.Promising.AArch64.EnvG
