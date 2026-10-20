/-
**Layer L, part 3: the ticket link.** ISA-neutral.
Adapted from `EnvG/LinkS.lean` and `EnvG/TakeLink.lean`
(nothing else changes).

The per-node transport of the ticket environment `EnvGTD`
(`EnvG/TicketEnv.lean`), carrying the counting extension `TX D`
(`SLR/TicketX.lean`) from the instruction's start to its end, and the
thread's `coh x` (the ticket counter's coherence view):

- `NodeRel.loadTD`, `NodeRel.storeTD`: the ghost-exposing `NodeRel.loadTG` /
  `NodeRel.storeSG` (formerly verbatim copies) with `TX` after: the env forbids loads and stores of
  `D.x`, so the memory gains no message to `x` and the dispenser invariant is
  kept by the take (`TicketInv.takeAll`) or the store's ghost
  (`TicketInv.grow`).
- `NodeRel.rmwTD`: `NodeRel.rmwSG` (formerly a verbatim copy of
  `NodeRel.rmwS`) followed by the **hand-out**
  (`EraseT.rmwHand`, `Dispenser.RStep.hand`, `Dispenser.mayWrite_hand'`). The
  bound `old < D.N` comes from `CountInv`: the thread's `coh x` is `0` (the
  env's `coh x` is, `RmwOkTD`, and the pre relation transfers it), so by the
  machine invariant's `ownCoh` each of its messages to `x` is an outstanding
  promise; one below the write is overtaken, and otherwise the thread has no
  message to `x` (`CountInv.xFresh_of_atomic`) or the RMW fulfils its only
  one (`CountInv.old_lt_fulfil`). Afterwards the env's `coh x` is positive.
- `PreTD` / `PostTD`: `PreS` / `PostS` with the `coh x` transfer (env `0`
  gives actual `0`) and, after, `TX` at the end memory; `nodeSimTD`: the
  `NodeSimT` instance; `treeJ_envGTD_eraseWPRDS_start`: link theorem 1 for
  `EnvGTD`.
-/
import Kraken.Promising.SLR.EnvG.TicketEnv
import Kraken.Promising.SLR.EnvG.TakeLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Coherence views of other locations

`readSuccs_getCoh_ne`, `writeSuccs_getCoh_ne`, `storeOut_getCoh_ne` are in
`EnvG/LinkS.lean` and `loadOutT_getCoh_ne` in `EnvG/TakeLink.lean` (same names). -/

/-! ## `TX` across a write to another location -/

/-- **`TX` after a write of thread `tid` to a location other than `x`** (a
fresh message or the fulfilment of a promise), the ghost step keeping the
claims, the acquire table and the update ids and growing `u`. -/
theorem tx_write {D : Dispenser} {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I} {tid : Nat}
    {g g' : Ghost} (E : Erase rF g T c) (hX : D.TX g c) {cx cx' : Ctx} {l : Loc} {v : Val} {trOpt : Option Time}
    {tw : Time} (hm : cx.mem = c.mem) (hev : WriteEv tid cx cx' l v trOpt tw) (hl : l ≠ D.x)
    (hcl : g'.claims = g.claims) (htab : g'.acqTab = g.acqTab) (hupd : g'.upd = g.upd) (hu : ∀ s ∈ g.u, s ∈ g'.u) :
    D.TX g' (c.withThread tid t cx'.mem) := by
  have hsz := Config.withThread_size c tid t cx'.mem
  obtain ⟨hC, hp⟩ : D.CountInv (c.withThread tid t cx'.mem) ∧ c.mem.Prefix cx'.mem := by
    rcases hev.cases with ⟨hm', -, -⟩ | ⟨hm', -⟩
    · rw [hm', hm]
      exact ⟨hX.2.same rfl hsz, Memory.Prefix.refl _⟩
    · rw [hm', hm]
      exact ⟨hX.2.append (w := ⟨l, v, tid⟩) rfl (fun h => absurd h hl) hsz (fun h => absurd h hl),
        Memory.Prefix.append _ _⟩
  exact ⟨Dispenser.TicketInv.grow E hX.1 hp hC.monoX hcl htab hupd hu, hC⟩

/-! ## The transports -/

section Transport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx} {D : Dispenser}

/-- **Load transport with the take, keeping `TicketInv`** (`NodeRel.loadTG`,
with the dispenser invariant after the take). -/
theorem NodeRel.loadTD (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    (hTI : D.TicketInv g c) {k : LoadKind} {xcl : Bool} {l : Loc} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv cx k xcl l) (B : Time) :
    ∃ σ' r' g', LoadOutT A tid σ σ' k xcl l x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' x.2.2 ∧
      RStepS B r g r' g' x.2.2 ∧ PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' x.2.2 ∧ WpPath c tid t r g r' g' x.2.2 ∧
      D.TicketInv g' c := by
  obtain ⟨σ', r', g', ho, E', hR, hp, hw, hgx⟩ := h.loadTG hnp0 hx B
  refine ⟨σ', r', g', ho, E', hR, hp, hw, ?_⟩
  rcases hgx with rfl | ⟨E0, rfl⟩
  · exact hTI
  · exact Dispenser.TicketInv.takeAll (lt_size_of_get? h.ht) trivial E0 hTI

/-- **Store transport keeping `TX`** (`NodeRel.storeSG`, for a store to a
location other than `x`, with `TX` at the end memory). -/
theorem NodeRel.storeTD (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf) (hX : D.TX g c) {k : StoreKind} {l : Loc} {v : Val} (hlx : l ≠ D.x)
    (hS : pf = none ∨ pf = some (l, v))
    (hok : StoreOk A tid pl σ k false l v) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', StoreOut A tid pl σ σ' k false l v true ∧
      ErAt rF (fun _ => True) c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' cx' ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' cx' ∧ WpPath c tid t r g r' g' cx' ∧
      c.mem.last ≤ cx'.mem.last ∧ (∀ ts ∈ cx'.prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl ∧
      D.TX g' (c.withThread tid t cx'.mem) := by
  rcases h.storeSG hst hS hok hc hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, hcl, hcl', htab, hupd, hu⟩
  · exact .inl ho
  obtain ⟨_, _, _, hev, _, _⟩ := h.ctx.write (A := A) hi (ivLe_envIv _ (iv.forStore cx.stores))
    (h.ctx.sim.ivb.forStore cx.stores) (Nat.le_refl 0) (Nat.zero_le _) hc
  exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, hcl, tx_write h.erase hX h.mem hev hlx hcl' htab hupd hu⟩

/-- A thread whose `coh x` is `0` has only outstanding promises among its
messages to `x` (the machine invariant's `ownCoh`). -/
theorem own_x_prom {D : Dispenser} (hm : c.MachInv) (ht : c.threads[tid]? = some t)
    (h0 : t.views.getCoh D.x = 0) {ts : Time} {w : Msg} (hget : c.mem.get? ts = some w) (hl : w.loc = D.x)
    (htid : w.tid = tid) : ts ∈ t.prom := by
  refine Classical.byContradiction fun hnp => ?_
  have := hm.ownCoh tid t ht ts w hget htid hnp
  rw [hl, h0] at this
  have hts : ts = 0 := by omega_t
  subst hts
  simp [Memory.get?] at hget

/-- **The ticket RMW transport** (`NodeRel.rmwSG` followed by the hand-out of
`tk old`): the RMW on `x` of a thread whose `coh x` is `0`
either overtakes an own promise, or reads `old < D.N`, hands out `tk old`
(`EraseT.rmwHand`), keeps `TX` and leaves the env's `coh x` positive. -/
theorem NodeRel.rmwTD (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    (hX : D.TX g c) (ht0 : t.views.getCoh D.x = 0)
    {k : RmwKind} {l : Loc} {op : Val → Option Val} (hokD : RmwOkTD A tid pl D σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOutTD A tid pl D σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
      RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') ∧
      WpPath c tid t r g r' g' (rmwAfter A k false l cx') ∧ c.mem.last ≤ (rmwAfter A k false l cx').mem.last ∧
      (∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl ∧
      D.TX g' (c.withThread tid t (rmwAfter A k false l cx').mem) ∧ 0 < σ'.vs.getCoh D.x := by
  obtain ⟨hok, rfl, hTO, hkr, -⟩ := hokD
  obtain ⟨tr, old, cx₁⟩ := x
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
  simp only at hm1 hp1 hop hc E ⊢
  have hm1c : cx₁.mem = c.mem := hm1.trans (hm0.trans h.mem)
  have hp1t : cx₁.prom = t.prom := hp1.trans (hp0.trans h.prom)
  have hn := lt_size_of_get? h.ht
  have hi1 : cx₁.Inv tid := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
  obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc hi1
  obtain ⟨-, -, hrd, -⟩ := rmw_event A tid iv hx hi hc
  have hrdc : c.mem.read? D.x tr = some old := hm1c ▸ hrd
  obtain ⟨htrw, hat⟩ := hev.tr tr rfl
  ---- the ticket bound, and `CountInv` at the end memory
  have hsz := Config.withThread_size c tid t cx'.mem
  have hcase : cx'.Overtaken ∨ (old.toNat < D.N ∧ D.CountInv (c.withThread tid t cx'.mem)) := by
    rcases hev.cases with ⟨hm', htp, hget⟩ | ⟨hm', rfl⟩
    · -- the RMW fulfils its thread's promise
      rw [hm1c] at hget
      refine .inr ⟨hX.2.old_lt_fulfil hrdc htrw hget hn, ?_⟩
      rw [hm', hm1c]
      exact hX.2.same rfl hsz
    · -- a fresh write: an own message to `x` is an outstanding promise, overtaken
      by_cases hown : ∃ ts w, c.mem.get? ts = some w ∧ w.loc = D.x ∧ w.tid = tid
      · obtain ⟨ts, w, hget, hl, htid⟩ := hown
        have htp := own_x_prom h.mach h.ht ht0 hget hl htid
        have hle : ts ≤ cx₁.mem.last := by rw [hm1c]; exact c.mem.last_le_of_get?_eq_some hget
        refine .inl ⟨ts, ?_, w, ?_, ?_⟩
        · rw [hev.prom]
          exact (List.mem_erase_of_ne (by omega_t)).mpr (hp1t ▸ htp)
        · rw [hm', Memory.get?_append_of_le _ _ _ hle, hm1c]; exact hget
        · rw [hl]
          exact Nat.le_trans (by omega_t) (writeSuccs_coh_tw' hc hev)
      · have hown' : ∀ ts w, c.mem.get? ts = some w → w.loc = D.x → w.tid ≠ tid :=
          fun ts w hget hl htid => hown ⟨ts, w, hget, hl, htid⟩
        have hlt := (hX.2.old_lt hrdc hn fun ts w _ hget hl => hown' ts w hget hl).1
        rw [hm1c] at hat
        obtain ⟨-, hf⟩ := hX.2.xFresh_of_atomic hrdc hat hown' hn (hTO.2 old new hlt hop)
        refine .inr ⟨hlt, ?_⟩
        rw [hm', hm1c]
        exact hX.2.append rfl hf hsz fun _ => hn
  rcases hcase with hov | ⟨hnN, hC⟩
  · exact .inl hov
  ---- the RMW (`NodeRel.rmwSG`)
  rcases h.rmwSG hnp0 hkr hok hx hop hc E hi with hov |
    ⟨r', g', σ₁, hσ, E', hR, hP, hW, hlast, hpd, hcl, ⟨tw', rfl⟩, hun, hcoh⟩
  · exact .inl hov
  obtain ⟨hm4, -⟩ := rmwAfter_memProm (A := A) k false D.x cx'
  have hr' : r' = σ₁.r := by
    rcases hP.res with ⟨e, -⟩ | ⟨ts, -, -, h1, h2, -⟩
    · exact e
    · exact absurd h2 (hpd ts h1)
  ---- the hand-out
  have hpre : c.mem.Prefix cx'.mem := by
    rcases hev.cases with ⟨hm', -, -⟩ | ⟨hm', -⟩
    · rw [hm', hm1c]; exact Memory.Prefix.refl _
    · rw [hm', hm1c]; exact Memory.Prefix.append _ _
  have E'' : Erase (setRes (setRes rF tid r) tid r') (rmwGhost g D.x tr tw' false []) (fun _ => True)
      (c.withThread tid { t with prom := cx'.prom } cx'.mem) := by
    rw [setRes_setRes]; exact E'
  obtain ⟨s₀, hs₀, hd, h1, hU, E3, hTI⟩ := Dispenser.EraseT.rmwHand (D := D) h.erase hX.1 E'' hpre
    (by rw [Config.withThread_size]; exact hn) hrdc hun hnN hC.monoX (fun _ _ _ hT => absurd trivial hT)
  rw [setRes_setRes] at E3
  have hTI' : D.TicketInv (D.handGhost (rmwGhost g D.x tr tw' false []) old.toNat) (c.withThread tid t cx'.mem) :=
    ⟨hTI.1, hTI.2⟩
  obtain ⟨hle, hW2, hW3, hmw, hW5⟩ := hW
  refine .inr ⟨_, _, _, ⟨_, hσ, hnN, rfl⟩, E3, Dispenser.RStep.hand hR hs₀ hd h1 hU,
    ⟨hP.snap, hP.ghost.trans (Dispenser.handGhost_le _ _), hP.ctx, .inl ⟨by rw [hr'], hpd⟩, hP.cl, hP.fenced⟩,
    ⟨hle.trans (Dispenser.handGhost_le _ _), hW2, hW3, Dispenser.mayWrite_hand' hs₀ hd h1 hU hmw, hW5⟩, hlast, hpd,
    hcl, Dispenser.TX.congr ⟨hTI', hC⟩ (by simp only [Config.withThread_mem']; exact hm4)
      (by simp only [Config.withThread_size]), Nat.lt_of_le_of_lt (Nat.zero_le _) hcoh⟩

end Transport

/-! ## The instance and link theorem 1 -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {D : Dispenser}

/-- **Pre relation of the ticket link**: `PreS`, and the env's `coh x = 0`
gives the start thread's and the node's actual `coh x = 0`. -/
def PreTD (D : Dispenser) (tid : Nat) (pl : Plan) (iv : InstrViews) (rF : Nat → Res) (c : Config I) (t : Thread I)
    (rv₀ : Res) (g₀ : Ghost) (cl₀ : Prop) (rS : Res) (gS : Ghost) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx) :
    Prop :=
  PreS tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx ∧
    (σ.vs.getCoh D.x = 0 → t.views.getCoh D.x = 0 ∧ cx.views.getCoh D.x = 0)

/-- **Post relation of the ticket link**: `PostS`, `TX` at the node's memory,
and the env's `coh x = 0` gives the node's actual `coh x = 0`. -/
def PostTD (D : Dispenser) (tid : Nat) (pl : Plan) (iv : InstrViews) (c : Config I) (t : Thread I) (rv₀ : Res)
    (g₀ : Ghost) (cl₀ : Prop) (pf : Option (Loc × Val)) (rS : Res) (gS : Ghost) (σ : State I) (r : Res) (g : Ghost)
    (cx : Ctx) : Prop :=
  PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx ∧ D.TX g (c.withThread tid t cx.mem) ∧
    (σ.vs.getCoh D.x = 0 → cx.views.getCoh D.x = 0)

/-- **The per-node transport of `EnvGTD`**, at the instruction's start
`(rS, gS)` with `TX gS c`. -/
theorem nodeSimTD {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf) (hX : D.TX gS c) :
    NodeSimT A tid iv rF (fun _ => True) c t gS (EnvGTD I A tid pl D) (LokS pf) (SokS pf) (RokS A pf) (LokS pf)
      (fun σ r g cx => PreTD D tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostTD D tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) where
  pre_post := by
    rintro σ r g cx hpf ⟨⟨h, rfl, rfl⟩, hco⟩
    refine ⟨⟨h.post, WpPath.refl h.mem h.prom, by rw [h.mem]; exact Nat.le_refl _,
      fun ts hts => hst.none hpf ts (h.prom ▸ hts), fun hne => absurd hpf hne⟩, ?_, fun h0 => (hco h0).2⟩
    exact Dispenser.TX.congr hX (by rw [Config.withThread_mem', h.mem]) (Config.withThread_size ..)
  fence_pre {k} {σ} _ _ cx h _ :=
    ⟨fenceState σ k, fenceOut_fenceState σ k, ⟨⟨h.1.1.fence k, h.1.2⟩, fun h0 => by
      rw [fenceStep_views, fenceViews_getCoh]
      exact h.2 ((fenceViews_getCoh σ.vs k D.x).symm.trans h0)⟩⟩
  fence_post {k} {σ} _ _ cx h _ := by
    have hm := fenceStep_mem cx k; have hp := fenceStep_prom cx k
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, hX', hco⟩ := h
    refine ⟨fenceState σ k, fenceOut_fenceState σ k, ⟨h1.fence k, h2.congr hm hp, hm ▸ h3, hp ▸ h4, h5⟩,
      by rw [hm]; exact hX', fun h0 => ?_⟩
    rw [fenceStep_views, fenceViews_getCoh]
    exact hco ((fenceViews_getCoh σ.vs k D.x).symm.trans h0)
  load := by
    rintro k xcl addr n σ r g cx hpf ⟨⟨h, rfl, rfl⟩, hco⟩ hlx x hx -
    have hlx' : D.x ≠ (⟨addr, n⟩ : Loc) := Ne.symm hlx
    obtain ⟨σ', r', g', ho, E', hR, hp, hw, hTI⟩ := h.loadTD (hst.none hpf) hX.1 hx c.mem.last
    obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
    have hm : x.2.2.mem = c.mem := hm1.trans h.mem
    have hpr : x.2.2.prom = t.prom := hp1.trans h.prom
    refine ⟨σ', r', g', ho, E', hR.toG (Nat.le_refl _), ⟨⟨hp, hw, by rw [hm]; exact Nat.le_refl _,
      fun ts hts hpd => hst.none hpf ts (hpr ▸ hts) (hw.2.2.1 ts hpd), fun hne => absurd hpf hne⟩, ?_, fun h0 => ?_⟩⟩
    · exact Dispenser.TX.congr ⟨hTI, hX.2⟩ (by rw [Config.withThread_mem', hm]) (Config.withThread_size ..)
    · rw [readSuccs_getCoh_ne hx hlx']
      exact (hco ((loadOutT_getCoh_ne ho hlx').symm.trans h0)).2
  store := by
    rintro k xcl addr n v σ r g cx hS ⟨⟨h, rfl, rfl⟩, hco⟩ ⟨hok, hlx⟩
    have hlx' : D.x ≠ (⟨addr, n⟩ : Loc) := Ne.symm hlx
    obtain rfl : xcl = false := hok.1
    refine ⟨fun cx' hc _ hi _ => ?_, fun hx => absurd hx Bool.false_ne_true⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    rcases h.storeTD hst hX hlx hS hok hc hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, hcl, hX'⟩
    · exact .inl ho
    · refine .inr ⟨r', g', σ', hst', E', hR, ⟨⟨hp, hw, hl, hpd, fun _ hc0 => hcl ▸ h.cl hc0⟩, hX', fun h0 => ?_⟩⟩
      rw [writeSuccs_getCoh_ne hc hlx']
      exact (hco ((storeOut_getCoh_ne hst' hlx').symm.trans h0)).2
  rmw := by
    rintro k addr n op σ r g cx ⟨hpf, -⟩ ⟨⟨h, rfl, rfl⟩, hco⟩ hok x hx
    refine ⟨fun hop => absurd hop (hok.2.2.1.1 x.2.1), fun new hop cx' hc E hi _ => ?_⟩
    rcases h.rmwTD (hst.none hpf) hX (hco hok.2.2.2.2).1 hok hx hop hc E hi with
      ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, -, hX', hpos⟩
    · exact .inl ho
    · exact .inr ⟨r', g', σ', hst', E', hR, ⟨⟨hp, hw, hl, hpd, fun hne => absurd hpf hne⟩, hX',
        fun h0 => absurd h0 (Nat.ne_of_gt hpos)⟩⟩

/-- **Link theorem 1 for the ticket environment** (`treeJ_envGT_eraseWPRDS`
for `EnvGTD`, with `TX` at the start and the `coh x` transfer). -/
theorem treeJ_envGTD_eraseWPRDS {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    (hX : D.TX gS c) {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDST (nodeSimTD (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀)
      (g₀ := g₀) (cl₀ := cl₀) (rS := rS) hst hX) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (hco : σ.vs.getCoh D.x = 0 → t.views.getCoh D.x = 0 ∧ cx.views.getCoh D.x = 0)
    (ha : SingleAccessS (LokS pf) (SokS pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid iv rF (fun _ => True) c t gS
      (PostOf (E := EnvGTD I A tid pl D) Q
        (fun (σ' : State I) r' g' cx' => PostTD D tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDST _ hW ⟨⟨h, rfl, rfl⟩, hco⟩ ha

/-- **Link theorem 1 for the ticket environment at an instruction's start**:
from `EnvRel`, `TX` and the `coh x` transfer of the start thread. -/
theorem treeJ_envGTD_eraseWPRDS_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf) (hX : D.TX g c) (hown : σ.vs.getCoh D.x = 0 → t.views.getCoh D.x = 0)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDST (nodeSimTD (A := A) (pl := pl) (iv := instrViews t d) (rF := rF) (rv₀ := σ.r)
      (g₀ := g) (cl₀ := cl) (rS := r) hst hX) Q).W tree σ)
    (ha : SingleAccessS (LokS pf) (SokS pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid (instrViews t d) rF (fun _ => True) c t g
      (PostOf (E := EnvGTD I A tid pl D) Q
        (fun (σ' : State I) r' g' cx' => PostTD D tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envGTD_eraseWPRDS hst hX hW (hrel.toNodeRel rF d E hm) (fun h0 => ⟨hown h0, hown h0⟩) ha

end Link

#print axioms NodeRel.loadTD
#print axioms NodeRel.storeTD
#print axioms NodeRel.rmwTD
#print axioms treeJ_envGTD_eraseWPRDS_start

end Kraken.Promising.SLR.EnvG
