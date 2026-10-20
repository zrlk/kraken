/-
**Item 1, part 2: the ticket link with a
release-kind ticket RMW.** ISA-neutral. Adapted from
`EnvG/TicketLink.lean`, `EnvG/LinkS.lean` (`NodeRel.rmwSG`) and
`EnvG/LinkR.lean` (`NodeRel.rmwRelS`); nothing else changes.

The per-node transport of `EnvGTDR` (`EnvG/TicketREnv.lean`), carrying the
counting extension `TX D` and the thread's `coh x`, with the RMW side
condition `RokR` (`EnvG/LinkR.lean`): the ticket RMW on `x` may be of any
kind, and may be the in-flight prepaid release of its own write.

- `NodeRel.rmwSGR`: `NodeRel.rmwSG` (ghost-exposing RMW transport without a
  release in flight) for an RMW of any kind at a location the plan never
  releases (`∀ v, pl.rel l v = false`), in place of `¬ effRelRmw A k`.
- `NodeRel.rmwRelSG`: `NodeRel.rmwRelS` (the RMW fulfilling the in-flight
  pending promise) at such a location, exposing the ghost step
  (`unpend (rmwGhost g l tr tw false []) tw`), the fulfilment facts, the
  unclaimed read and the env's `coh l` after.
- `Dispenser.EraseT.rmwHandUnpend`: `EraseT.rmwHand` after the fulfilment of
  a pending promise (the ghost is `unpend` of the RMW's ghost; the dispenser
  invariant does not look at pending marks, `DispOK.frame`).
- `NodeRel.ticketBoundR`: the ticket bound and `CountInv` after the ticket
  RMW (the first half of `NodeRel.rmwTD`, verbatim).
- `NodeRel.rmwTDR` / `NodeRel.rmwTDRRel`: the ticket RMW transport without /
  with a release in flight, followed by the hand-out (`NodeRel.rmwTD`'s
  conclusion).
- `nodeSimTDR` (the `NodeSimT2` instance; loads, stores and fences are
  `nodeSimTD`'s, `EnvGTDR` agreeing with `EnvGTD` on them definitionally),
  `treeJ_envGTDR_eraseWPRDS(_start)`: link theorem 1 for `EnvGTDR`, with
  `PreTD`/`PostTD` of the ticket link.
-/
import Kraken.Promising.SLR.EnvG.TicketREnv
import Kraken.Promising.SLR.EnvG.TicketLink
import Kraken.Promising.SLR.EnvG.TakeRLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The RMW transports at a location the plan never releases -/

section Transport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}

/-- **RMW transport of any kind at a location the plan never releases,
exposing the ghost step** (`NodeRel.rmwSG` with `∀ v, pl.rel l v = false`
in place of `¬ effRelRmw A k`: the written value is pure either way). -/
theorem NodeRel.rmwSGR (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : RmwKind} {l : Loc} (hrl0 : ∀ v, pl.rel l v = false) {op : Val → Option Val} (hok : RmwOk A tid pl σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOut A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
      RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') ∧
      WpPath c tid t r g r' g' (rmwAfter A k false l cx') ∧ c.mem.last ≤ (rmwAfter A k false l cx').mem.last ∧
      (∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl ∧
      (∃ tw, g' = rmwGhost g l x.1 tw false []) ∧ ¬ g.Claimed (l, x.1) ∧ x.1 < σ'.vs.getCoh l :=
  h.rmwSGP hnp0 (fun v _ => hrl0 v) hok hx hop hc E hi

/-- **RMW transport at an in-flight release, at a location the plan never
releases, exposing the ghost step** (`NodeRel.rmwRelS` with
`∀ v', pl.rel l v' = false` in place of `RelRmwGiveOk`): the write
fulfilling the pending promise `tw` leaves the ghost
`unpend (rmwGhost g l x.1 tw false []) tw`, the memory unchanged, and the
message read unclaimed before. -/
theorem NodeRel.rmwRelSG (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {l : Loc} {v : Val}
    (hst : StartS tid c t g (some (l, v))) (hrl0 : ∀ v', pl.rel l v' = false)
    {k : RmwKind} {op : Val → Option Val} (hok : RmwOk A tid pl σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOut A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
      RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') ∧
      WpPath c tid t r g r' g' (rmwAfter A k false l cx') ∧ c.mem.last ≤ (rmwAfter A k false l cx').mem.last ∧
      (∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl ∧
      (∃ tw, g' = unpend (rmwGhost g l x.1 tw false []) tw ∧ x.1 < tw ∧ c.mem.get? tw = some ⟨l, new, tid⟩ ∧
        cx'.mem = c.mem) ∧ ¬ g.Claimed (l, x.1) ∧ x.1 < σ'.vs.getCoh l :=
  h.rmwRelSGP hst (fun _ hrl => absurd ((hrl0 v).symm.trans hrl) Bool.false_ne_true) hok hx hop hc E hi

end Transport

/-! ## The hand-out after the fulfilment of a pending promise -/

/-- **`EraseT.rmwHand` after the fulfilment of a pending promise**: the ghost
after the RMW is `unpend (rmwGhost g x tr tw rel ss) tw` (the pending mark of
the fulfilled promise dropped); the dispenser invariant does not look at
pending marks (`DispOK.frame`), so the hand-out of `tk old` goes through as
in `EraseT.rmwHand`. -/
theorem _root_.Kraken.Promising.SLR.Dispenser.EraseT.rmwHandUnpend {D : Dispenser} {rF : Nat → Res} {g : Ghost}
    {T : Nat → Prop} {c c' : Config I} {tid : Nat} {r' : Res} (E : Erase rF g T c) (h : D.TicketInv g c)
    {tr tw : Time} {old : Val} {rel : Bool} {ss : List Slot}
    (E' : Erase (setRes rF tid r') (unpend (rmwGhost g D.x tr tw rel ss) tw) T c')
    (hp : c.mem.Prefix c'.mem) (hn : tid < c'.threads.size) (hrd : c.mem.read? D.x tr = some old)
    (hun : ¬ g.Claimed (D.x, tr)) (hnN : old.toNat < D.N) (hmono : D.MonoX c'.mem)
    (hval : ∀ i t, c'.threads[i]? = some t → ¬ T i → ∀ ts ∈ t.prom, ts ∉ (unpend (rmwGhost g D.x tr tw rel ss) tw).pend →
      ∀ w, c'.mem.get? ts = some w →
      mayWrite (setRes rF tid (r'.op (tok D.o (D.tk old.toNat))) i)
        (D.handGhost (unpend (rmwGhost g D.x tr tw rel ss) tw) old.toNat) w.loc) :
    ∃ s₀ ∈ (unpend (rmwGhost g D.x tr tw rel ss) tw).u, D.IsDisp s₀ ∧ s₀.res.acq D.o (D.tk old.toNat) = 1 ∧
      D.ιD ∈ g.upd D.o ∧
      EraseT D (setRes rF tid (r'.op (tok D.o (D.tk old.toNat))))
        (D.handGhost (unpend (rmwGhost g D.x tr tw rel ss) tw) old.toNat) T c' := by
  obtain ⟨-, hD⟩ := Dispenser.DispOK.rmw (rel := rel) (ss := ss) (tw := tw) E h hp hrd hun
  have htr := lc_read?_le_last hrd
  have hD' : D.DispOK (unpend (rmwGhost g D.x tr tw rel ss) tw) c'.mem (· = old.toNat) :=
    hD.frame (fun s hs _ => hs) (fun _ => Iff.rfl) id id rfl
  have hH : D.Handed (unpend (rmwGhost g D.x tr tw rel ss) tw) c'.mem old.toNat :=
    ⟨tr, tw, old, List.mem_cons_self .., by rw [hp.read? htr]; exact hrd, rfl⟩
  obtain ⟨s₀, hs₀, hd, h1, hk⟩ := Dispenser.DispOK.handOut hD' hH hnN
  refine ⟨s₀, hs₀, hd, h1, h.disp.upd, ?_, ⟨hk (Dispenser.disp_unique E' hs₀ hd), hmono⟩⟩
  exact Dispenser.eraseHandOut E' hn hs₀ hd h1 (fun v m V r hr => hD'.dPred v m V r _ hr) hval

/-! ## The ticket RMW transports -/

section TicketTransport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx} {D : Dispenser}

/-- **The ticket bound** (the first half of `NodeRel.rmwTD`, verbatim): the
RMW on `x` of a thread whose `coh x` is `0` either overtakes an own promise,
or reads a value below `D.N`, keeps `CountInv`, and grows the memory by a
prefix. -/
theorem NodeRel.ticketBoundR (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hX : D.TX g c)
    (ht0 : t.views.getCoh D.x = 0) {k : RmwKind} {op : Val → Option Val} (hTO : TicketOp D.N op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false D.x false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true D.x new (some x.1)
      (x.2.2.loadViews.getLastD 0))
    (hi : cx.Inv tid) :
    cx'.Overtaken ∨ (x.2.1.toNat < D.N ∧ D.CountInv (c.withThread tid t cx'.mem) ∧
      c.mem.read? D.x x.1 = some x.2.1 ∧ c.mem.Prefix cx'.mem) := by
  obtain ⟨tr, old, cx₁⟩ := x
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
  simp only at hm1 hp1 hop hc ⊢
  have hm1c : cx₁.mem = c.mem := hm1.trans (hm0.trans h.mem)
  have hp1t : cx₁.prom = t.prom := hp1.trans (hp0.trans h.prom)
  have hn := lt_size_of_get? h.ht
  have hi1 : cx₁.Inv tid := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
  obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc hi1
  obtain ⟨-, -, hrd, -⟩ := rmw_event A tid iv hx hi hc
  have hrdc : c.mem.read? D.x tr = some old := hm1c ▸ hrd
  obtain ⟨htrw, hat⟩ := hev.tr tr rfl
  have hsz := Config.withThread_size c tid t cx'.mem
  have hpre : c.mem.Prefix cx'.mem := by
    rcases hev.cases with ⟨hm', -, -⟩ | ⟨hm', -⟩
    · rw [hm', hm1c]; exact Memory.Prefix.refl _
    · rw [hm', hm1c]; exact Memory.Prefix.append _ _
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
  · exact .inr ⟨hnN, hC, hrdc, hpre⟩

/-- **The ticket RMW transport without a release in flight, any kind**
(`NodeRel.rmwTD` for `RmwOkTDR`, by `NodeRel.rmwSGR`): the RMW on `x` of a
thread whose `coh x` is `0` either overtakes an own promise, or reads
`old < D.N`, hands out `tk old`, keeps `TX` and leaves the env's `coh x`
positive. -/
theorem NodeRel.rmwTDR (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    (hX : D.TX g c) (ht0 : t.views.getCoh D.x = 0)
    {k : RmwKind} {l : Loc} {op : Val → Option Val} (hokD : RmwOkTDR A tid pl D σ k l op)
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
  obtain ⟨hok, rfl, hTO, hrl0, -⟩ := hokD
  rcases h.ticketBoundR hX ht0 hTO hx hop hc hi with hov | ⟨hnN, hC, hrdc, hpre⟩
  · exact .inl hov
  rcases h.rmwSGR hnp0 hrl0 hok hx hop hc E hi with hov |
    ⟨r', g', σ₁, hσ, E', hR, hP, hW, hlast, hpd, hcl, ⟨tw', rfl⟩, hun, hcoh⟩
  · exact .inl hov
  have hn := lt_size_of_get? h.ht
  obtain ⟨hm4, -⟩ := rmwAfter_memProm (A := A) k false D.x cx'
  have hr' : r' = σ₁.r := by
    rcases hP.res with ⟨e, -⟩ | ⟨ts, -, -, h1, h2, -⟩
    · exact e
    · exact absurd h2 (hpd ts h1)
  have E'' : Erase (setRes (setRes rF tid r) tid r') (rmwGhost g D.x x.1 tw' false []) (fun _ => True)
      (c.withThread tid { t with prom := cx'.prom } cx'.mem) := by
    rw [setRes_setRes]; exact E'
  obtain ⟨s₀, hs₀, hd, h1, hU, E3, hTI⟩ := Dispenser.EraseT.rmwHand (D := D) h.erase hX.1 E'' hpre
    (by rw [Config.withThread_size]; exact hn) hrdc hun hnN hC.monoX (fun _ _ _ hT => absurd trivial hT)
  rw [setRes_setRes] at E3
  have hTI' : D.TicketInv (D.handGhost (rmwGhost g D.x x.1 tw' false []) x.2.1.toNat)
      (c.withThread tid t cx'.mem) :=
    ⟨hTI.1, hTI.2⟩
  obtain ⟨hle, hW2, hW3, hmw, hW5⟩ := hW
  refine .inr ⟨_, _, _, ⟨_, hσ, hnN, rfl⟩, E3, Dispenser.RStep.hand hR hs₀ hd h1 hU,
    ⟨hP.snap, hP.ghost.trans (Dispenser.handGhost_le _ _), hP.ctx, .inl ⟨by rw [hr'], hpd⟩, hP.cl, hP.fenced⟩,
    ⟨hle.trans (Dispenser.handGhost_le _ _), hW2, hW3, Dispenser.mayWrite_hand' hs₀ hd h1 hU hmw, hW5⟩, hlast, hpd,
    hcl, Dispenser.TX.congr ⟨hTI', hC⟩ (by simp only [Config.withThread_mem']; exact hm4)
      (by simp only [Config.withThread_size]), Nat.lt_of_le_of_lt (Nat.zero_le _) hcoh⟩

/-- **The ticket RMW transport at an in-flight release** (`pf = some (l, v)`,
by `NodeRel.rmwRelSG`): the RMW on `x` fulfilling the thread's pending
promise either overtakes an own promise, or reads `old < D.N`, hands out
`tk old`, keeps `TX` and leaves the env's `coh x` positive. -/
theorem NodeRel.rmwTDRRel (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {l : Loc} {v : Val}
    (hst : StartS tid c t g (some (l, v))) (hX : D.TX g c) (ht0 : t.views.getCoh D.x = 0)
    {k : RmwKind} {op : Val → Option Val} (hokD : RmwOkTDR A tid pl D σ k l op)
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
  obtain ⟨hok, rfl, hTO, hrl0, -⟩ := hokD
  rcases h.ticketBoundR hX ht0 hTO hx hop hc hi with hov | ⟨hnN, hC, hrdc, hpre⟩
  · exact .inl hov
  rcases h.rmwRelSG hst hrl0 hok hx hop hc E hi with hov |
    ⟨r', g', σ₁, hσ, E', hR, hP, hW, hlast, hpd, hcl, ⟨tw', rfl, -, -, -⟩, hun, hcoh⟩
  · exact .inl hov
  have hn := lt_size_of_get? h.ht
  obtain ⟨hm4, -⟩ := rmwAfter_memProm (A := A) k false D.x cx'
  have hr' : r' = σ₁.r := by
    rcases hP.res with ⟨e, -⟩ | ⟨ts, -, -, h1, h2, -⟩
    · exact e
    · exact absurd h2 (hpd ts h1)
  have E'' : Erase (setRes (setRes rF tid r) tid r') (unpend (rmwGhost g D.x x.1 tw' false []) tw') (fun _ => True)
      (c.withThread tid { t with prom := cx'.prom } cx'.mem) := by
    rw [setRes_setRes]; exact E'
  obtain ⟨s₀, hs₀, hd, h1, hU, E3, hTI⟩ := Dispenser.EraseT.rmwHandUnpend (D := D) h.erase hX.1 E'' hpre
    (by rw [Config.withThread_size]; exact hn) hrdc hun hnN hC.monoX (fun _ _ _ hT => absurd trivial hT)
  rw [setRes_setRes] at E3
  have hTI' : D.TicketInv (D.handGhost (unpend (rmwGhost g D.x x.1 tw' false []) tw') x.2.1.toNat)
      (c.withThread tid t cx'.mem) :=
    ⟨hTI.1, hTI.2⟩
  obtain ⟨hle, hW2, hW3, hmw, hW5⟩ := hW
  refine .inr ⟨_, _, _, ⟨_, hσ, hnN, rfl⟩, E3, Dispenser.RStep.hand hR hs₀ hd h1 hU,
    ⟨hP.snap, hP.ghost.trans (Dispenser.handGhost_le _ _), hP.ctx, .inl ⟨by rw [hr'], hpd⟩, hP.cl, hP.fenced⟩,
    ⟨hle.trans (Dispenser.handGhost_le _ _), hW2, hW3, Dispenser.mayWrite_hand' hs₀ hd h1 hU hmw, hW5⟩, hlast, hpd,
    hcl, Dispenser.TX.congr ⟨hTI', hC⟩ (by simp only [Config.withThread_mem']; exact hm4)
      (by simp only [Config.withThread_size]), Nat.lt_of_le_of_lt (Nat.zero_le _) hcoh⟩

end TicketTransport

/-! ## The instance and link theorem 1 -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {D : Dispenser}

/-- **The per-node transport of `EnvGTDR`**, at the instruction's start
`(rS, gS)` with `TX gS c`: loads, stores and fences as `nodeSimTD`; the
ticket RMW without (`NodeRel.rmwTDR`) or with (`NodeRel.rmwTDRRel`) its own
release in flight. -/
theorem nodeSimTDR {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf) (hX : D.TX gS c) :
    NodeSimT2 A tid iv rF (fun _ => True) c t gS (EnvGTDR I A tid pl D) (LokS pf) (SokS pf) (RokR pf) (LokS pf)
      (fun σ r g cx => PreTD D tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostTD D tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) :=
  have hT := nodeSimTD (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst hX
  { pre_post := hT.pre_post
    fence_pre := hT.fence_pre
    fence_post := hT.fence_post
    load := hT.load
    store := hT.store
    rmw := by
      rintro k addr n op σ r g cx hR ⟨⟨h, rfl, rfl⟩, hco⟩ hok x hx
      refine ⟨fun hop => absurd hop (hok.2.2.1.1 x.2.1), fun new hop cx' hc E hi _ => ?_⟩
      have ht0 := (hco hok.2.2.2.2).1
      rcases hR with hpf | ⟨v, hpf, -⟩
      · rcases h.rmwTDR (hst.none hpf) hX ht0 hok hx hop hc E hi with
          ho | ⟨r', g', σ', hst', E', hR', hp, hw, hl, hpd, -, hX', hpos⟩
        · exact .inl ho
        · exact .inr ⟨r', g', σ', hst', E', hR', ⟨⟨hp, hw, hl, hpd, fun hne => absurd hpf hne⟩, hX',
            fun h0 => absurd h0 (Nat.ne_of_gt hpos)⟩⟩
      · subst hpf
        rcases h.rmwTDRRel hst hX ht0 hok hx hop hc E hi with
          ho | ⟨r', g', σ', hst', E', hR', hp, hw, hl, hpd, hcl, hX', hpos⟩
        · exact .inl ho
        · exact .inr ⟨r', g', σ', hst', E', hR', ⟨⟨hp, hw, hl, hpd, fun _ hc0 => hcl ▸ h.cl hc0⟩, hX',
            fun h0 => absurd h0 (Nat.ne_of_gt hpos)⟩⟩ }

/-- **Link theorem 1 for `EnvGTDR`** (`treeJ_envGTD_eraseWPRDS` with the
`RokR` side conditions). -/
theorem treeJ_envGTDR_eraseWPRDS {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    (hX : D.TX gS c) {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDST2 (nodeSimTDR (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀)
      (g₀ := g₀) (cl₀ := cl₀) (rS := rS) hst hX) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (hco : σ.vs.getCoh D.x = 0 → t.views.getCoh D.x = 0 ∧ cx.views.getCoh D.x = 0)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid iv rF (fun _ => True) c t gS
      (PostOf (E := EnvGTDR I A tid pl D) Q
        (fun (σ' : State I) r' g' cx' => PostTD D tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDST2 _ hW ⟨⟨h, rfl, rfl⟩, hco⟩ ha

/-- **Link theorem 1 for `EnvGTDR` at an instruction's start**: from
`EnvRel`, `TX` and the `coh x` transfer of the start thread. -/
theorem treeJ_envGTDR_eraseWPRDS_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf) (hX : D.TX g c) (hown : σ.vs.getCoh D.x = 0 → t.views.getCoh D.x = 0)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDST2 (nodeSimTDR (A := A) (pl := pl) (iv := instrViews t d) (rF := rF) (rv₀ := σ.r)
      (g₀ := g) (cl₀ := cl) (rS := r) hst hX) Q).W tree σ)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) :
    tree.EraseWPRDS A tid (instrViews t d) rF (fun _ => True) c t g
      (PostOf (E := EnvGTDR I A tid pl D) Q
        (fun (σ' : State I) r' g' cx' => PostTD D tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envGTDR_eraseWPRDS hst hX hW (hrel.toNodeRel rF d E hm) (fun h0 => ⟨hown h0, hown h0⟩) ha

end Link

#print axioms NodeRel.rmwSGR
#print axioms NodeRel.rmwRelSG
#print axioms Dispenser.EraseT.rmwHandUnpend
#print axioms NodeRel.rmwTDR
#print axioms NodeRel.rmwTDRRel
#print axioms treeJ_envGTDR_eraseWPRDS_start

end Kraken.Promising.SLR.EnvG
