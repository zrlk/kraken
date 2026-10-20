/-
Whole-thread environment, **Claim-conditional RMWs** part 2: the per-tree link of the
claim-conditional environment `EnvGC` (`EnvG/RmwGhost.lean`), additively
beside `EnvG/LinkR.lean`. ISA-neutral; nothing imports this file.

- `NodeRel.rmwC'` (no release in flight, any RMW kind): a claiming RMW
  (`ClaimOk`) is `LinkR`'s `NodeRel.rmwS'` with the give taken from `σ.r` and
  the claimed slots kept (`Plan.afterC_op_give`); a non-claiming RMW is erased
  as a store at its write (`ErAt.store`, `RStep.store`, `mayWrite_store_le`):
  the read message's update slots stay where they are.
- `NodeRel.rmwRelC` (the RMW's write is the in-flight prepaid promise
  `ts`): the fulfilment is `ErAt.fulfilPend`, followed, for a claiming RMW, by
  `Erase.claimPend`; the actual resource is the env's
  `(pl.after l v ts P σ.r) ⋅ C` with **no** side condition (`Res.addW_op_claim`):
  `RelRmwGiveOk` and `Plan.Whole` are not needed.
- `nodeSimS2_envGC`, `treeJ_envGC_eraseWPRDSR(_start)`: as
  `nodeSimS2_envG`/`treeJ_envG_eraseWPRDSR(_start)` without `hG`.

Both transports are proved once, for the adjacency permission
`RmwOkCAdj` (`NodeRel.rmwCAdj'`/`NodeRel.rmwRelCAdj`, moved here from
`EnvG/AdjSpikeLink.lean`; `EnvG/AdjCore.lean`), and `rmwC'`/`rmwRelC` are
their instances through `RmwOkC.toCAdj`.

Phase-1 limits otherwise as `LinkR` (`RokR`: an in-flight release RMW never
fails).
-/
import Kraken.Promising.SLR.EnvG.AdjCore

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- **`acqLe` for a claiming RMW of either release mode** (`mayWrite_rmwRel_le`
for any `rel`). -/
theorem mayWrite_rmw_le {g : Ghost} {r r' R : Res} {x : Loc} {tr tw : Time} {rel : Bool} {p : Val × Time}
    {ss : List Slot} (hres : r'.op R = (r.op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x p)
    (hprod : Res.prod (ss.map (·.res)) = R) (hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key) {y : Loc}
    (h : mayWrite r' (rmwGhost g x tr tw rel ss) y) : mayWrite r g y := by
  have h' : mayWrite r' (storeGhost (rmwGhost g x tr tw false []) x tw rel ss) y := by
    have e : (rmwGhost g x tr tw rel ss).u = (storeGhost (rmwGhost g x tr tw false []) x tw rel ss).u := by
      simp [rmwGhost, storeGhost]
    unfold mayWrite at h ⊢
    rw [← e]; exact h
  have hdisj' : ∀ s ∈ (rmwGhost g x tr tw false []).u, ∀ s' ∈ ss, s.key ≠ s'.key := by
    intro s hs s' hs'
    rcases mem_rmw_u.mp hs with ⟨hs, -⟩ | hs
    · exact hdisj s hs s' hs'
    · cases hs
  have h1 := mayWrite_store_le (r := (r.op (Res.prod ((claimedSlots g x tr).map (·.res))))) hres hprod hdisj' h'
  have h2 : mayWrite ((r.op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x p) (rmwGhost g x tr tw false []) y := by
    unfold mayWrite at h1 ⊢
    rw [Res.addW_q, Res.addW_acq]; exact h1
  exact SpinCommon.mayWrite_claim h2

/-- A failing RMW's outcome in `EnvG` is one in `EnvGC`. -/
theorem RmwOut.toC_none {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {old : Val} (h : RmwOut A tid pl σ σ' k l op old) (hop : op old = none) :
    RmwOutC A tid pl σ σ' k l op old := by
  obtain ⟨c, x, hanc, hx, hold, hcl, hseen, hfR, hfW, hbr⟩ := h
  refine ⟨c, x, hanc, hx, hold, hcl, hseen, hfR, hfW, ?_⟩
  rcases hbr with hb | ⟨new, -, -, hop', -⟩
  · exact .inl hb
  · rw [hop] at hop'; cases hop'

section Transport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}

/-- **Claim-conditional RMW transport without a release in flight, any
kind, for `RmwOkCAdj`** (moved here from `EnvG/AdjSpikeLink.lean`): the release
obligation may assume `AdjAt`, which the fresh RMW's
read supplies (`adjAt_of_ctx`). The generic form: `NodeRel.rmwC'` is its
instance (`RmwOkC.toCAdj`). -/
theorem NodeRel.rmwCAdj' (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : RmwKind} {l : Loc} {op : Val → Option Val} (hok : RmwOkCAdj A tid pl σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOutC A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
      RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') ∧
      WpPath c tid t r g r' g' (rmwAfter A k false l cx') ∧ c.mem.last ≤ (rmwAfter A k false l cx').mem.last ∧
      (∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl := by
  obtain ⟨tr, old, cx₁⟩ := x
  obtain ⟨cxe₁, hx', hc1⟩ := (h.ctx.fenceOpt (A := A)).read hx
  have hx'0 : (tr, old, cxe₁) ∈ readSuccs A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l
      false := hx'
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
  simp only at hm1 hp1 hop hc E ⊢
  have hm1c : cx₁.mem = c.mem := hm1.trans (hm0.trans h.mem)
  have hp1t : cx₁.prom = t.prom := hp1.trans (hp0.trans h.prom)
  have hn := lt_size_of_get? h.ht
  have hi1 : cx₁.Inv tid := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
  have hex : cxe₁.loadViews.getLastD 0 ≤ cx₁.loadViews.getLastD 0 :=
    Nat.le_trans (Rel2.getLastD hc1.sim.rel.loadViews 0 0 (Nat.zero_le _)) (idUpTo_fv_le _ _)
  have hexb : cx₁.loadViews.getLastD 0 ≤ cx₁.mem.last := getLastD_le' hc1.sim.bnd.loadViews
  obtain ⟨cxe₂, tw, hc', hev, hev', hcl2⟩ := hc1.write hi1 (ivLe_envIv _ iv) hc1.sim.ivb hex hexb hc
  have hc'0 : cxe₂ ∈ writeSuccs A tid iv0 cxe₁ (A.rmwKind k).storeKind true l new (some tr)
      (cxe₁.loadViews.getLastD 0) := hc'
  by_cases hov : cxe₂.Overtaken
  · exact .inl (hcl2.overtaken hov)
  obtain ⟨hr, hn'⟩ : r = σ.r ∧ ∀ ts ∈ t.prom, ts ∉ g.pend := by
    rcases h.res with h' | ⟨ts, -, -, h1, h2, -⟩
    · exact h'
    · exact absurd h2 (hnp0 ts h1)
  have hgr : g.rel = σ.g.rel := h.ghost.rel
  have hprom' : ∀ ts ∈ cx'.prom, ts ∈ t.prom := fun ts hts => by
    rw [hev.prom] at hts; exact hp1t ▸ List.mem_of_mem_erase hts
  have hpd : tw ∉ g.pend := fun hpd => by
    rcases hev.cases with ⟨-, htp, -⟩ | ⟨-, rfl⟩
    · exact hn' tw (hp1t ▸ htp) hpd
    · have h1 := h.erase.pend_le hpd; rw [← hm1c] at h1; omega_t
  obtain ⟨-, -, hrd, hseen⟩ := rmw_event A tid iv hx hi hc
  have hnp : ∀ p ∈ cx₁.prom, p ∉ g.pend := fun p hp => hn' p (hp1t ▸ hp)
  have hposr : 0 < (r.wr l).q := hr ▸ hok.1
  obtain ⟨hrdAt, hvle⟩ := readAt_rmw hx'0
  obtain ⟨hpure, hrel⟩ := hok.2 c g tr old new h.anchorOk hrdAt hop
  have htrC : ClaimOk A k σ.vs l tr → tr ≤ (rmwAfter A k false l cx').views.wfloor := fun hcond => by
    rcases hcond with hk | ⟨hk, hnf⟩
    · exact rmw_tr_le_wfloor_acqRel hc (by rw [hk]; rfl)
    · have hfw : ∀ f, (fenceOptCtx A (envCtx tid σ.vs c)).views.getFwd l = some f → f.time ≠ tr := by
        intro f hf ht
        rw [fenceOptCtx_views, rmwReadViews_getFwd] at hf
        exact hnf ⟨f, hf, ht⟩
      exact Nat.le_trans (rmw_tr_le_wfloor_acq hx'0 hk hfw hc'0 k false) (hcl2.rmwAfter k false l).wfloor
  have hown : tw ∈ cx₁.prom → Pred.Pure (g.rel l) new := fun htp => by
    rcases hev.cases with ⟨-, -, hget⟩ | ⟨-, rfl⟩
    · exact Erase.pure_of_own h.erase h.ht (hp1t ▸ htp) hpd (hm1c ▸ hget)
    · obtain ⟨w, hw, -⟩ := hi1.prom _ htp
      have := cx₁.mem.last_le_of_get?_eq_some hw
      omega_t
  have hpl : pl.rel l new = true → tw ∉ ownProm tid c ∨ tw ∈ g.pend := fun hrl =>
    .inl fun htp => (hrel hrl).2.1 (hgr ▸ hown (by rw [hp1t, ← ownProm_eq h.ht]; exact htp))
  have hun : ¬ g.Claimed (l, tr) :=
    ErAt.not_claimed_rmw E hn hi1 hev hrd hseen fun p hp hpd => absurd hpd (hnp p hp)
  -- the slots of the written message (what it carries: the give of `σ.r`)
  obtain ⟨rel, ss, hrelS, hrlxS, hfs, hdisj, hRel, hRlx⟩ : ∃ rel ss,
      (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw new cx'.mem ss ∧ ¬ g.Claimed (l, tw)) ∧
      (rel = false → ss = [] ∧ Pred.Pure (g.rel l) new) ∧ FreshSlots c.mem.last ss ∧
      (∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key) ∧
      (pl.rel l new = true → l ∉ pl.gives l new ∧ Res.prod (ss.map (·.res)) = pl.give l new σ.cl σ.r) ∧
      (pl.rel l new = false → Res.prod (ss.map (·.res)) = Res.unit) := by
    cases hrl : pl.rel l new with
    | false =>
      exact ⟨false, [], fun h => absurd h Bool.false_ne_true, fun _ => ⟨rfl, hgr ▸ hpure hrl⟩, FreshSlots.nil _,
        fun _ _ _ h => absurd h List.not_mem_nil, fun h => absurd h Bool.false_ne_true, fun _ => rfl⟩
    | true =>
      obtain ⟨-, himp, hgl, hob⟩ := hrel hrl
      have hnotown : tw ∉ cx₁.prom := fun htp => himp (hgr ▸ hown htp)
      obtain ⟨hm', rfl⟩ : cx'.mem = (cx₁.mem.append ⟨l, new, tid⟩).1 ∧ tw = cx₁.mem.last + 1 := by
        rcases hev.cases with ⟨-, htp, -⟩ | h'
        · exact absurd htp hnotown
        · exact h'
      have hwb := writeBound_of_writeOk A tid (writeSuccs_at A tid hc'0 hev').1 hvle
      rw [hm1c] at hwb
      obtain ⟨htrw, hat⟩ := hev.tr tr rfl
      have hadj : AdjAt tid c g l tr (c.mem.last + 1) :=
        adjAt_of_ctx (cx := fenceOptCtx A cx) h.ht (hm0.trans h.mem) (hp0.trans h.prom)
          (fenceOpt_inv tid hi A.rmwFence .sy).1.own hx (by rw [← hm1c]; exact hat) hn'
      have hP := hob (by rw [← hm1c]; exact htrw) hwb hadj
      have hP' : (g.rel l).P new cx'.mem (cx₁.mem.last + 1) (pl.give l new σ.cl σ.r) := by
        rw [hgr, hm', hm1c]; exact hP
      obtain ⟨ss, hss, hprod⟩ := Erase.slotsFor E hP'
      rw [total_withThread] at hss
      have hncl : ¬ g.Claimed (l, cx₁.mem.last + 1) :=
        Erase.not_claimed_fresh E (show cx₁.mem.last < cx₁.mem.last + 1 by omega_t)
      have hfs : FreshSlots c.mem.last ss :=
        hev.freshSlots (by rw [hm1c]; exact Nat.le_refl _) hss.key (fun htp => absurd htp hnotown)
      have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he => by
        have h1 := h.erase.slot_key_le hs
        have h2 := hfs s' hs'
        rw [he] at h1; omega_t
      exact ⟨true, ss, fun _ => ⟨hss, hncl⟩, fun h => Bool.noConfusion h, hfs, hdisj, fun _ => ⟨hgl, hprod⟩,
        fun h => Bool.noConfusion h⟩
  have hRes : ∀ C : Res, ((pl.after l new tw σ.cl σ.r).op C).op (Res.prod (ss.map (·.res))) =
      (r.op C).addW l (new, tw) := fun C => by
    rw [hr]; exact pl.afterC_op_give hok.1 hRel hRlx
  -- the erasure and reach obligations, claiming or not, with `acqLe`
  obtain ⟨g', E', hR, hmw, hgle, hpend⟩ : ∃ g',
      ErAt rF (fun _ => True) c t tid
        ((pl.after l new tw σ.cl σ.r).op (Res.prod ((claimSlotsC A k σ.vs g l tr).map (·.res)))) g' cx' ∧
      RStep c.mem.last r g ((pl.after l new tw σ.cl σ.r).op (Res.prod ((claimSlotsC A k σ.vs g l tr).map (·.res))))
        g' (rmwAfter A k false l cx') ∧
      (∀ y, mayWrite ((pl.after l new tw σ.cl σ.r).op (Res.prod ((claimSlotsC A k σ.vs g l tr).map (·.res)))) g' y →
        mayWrite r g y) ∧ g.Le g' ∧ g'.pend = g.pend := by
    by_cases hk : ClaimOk A k σ.vs l tr
    · rw [claimSlotsC_of_ok hk]
      have hres := hRes (Res.prod ((claimedSlots g l tr).map (·.res)))
      exact ⟨_, E.rmw hn hi1 hev hrd hseen hnp hposr hrelS hrlxS hres (fun _ _ _ h => absurd trivial h),
        RStep.rmw hfs hres (fun _ => htrC hk), fun y hy => mayWrite_rmw_le hres rfl hdisj hy,
        Ghost.Le.rmwGhost g l tr tw rel ss, rfl⟩
    · rw [claimSlotsC_of_not hk]
      have hres := hRes Res.unit
      rw [Res.op_unit, Res.op_unit] at hres
      simp only [List.map_nil, Res.prod_nil, Res.op_unit]
      exact ⟨_, E.store hn hi1 hev hpd hposr hrelS hrlxS hres (fun _ _ _ h => absurd trivial h),
        RStep.store hfs hres _, fun y hy => mayWrite_store_le hres rfl hdisj hy,
        Ghost.Le.storeGhost g l tw rel ss, rfl⟩
  obtain ⟨hm4, hp4⟩ := rmwAfter_memProm (A := A) k false l cx'
  have hwl : ∀ w, WrittenCx c t cx' w → w.loc = l := fun w hw => writtenCx_loc hm1c hp1t hev hw
  have hnpd' : ∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend := fun ts hts hpd' =>
    hn' ts (hprom' ts (hp4 ▸ hts)) (by rw [← hpend]; exact hpd')
  refine .inr ⟨_, _, { σ with
      snap := snapAfter tid c cxe₂, vs := (rmwAfter A k false l cxe₂).views
      r := (pl.after l new tw σ.cl σ.r).op (Res.prod ((claimSlotsC A k σ.vs g l tr).map (·.res))), g := g
      seen := seenAfter A (A.rmwKind k).loadKind σ g l tr, fencedR := false, fencedW := false },
    ⟨c, (tr, old, cxe₁), h.anchorOk, hx'0, rfl, rfl, rfl, rfl, rfl,
      .inr ⟨new, cxe₂, tw, hop, hc'0, hev', hov, hpl, rfl, rfl, ⟨σ.cl, id, rfl⟩, hun⟩⟩, E', hR,
    ⟨snapLe_snapAfter h.ht (hcl2.mem.trans hm4.symm) (hcl2.prom.trans hp4.symm),
      hgle, ⟨_, hcl2.rmwAfter k false l, rfl⟩, .inl ⟨rfl, hnpd'⟩, fun hc0 => h.cl hc0.1,
      ⟨fun e => absurd e Bool.false_ne_true, fun e => absurd e Bool.false_ne_true⟩⟩,
    WpPath.congr ⟨hgle, fun _ h _ => by rw [hpend]; exact h, fun _ h => by rw [← hpend]; exact h, hmw,
      fun w hw => (hwl w hw) ▸ hposr⟩ hm4 hp4,
    by rw [hm4, ← hm1c]; exact hev.last_le, hnpd', rfl⟩

/-- **Claim-conditional RMW transport at an in-flight release**
(`pf = some (l, v)`): the write fulfilling the pending promise `ts` performs
the prepaid write and, for a claiming RMW, claims the message read; every
other write overtakes `ts`. No give-away side condition. For `RmwOkCAdj`
(moved here from `EnvG/AdjSpikeLink.lean`; the in-flight
fulfilment uses only the unguarded conjuncts). The generic form:
`NodeRel.rmwRelC` is its instance. -/
theorem NodeRel.rmwRelCAdj (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {l : Loc} {v : Val}
    (hst : StartS tid c t g (some (l, v)))
    {k : RmwKind} {op : Val → Option Val} (hok : RmwOkCAdj A tid pl σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOutC A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
      RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') ∧
      WpPath c tid t r g r' g' (rmwAfter A k false l cx') ∧ c.mem.last ≤ (rmwAfter A k false l cx').mem.last ∧
      (∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl := by
  obtain ⟨ts, hts, hpts, hgts, habove⟩ := hst.some l v rfl
  obtain ⟨P, hP, hr, h6⟩ : ∃ P : Prop, (σ.cl → P) ∧ r = pl.after l v ts P σ.r ∧
      ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts := by
    rcases h.res with ⟨-, hn'⟩ | ⟨ts₁, l₀, v₀, h1, h2, h3, ⟨P, hP, h5⟩, h6⟩
    · exact absurd hpts (hn' ts hts)
    · obtain rfl := h6 ts hts hpts
      rw [hgts] at h3
      simp only [Option.some.injEq, Msg.mk.injEq] at h3
      obtain ⟨rfl, rfl, -⟩ := h3
      exact ⟨P, hP, h5, h6⟩
  obtain ⟨tr, old, cx₁⟩ := x
  obtain ⟨cxe₁, hx', hc1⟩ := (h.ctx.fenceOpt (A := A)).read hx
  have hx'0 : (tr, old, cxe₁) ∈ readSuccs A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l
      false := hx'
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
  simp only at hm1 hp1 hop hc E ⊢
  have hm1c : cx₁.mem = c.mem := hm1.trans (hm0.trans h.mem)
  have hp1t : cx₁.prom = t.prom := hp1.trans (hp0.trans h.prom)
  have hn := lt_size_of_get? h.ht
  have hi1 : cx₁.Inv tid := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
  have hex : cxe₁.loadViews.getLastD 0 ≤ cx₁.loadViews.getLastD 0 :=
    Nat.le_trans (Rel2.getLastD hc1.sim.rel.loadViews 0 0 (Nat.zero_le _)) (idUpTo_fv_le _ _)
  have hexb : cx₁.loadViews.getLastD 0 ≤ cx₁.mem.last := getLastD_le' hc1.sim.bnd.loadViews
  obtain ⟨cxe₂, tw, hc', hev, hev', hcl2⟩ := hc1.write hi1 (ivLe_envIv _ iv) hc1.sim.ivb hex hexb hc
  have hc'0 : cxe₂ ∈ writeSuccs A tid iv0 cxe₁ (A.rmwKind k).storeKind true l new (some tr)
      (cxe₁.loadViews.getLastD 0) := hc'
  by_cases hov : cxe₂.Overtaken
  · exact .inl (hcl2.overtaken hov)
  have hts1 : ts ∈ cx₁.prom := by rw [hp1t]; exact hts
  have hgts1 : cx₁.mem.get? ts = some ⟨l, v, tid⟩ := by rw [hm1c]; exact hgts
  by_cases hnpd : tw ∉ g.pend
  · -- any other outcome overtakes the pending promise
    have hpd := hnpd
    refine .inl (overtaken_of_inflight' hc hev hts1 hgts1 ?_)
    rcases hev.cases with ⟨-, htp, hget⟩ | ⟨-, rfl⟩
    · have hne : tw ≠ ts := fun e => hpd (e ▸ hpts)
      exact habove tw (hp1t ▸ htp) hne _ (hm1c ▸ hget) rfl
    · have := cx₁.mem.last_le_of_get?_eq_some hgts1
      omega_t
  -- fulfilling the pending promise
  have hpd : tw ∈ g.pend := Classical.not_not.mp hnpd
  obtain ⟨hmeq, htp, hget⟩ : cx'.mem = cx₁.mem ∧ tw ∈ cx₁.prom ∧ cx₁.mem.get? tw = some ⟨l, new, tid⟩ := by
    rcases hev.cases with h' | ⟨-, rfl⟩
    · exact h'
    · have h1 := h.erase.pend_le hpd; rw [← hm1c] at h1; omega_t
  obtain rfl : tw = ts := h6 tw (hp1t ▸ htp) hpd
  obtain rfl : v = new := by
    rw [hgts1] at hget
    simp only [Option.some.injEq, Msg.mk.injEq] at hget
    exact hget.2.1
  have hprom' : ∀ ts ∈ cx'.prom, ts ∈ t.prom := fun ts hts => by
    rw [hev.prom] at hts; exact hp1t ▸ List.mem_of_mem_erase hts
  obtain ⟨-, -, hrd, hseen⟩ := rmw_event A tid iv hx hi hc
  obtain ⟨hrdAt, -⟩ := readAt_rmw hx'0
  obtain ⟨-, hrel⟩ := hok.2 c g tr old v h.anchorOk hrdAt hop
  have htrC : ClaimOk A k σ.vs l tr → tr ≤ (rmwAfter A k false l cx').views.wfloor := fun hcond => by
    rcases hcond with hk | ⟨hk, hnf⟩
    · exact rmw_tr_le_wfloor_acqRel hc (by rw [hk]; rfl)
    · have hfw : ∀ f, (fenceOptCtx A (envCtx tid σ.vs c)).views.getFwd l = some f → f.time ≠ tr := by
        intro f hf ht
        rw [fenceOptCtx_views, rmwReadViews_getFwd] at hf
        exact hnf ⟨f, hf, ht⟩
      exact Nat.le_trans (rmw_tr_le_wfloor_acq hx'0 hk hfw hc'0 k false) (hcl2.rmwAfter k false l).wfloor
  have hqr : 0 < (r.wr l).q := by
    rw [hr]; unfold Plan.after
    cases hrl : pl.rel l v with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, Res.addW_q]; exact hok.1
    | true =>
      simp only [↓reduceIte, Res.addW_q]
      exact pl.keep_q_pos (hrel hrl).2.2.1 _ _ hok.1
  have hqa : 0 < ((pl.after l v tw P σ.r).wr l).q := hr ▸ hqr
  have hnp : ∀ p ∈ cx₁.prom, p ∈ g.pend → ((l, tr), p) ∉ g.claims := fun p hp' _ hcl =>
    E.claimFulf _ p hcl ⟨tid, _, ErAt.get? hn, hp'⟩
  obtain ⟨htrw, hat⟩ := hev.tr tr rfl
  have hun' : ¬ g.Claimed (l, tr) :=
    Erase.not_claimed_noclaim E (ErAt.get? hn) (hev.writeAt hi1) rfl htrw hrd hat hnp hseen
  have E1 : ErAt rF (fun _ => True) c t tid r (unpend g tw) cx' := ErAt.fulfilPend E hn hi1 hev hpd
  -- erasure and reach: fulfil, then (claiming RMWs only) claim the message read
  obtain ⟨g', E', hR, hmw, hgle, hpendg⟩ : ∃ g',
      ErAt rF (fun _ => True) c t tid
        ((pl.after l v tw P σ.r).op (Res.prod ((claimSlotsC A k σ.vs g l tr).map (·.res)))) g' cx' ∧
      RStep c.mem.last r g ((pl.after l v tw P σ.r).op (Res.prod ((claimSlotsC A k σ.vs g l tr).map (·.res))))
        g' (rmwAfter A k false l cx') ∧
      (∀ y, mayWrite ((pl.after l v tw P σ.r).op (Res.prod ((claimSlotsC A k σ.vs g l tr).map (·.res)))) g' y →
        mayWrite r g y) ∧ g.Le g' ∧ ∀ ts', ts' ∈ g'.pend ↔ ts' ∈ g.pend ∧ ts' ≠ tw := by
    by_cases hk : ClaimOk A k σ.vs l tr
    · rw [claimSlotsC_of_ok hk]
      have hreq : (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (v, tw) =
          (pl.after l v tw P σ.r).op (Res.prod ((claimedSlots g l tr).map (·.res))) := by
        rw [hr]; exact Res.addW_op_claim hqa (pl.after_addW hqa)
      have hno := ErAt.not_outstanding_fulfilled E hn hi1 hev hget
      have E2 := Erase.claimPend (tid := tid) (g := unpend g tw) E1 (by rw [Config.withThread_size]; exact hn) htrw
        (show cx'.mem.get? tw = some ⟨l, v, tid⟩ by rw [hmeq]; exact hget) rfl hno
        (fun ts w' h1 h2 hw' hl' => atomic_between hat hrd h1 h2 (by rw [← hmeq]; exact hw') hl') hun'
        (by rw [setRes_self]; exact hqr)
      simp only [setRes_setRes, setRes_self] at E2
      have hg' : rmwGhost (unpend g tw) l tr tw false [] = unpend (rmwGhost g l tr tw false []) tw := rfl
      have hcs : claimedSlots (unpend g tw) l tr = claimedSlots g l tr := rfl
      rw [hg', hcs, hreq] at E2
      have hR1 : RStep c.mem.last r g ((pl.after l v tw P σ.r).op (Res.prod ((claimedSlots g l tr).map (·.res))))
          (rmwGhost g l tr tw false []) (rmwAfter A k false l cx') :=
        RStep.rmw (FreshSlots.nil _) (by rw [List.map_nil]; exact (Res.op_unit _).trans hreq.symm) (fun _ => htrC hk)
      refine ⟨_, E2, RStep.trans hR1 (RStep.unpend tw _) (Nat.le_refl _), fun y hy => ?_,
        ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩, fun ts' => mem_unpend_pend⟩
      rw [← hreq] at hy
      exact SpinCommon.mayWrite_claim (mayWrite_unpend hy)
    · rw [claimSlotsC_of_not hk]
      simp only [List.map_nil, Res.prod_nil, Res.op_unit]
      rw [← hr]
      exact ⟨_, E1, RStep.unpend tw _, fun y hy => mayWrite_unpend hy, Ghost.Le.unpend g tw,
        fun ts' => mem_unpend_pend⟩
  obtain ⟨hm4, hp4⟩ := rmwAfter_memProm (A := A) k false l cx'
  have hwl : ∀ w, WrittenCx c t cx' w → w.loc = l := fun w hw => writtenCx_loc hm1c hp1t hev hw
  have hnotin : tw ∉ cx'.prom := by
    rw [hev.prom]; exact fun hm => ((List.Nodup.mem_erase_iff hi1.nodup).mp hm).1 rfl
  have hnototh : ∀ (i : Nat) (t' : Thread I), i ≠ tid → c.threads[i]? = some t' → tw ∉ t'.prom := by
    intro i t' hne hi' htp'
    obtain ⟨w', hw', htid⟩ := h.erase.promWf i t' hi' tw htp'
    rw [hgts] at hw'
    cases hw'
    exact hne htid.symm
  have hnopd : ∀ ts' ∈ (rmwAfter A k false l cx').prom, ts' ∉ g'.pend := by
    intro ts' hts' hpd'
    obtain ⟨h1, h2⟩ := (hpendg ts').mp hpd'
    exact h2 (h6 ts' (hprom' ts' (hp4 ▸ hts')) h1)
  refine .inr ⟨_, _, { σ with
      snap := snapAfter tid c cxe₂, vs := (rmwAfter A k false l cxe₂).views
      r := (pl.after l v tw P σ.r).op (Res.prod ((claimSlotsC A k σ.vs g l tr).map (·.res))), g := g
      seen := seenAfter A (A.rmwKind k).loadKind σ g l tr, fencedR := false, fencedW := false },
    ⟨c, (tr, old, cxe₁), h.anchorOk, hx'0, rfl, rfl, rfl, rfl, rfl,
      .inr ⟨v, cxe₂, tw, hop, hc'0, hev', hov, fun _ => .inr hpd, rfl, rfl, ⟨P, hP, rfl⟩, hun'⟩⟩, E', hR,
    ⟨snapLe_snapAfter h.ht (hcl2.mem.trans hm4.symm) (hcl2.prom.trans hp4.symm),
      hgle, ⟨_, hcl2.rmwAfter k false l, rfl⟩, .inl ⟨rfl, hnopd⟩, fun hc0 => h.cl hc0.1,
      ⟨fun e => absurd e Bool.false_ne_true, fun e => absurd e Bool.false_ne_true⟩⟩,
    WpPath.congr ⟨hgle, fun ts' hts' ho => ?_, fun ts' hts' => ((hpendg ts').mp hts').1, hmw,
      fun w hw => (hwl w hw) ▸ hqr⟩ hm4 hp4,
    by rw [hm4, ← hm1c]; exact hev.last_le, hnopd, rfl⟩
  refine (hpendg ts').mpr ⟨hts', ?_⟩
  rintro rfl
  rcases ho with ho | ⟨i, t', hne, hi', ho⟩
  · exact hnotin ho
  · exact hnototh i t' hne hi' ho

/-- **Claim-conditional RMW transport without a release in flight, any
kind.** -/
theorem NodeRel.rmwC' (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : RmwKind} {l : Loc} {op : Val → Option Val} (hok : RmwOkC A tid pl σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOutC A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
      RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') ∧
      WpPath c tid t r g r' g' (rmwAfter A k false l cx') ∧ c.mem.last ≤ (rmwAfter A k false l cx').mem.last ∧
      (∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl :=
  h.rmwCAdj' hnp0 hok.toCAdj hx hop hc E hi

/-- **Claim-conditional RMW transport at an in-flight release**
(`pf = some (l, v)`): the write fulfilling the pending promise `ts` performs
the prepaid write and, for a claiming RMW, claims the message read; every
other write overtakes `ts`. No give-away side condition. -/
theorem NodeRel.rmwRelC (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {l : Loc} {v : Val}
    (hst : StartS tid c t g (some (l, v)))
    {k : RmwKind} {op : Val → Option Val} (hok : RmwOkC A tid pl σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOutC A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
      RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') ∧
      WpPath c tid t r g r' g' (rmwAfter A k false l cx') ∧ c.mem.last ≤ (rmwAfter A k false l cx').mem.last ∧
      (∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl :=
  h.rmwRelCAdj hst hok.toCAdj hx hop hc E hi

end Transport

/-! ## The instance and the link theorem -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The per-node transport of `EnvGC`** (`nodeSimS2_envG` without the
give-away side condition). -/
theorem nodeSimS2_envGC {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf) :
    NodeSimS2 A tid iv rF (fun _ => True) c t (EnvGC I A tid pl) (LokS pf) (SokS pf) (RokR pf) (LokS pf)
      (fun σ r g cx => PreS tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) where
  pre_post := (nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst).pre_post
  fence_pre := (nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst).fence_pre
  fence_post := (nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst).fence_post
  load := (nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst).load
  store := (nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst).store
  rmw := by
    rintro k addr n op σ r g cx hR ⟨h, rfl, rfl⟩ hok x hx
    rcases hR with hpf | ⟨v, hpf, htot⟩
    · refine ⟨fun hop => ?_, fun new hop cx' hc E hi _ => ?_⟩
      · obtain ⟨σ', ho, hp⟩ := h.rmwFail hx hop
        obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
        obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
        obtain ⟨hm2, hp2⟩ := fenceOptCtx_memProm (A := A) x.2.2
        have hm : (fenceOptCtx A x.2.2).mem = c.mem := hm2.trans (hm1.trans (hm0.trans h.mem))
        have hpr : (fenceOptCtx A x.2.2).prom = t.prom := hp2.trans (hp1.trans (hp0.trans h.prom))
        exact ⟨σ', ho.toC_none hop, hp, WpPath.refl hm hpr, by rw [hm]; exact Nat.le_refl _,
          fun ts hts => hst.none hpf ts (hpr ▸ hts), fun hne => absurd hpf hne⟩
      · rcases h.rmwC' (hst.none hpf) hok hx hop hc E hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, -⟩
        · exact .inl ho
        · exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, fun hne => absurd hpf hne⟩
    · subst hpf
      refine ⟨fun hop => absurd hop (htot _), fun new hop cx' hc E hi _ => ?_⟩
      rcases h.rmwRelC hst hok hx hop hc E hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, hcl⟩
      · exact .inl ho
      · exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, fun _ hc0 => hcl ▸ h.cl hc0⟩

/-- **Link theorem 1 for `EnvGC`**: `treeJ_envG_eraseWPRDSR` without the
give-away side condition. -/
theorem treeJ_envGC_eraseWPRDSR {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDS2 (nodeSimS2_envGC (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀)
      (cl₀ := cl₀) (rS := rS) hst) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvGC I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDS2 _ hW ⟨h, rfl, rfl⟩ ha

/-- **Link theorem 1 for `EnvGC` at an instruction's start**. -/
theorem treeJ_envGC_eraseWPRDSR_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDS2 (nodeSimS2_envGC (A := A) (pl := pl) (iv := instrViews t d) (rF := rF)
      (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hst) Q).W tree σ)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvGC I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envGC_eraseWPRDSR hst hW (hrel.toNodeRel rF d E hm) ha

end Link

end Kraken.Promising.SLR.EnvG
