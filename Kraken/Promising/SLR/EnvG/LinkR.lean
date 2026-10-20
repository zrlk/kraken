/-
Whole-thread environment (`EnvG`), release-kind RMWs, part 2: **the link with
release-kind RMWs** (lifts the phase-1 limit "releases are stores",
additively beside `EnvG/LinkS.lean`). ISA-neutral.

`LinkS.lean`'s link admits an RMW node only with no release in flight and of
non-release kind (`RokS`). Here (side conditions `RokR`, on the RMW's kind,
location and operation, through `SingleAccessS2`/`NodeSimS2`,
`EnvG/TreeLinkS.lean`):

- `pf = none` (no own pending promise): **any** RMW (`NodeRel.rmwS'`). A
  written value that is a planned release is fresh (impure, so it fulfils no
  old non-pending promise, and none is pending); its slots carry what
  `RmwOk`'s release obligation gives away (`pl.give l new (σ.r ⋅ C)`, `C` the
  claimed update slots), and the write claims as any RMW does
  (`ErAt.rmw` at `rel = true`).
- `pf = some (l, v)` (the RMW's write is the in-flight prepaid promise
  `ts`): the RMW writes `l` and its operation never fails (`∀ x, op x ≠
  none`: a failing CAS would leave the pending promise outstanding and alive
  after the instruction, which phase 1 cannot carry; **phase-1 limit**,
  `casal`/x64 `cmpxchg` releases are outside). `NodeRel.rmwRelS`:
  - the write fulfilling `ts` (so `new = v`) is `ErAt.fulfilPend` followed by
    the claim of the message read (`Erase.claimPend`: the claim is made when
    the write is performed, never at promise time, `Erase.claimFulf`), as in
    `EvTree.eraseWPR_rmw_pendClaim`; reach: `RStep.rmw` (the claim floor from
    `RmwOk`'s `ClaimOk`) then `RStep.unpend`;
  - every other write overtakes `ts` (`overtaken_of_inflight'`: the
    variant of `overtaken_of_inflight` for a pending message of any value);
  - the actual resource after the fulfilment, `(pl.after l v ts σ.r ⋅ C) ⊎
    {(v, ts)}`, is the env's `pl.afterRmw l v tr ts g σ.r`
    (`Plan.after_op_claim`), for a planned release provided the claimed
    slots carry nothing at the given-away locations (`RelRmwGiveOk`,
    `EnvG/PrepayRmw.lean`) and the release is whole (`Plan.Whole`, from
    `RmwOk`: F1's splits are for store releases only), with the split
    knowledge `P` the prepay recorded in `Inflight`.
- `PostS`'s `cl` clause (`pf ≠ none → cl₀ → σ.cl`) holds at the RMW node as
  at the store: an RMW outcome keeps the env's `cl`.

Contents: the resource lemmas, `overtaken_of_inflight'`,
`mayWrite_rmwRel_le`, `NodeRel.rmwS'`, `NodeRel.rmwRelS`, `RokR`,
`nodeSimS2_envG`, `treeJ_envG_eraseWPRDSR(_start)`.

Phase 1 otherwise unchanged: single-access trees, read-side acquire only.
-/
import Kraken.Promising.SLR.EnvG.PrepayRmw

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Resource lemmas -/

/-- `Res.drop` distributes over composition. -/
theorem Res.drop_op (L : List Loc) (a b : Res) : Res.drop L (a.op b) = (Res.drop L a).op (Res.drop L b) := by
  apply Res.ext
  · funext x
    simp only [Res.op, Res.drop]
    split
    · exact (Perm.op_unit _).symm
    · rfl
  · funext x ι
    simp only [Res.op, Res.drop]
    split <;> omega

/-- A resource with nothing at `L` is unchanged by dropping `L`. -/
theorem Res.drop_of_only_unit {L : List Loc} {C : Res} (h : Res.only L C = Res.unit) : Res.drop L C = C := by
  apply Res.ext
  · funext x
    simp only [Res.drop]
    split
    · next hx =>
      have := congrArg (fun r : Res => r.wr x) h
      simp only [Res.only, hx, ↓reduceIte, Res.unit] at this
      exact this.symm
    · rfl
  · funext x ι
    simp only [Res.drop]
    split
    · next hx =>
      have := congrArg (fun r : Res => r.acq x ι) h
      simp only [Res.only, hx, ↓reduceIte, Res.unit] at this
      exact this.symm
    · rfl

/-- Adding a write twice is adding it once (with a positive fraction). -/
theorem Res.addW_addW_self {r : Res} {x : Loc} {p : Val × Time} (hq : 0 < (r.wr x).q) :
    (r.addW x p).addW x p = r.addW x p :=
  Res.addW_of_mem ((Res.addW_X_self _ _ _ _).mpr (.inr ⟨hq, rfl⟩))

/-- **The resource after an in-flight RMW's fulfilment is the env's**: the
actual resource after the prepay (`pl.after l v ts rv`), with the claimed
slots `C` and the (already present) write, is `Plan.after` of `rv ⋅ C`; for a
planned release provided it is whole (`Plan.Whole`, no split: `RmwOk`'s
phase-1 limit) and `C` has nothing at the given-away locations. The split's
knowledge `cl` is the same on both sides. -/
theorem Plan.after_op_claim (pl : Plan) {l : Loc} {v : Val} {ts : Time} {cl : Prop} {rv C : Res}
    (hq : 0 < (rv.wr l).q) (hl : pl.rel l v = true → l ∉ pl.gives l v) (hs : pl.rel l v = true → pl.Whole l v)
    (hC : pl.rel l v = true → Res.only (pl.gives l v) C = Res.unit) :
    ((pl.after l v ts cl rv).op C).addW l (v, ts) = pl.after l v ts cl (rv.op C) := by
  unfold Plan.after
  cases hrl : pl.rel l v with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Res.addW_op _ _ hq]
    exact Res.addW_addW_self (Res.pos_op.mpr (.inl hq))
  | true =>
    simp only [↓reduceIte]
    have hq' : 0 < ((pl.keep l v cl rv).wr l).q := by rw [pl.keep_wr_self (hl hrl) (hs hrl)]; exact hq
    have hk : pl.keep l v cl (rv.op C) = (pl.keep l v cl rv).op C := by
      rw [pl.keep_of_whole (hs hrl), pl.keep_of_whole (hs hrl)]
      rw [Res.drop_op, Res.drop_of_only_unit (hC hrl)]
    rw [hk, Res.addW_op _ _ hq']
    exact Res.addW_addW_self (Res.pos_op.mpr (.inl hq'))

/-! ## Overtaking and `acqLe` -/

/-- **Every write of the in-flight location other than the fulfilment
overtakes the pending promise** (`overtaken_of_inflight` for a pending
message of any value: an RMW writes `op old`). -/
theorem overtaken_of_inflight' {A : Arch} {tid : Nat} {iv : InstrViews} {cx cx' : Ctx} {k : StoreKind}
    {xcl : Bool} {l : Loc} {v v' : Val} {trOpt : Option Time} {extra : View} {tw ts : Time}
    (hc : cx' ∈ writeSuccs A tid iv cx k xcl l v trOpt extra) (hev : WriteEv tid cx cx' l v trOpt tw)
    (hts : ts ∈ cx.prom) (hget : cx.mem.get? ts = some ⟨l, v', tid⟩) (hlt : ts < tw) : cx'.Overtaken := by
  have hne : ts ≠ tw := by omega_t
  refine ⟨ts, by rw [hev.prom]; exact (List.mem_erase_of_ne hne).mpr hts, ⟨l, v', tid⟩, ?_,
    Nat.le_trans (Nat.le_of_lt hlt) (writeSuccs_coh_tw' hc hev)⟩
  rcases hev.cases with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm]; exact hget
  · rw [hm, Memory.get?_append_of_le _ _ _ (cx.mem.last_le_of_get?_eq_some hget)]; exact hget

/-- **`acqLe` for a release RMW**: the claimed update slots (acquirable by
everyone) and the release's slots on a fresh key. -/
theorem mayWrite_rmwRel_le {g : Ghost} {r r' R : Res} {x : Loc} {tr tw : Time} {p : Val × Time} {ss : List Slot}
    (hres : r'.op R = (r.op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x p)
    (hprod : Res.prod (ss.map (·.res)) = R) (hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key) {y : Loc}
    (h : mayWrite r' (rmwGhost g x tr tw true ss) y) : mayWrite r g y := by
  have h' : mayWrite r' (storeGhost (rmwGhost g x tr tw false []) x tw true ss) y := by
    have e : (rmwGhost g x tr tw true ss).u = (storeGhost (rmwGhost g x tr tw false []) x tw true ss).u := by
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

/-! ## The RMW transports -/

section Transport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}

/-- **RMW transport without a release in flight, any kind** (`NodeRel.rmwS`
without `¬ effRelRmw`): a planned-release written value is a fresh release
whose slots carry `RmwOk`'s give-away. -/
theorem NodeRel.rmwS' (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : RmwKind} {l : Loc} {op : Val → Option Val} (hok : RmwOk A tid pl σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOut A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
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
  obtain ⟨hcond, hpure, hrel⟩ := hok.2 c g tr old new h.anchorOk hrdAt hop
  have htr : claimedSlots g l tr ≠ [] → tr ≤ (rmwAfter A k false l cx').views.wfloor := fun hne => by
    rcases hcond hne with hk | ⟨hk, hnf⟩
    · exact rmw_tr_le_wfloor_acqRel hc (by rw [hk]; rfl)
    · have hfw : ∀ f, (fenceOptCtx A (envCtx tid σ.vs c)).views.getFwd l = some f → f.time ≠ tr := by
        intro f hf ht
        rw [fenceOptCtx_views, rmwReadViews_getFwd] at hf
        exact hnf ⟨f, hf, ht⟩
      exact Nat.le_trans (rmw_tr_le_wfloor_acq hx'0 hk hfw hc'0 k false) (hcl2.rmwAfter k false l).wfloor
  -- an own outstanding promise fulfilled here is not pending, so its value is pure
  have hown : tw ∈ cx₁.prom → Pred.Pure (g.rel l) new := fun htp => by
    rcases hev.cases with ⟨-, -, hget⟩ | ⟨-, rfl⟩
    · exact Erase.pure_of_own h.erase h.ht (hp1t ▸ htp) hpd (hm1c ▸ hget)
    · obtain ⟨w, hw, -⟩ := hi1.prom _ htp
      have := cx₁.mem.last_le_of_get?_eq_some hw
      omega_t
  have hpl : pl.rel l new = true → tw ∉ ownProm tid c ∨ tw ∈ g.pend := fun hrl =>
    .inl fun htp => (hrel hrl).2.1 (hgr ▸ hown (by rw [hp1t, ← ownProm_eq h.ht]; exact htp))
  -- the erasure and reach obligations, per kind of written value, with `acqLe`
  obtain ⟨rel, ss, E', hR, hmw⟩ : ∃ rel ss, ErAt rF (fun _ => True) c t tid (pl.afterRmw l new tr tw g σ.cl σ.r)
      (rmwGhost g l tr tw rel ss) cx' ∧
      RStep c.mem.last r g (pl.afterRmw l new tr tw g σ.cl σ.r) (rmwGhost g l tr tw rel ss) (rmwAfter A k false l cx') ∧
      (∀ y, mayWrite (pl.afterRmw l new tr tw g σ.cl σ.r) (rmwGhost g l tr tw rel ss) y → mayWrite r g y) := by
    cases hrl : pl.rel l new with
    | false =>
      have hres : (pl.afterRmw l new tr tw g σ.cl σ.r).op (Res.prod (([] : List Slot).map (·.res))) =
          (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (new, tw) := by
        simp [Plan.afterRmw, Plan.after, hrl, Res.op_unit, hr]
      refine ⟨false, [], E.rmw hn hi1 hev hrd hseen hnp hposr (rel := false) (fun h => absurd h Bool.false_ne_true)
        (fun _ => ⟨rfl, hgr ▸ hpure hrl⟩) hres (fun _ _ _ h => absurd trivial h),
        RStep.rmw (B := c.mem.last) (tw := tw) (rel := false) (FreshSlots.nil _) hres htr, fun y hy => ?_⟩
      have e : pl.afterRmw l new tr tw g σ.cl σ.r =
          (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (new, tw) := by
        simp [Plan.afterRmw, Plan.after, hrl, hr]
      rw [e] at hy
      exact SpinCommon.mayWrite_claim hy
    | true =>
      obtain ⟨-, himp, hgl, hwh, hob⟩ := hrel hrl
      have hnotown : tw ∉ cx₁.prom := fun htp => himp (hgr ▸ hown htp)
      obtain ⟨hm', rfl⟩ : cx'.mem = (cx₁.mem.append ⟨l, new, tid⟩).1 ∧ tw = cx₁.mem.last + 1 := by
        rcases hev.cases with ⟨-, htp, -⟩ | h'
        · exact absurd htp hnotown
        · exact h'
      have hwb := writeBound_of_writeOk A tid (writeSuccs_at A tid hc'0 hev').1 hvle
      rw [hm1c] at hwb
      obtain ⟨htrw, -⟩ := hev.tr tr rfl
      have hP := hob (by rw [← hm1c]; exact htrw) hwb
      have hP' : (g.rel l).P new cx'.mem (cx₁.mem.last + 1)
          (pl.give l new σ.cl (σ.r.op (Res.prod ((claimedSlots g l tr).map (·.res))))) := by
        rw [hgr, hm', hm1c]; exact hP
      obtain ⟨ss, hss, hprod⟩ := Erase.slotsFor E hP'
      rw [total_withThread] at hss
      have hncl : ¬ g.Claimed (l, cx₁.mem.last + 1) :=
        Erase.not_claimed_fresh E (show cx₁.mem.last < cx₁.mem.last + 1 by omega_t)
      have hres : (pl.afterRmw l new tr (cx₁.mem.last + 1) g σ.cl σ.r).op (Res.prod (ss.map (·.res))) =
          (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (new, cx₁.mem.last + 1) := by
        rw [hprod, hr]; simp only [Plan.afterRmw, Plan.after, hrl, ↓reduceIte, Plan.give]
        exact pl.keep_op_give hgl _ _ _
      have hfs : FreshSlots c.mem.last ss :=
        hev.freshSlots (by rw [hm1c]; exact Nat.le_refl _) hss.key (fun htp => absurd htp hnotown)
      have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he => by
        have h1 := h.erase.slot_key_le hs
        have h2 := hfs s' hs'
        rw [he] at h1; omega_t
      exact ⟨true, ss, E.rmw hn hi1 hev hrd hseen hnp hposr (rel := true) (fun _ => ⟨hss, hncl⟩)
          (fun h => Bool.noConfusion h) hres (fun _ _ _ h => absurd trivial h),
        RStep.rmw hfs hres htr, fun y hy => mayWrite_rmwRel_le hres rfl hdisj hy⟩
  obtain ⟨hm4, hp4⟩ := rmwAfter_memProm (A := A) k false l cx'
  have hwl : ∀ w, WrittenCx c t cx' w → w.loc = l := fun w hw => writtenCx_loc hm1c hp1t hev hw
  refine .inr ⟨_, _, { σ with
      snap := snapAfter tid c cxe₂, vs := (rmwAfter A k false l cxe₂).views
      r := pl.afterRmw l new tr tw g σ.cl σ.r, g := g
      seen := seenAfter A (A.rmwKind k).loadKind σ g l tr, fencedR := false, fencedW := false },
    ⟨c, (tr, old, cxe₁), h.anchorOk, hx'0, rfl, rfl, rfl, rfl, rfl,
      .inr ⟨new, cxe₂, tw, hop, hc'0, hev', hov, hpl, rfl, rfl, ⟨σ.cl, id, rfl⟩,
        ErAt.not_claimed_rmw E hn hi1 hev hrd hseen fun p hp hpd => absurd hpd (hnp p hp)⟩⟩, E', hR,
    ⟨snapLe_snapAfter h.ht (hcl2.mem.trans hm4.symm) (hcl2.prom.trans hp4.symm),
      Ghost.Le.rmwGhost g l tr tw rel ss, ⟨_, hcl2.rmwAfter k false l, rfl⟩,
      .inl ⟨rfl, fun ts hts hpd' => hn' ts (hprom' ts (hp4 ▸ hts)) hpd'⟩, fun hc0 => h.cl hc0.1,
      ⟨fun e => absurd e Bool.false_ne_true, fun e => absurd e Bool.false_ne_true⟩⟩,
    WpPath.congr ⟨Ghost.Le.rmwGhost g l tr tw rel ss, fun _ h _ => h, fun _ h => h, hmw,
      fun w hw => (hwl w hw) ▸ hposr⟩ hm4 hp4,
    by rw [hm4, ← hm1c]; exact hev.last_le, fun ts hts hpd' => hn' ts (hprom' ts (hp4 ▸ hts)) hpd', rfl⟩

/-- **RMW transport at an in-flight release, exposing the ghost step**
(generic form of `NodeRel.rmwRelS` and `NodeRel.rmwRelSG`):
`NodeRel.rmwRelS` with the give-away side condition at the RMW's own claimed
slots (`hC0`) in place of `RelRmwGiveOk`, and the ghost after the RMW
(`unpend (rmwGhost g l x.1 tw false []) tw`), the unchanged memory, the
unclaimed read message and the env's `coh l` exposed. -/
theorem NodeRel.rmwRelSGP (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {l : Loc} {v : Val}
    (hst : StartS tid c t g (some (l, v)))
    (hC0 : ∀ tr, pl.rel l v = true → Res.only (pl.gives l v) (Res.prod ((claimedSlots g l tr).map (·.res))) = Res.unit)
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
        cx'.mem = c.mem) ∧ ¬ g.Claimed (l, x.1) ∧ x.1 < σ'.vs.getCoh l := by
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
  have hgr : g.rel = σ.g.rel := h.ghost.rel
  have hprom' : ∀ ts ∈ cx'.prom, ts ∈ t.prom := fun ts hts => by
    rw [hev.prom] at hts; exact hp1t ▸ List.mem_of_mem_erase hts
  obtain ⟨-, -, hrd, hseen⟩ := rmw_event A tid iv hx hi hc
  obtain ⟨hrdAt, -⟩ := readAt_rmw hx'0
  obtain ⟨hcond, -, hrel⟩ := hok.2 c g tr old v h.anchorOk hrdAt hop
  have htr : claimedSlots g l tr ≠ [] → tr ≤ (rmwAfter A k false l cx').views.wfloor := fun hne => by
    rcases hcond hne with hk | ⟨hk, hnf⟩
    · exact rmw_tr_le_wfloor_acqRel hc (by rw [hk]; rfl)
    · have hfw : ∀ f, (fenceOptCtx A (envCtx tid σ.vs c)).views.getFwd l = some f → f.time ≠ tr := by
        intro f hf ht
        rw [fenceOptCtx_views, rmwReadViews_getFwd] at hf
        exact hnf ⟨f, hf, ht⟩
      exact Nat.le_trans (rmw_tr_le_wfloor_acq hx'0 hk hfw hc'0 k false) (hcl2.rmwAfter k false l).wfloor
  have hl : pl.rel l v = true → l ∉ pl.gives l v := fun hrl => (hrel hrl).2.2.1
  have hs : pl.rel l v = true → pl.Whole l v := fun hrl => (hrel hrl).2.2.2.1
  have hC : pl.rel l v = true → Res.only (pl.gives l v) (Res.prod ((claimedSlots g l tr).map (·.res))) = Res.unit :=
    hC0 tr
  have hqr : 0 < (r.wr l).q := by
    rw [hr]; unfold Plan.after
    cases hrl : pl.rel l v with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, Res.addW_q]; exact hok.1
    | true =>
      simp only [↓reduceIte, Res.addW_q]
      exact pl.keep_q_pos (hl hrl) _ _ hok.1
  have hreq : (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (v, tw) =
      pl.afterRmw l v tr tw g P σ.r := by
    rw [hr]; exact pl.after_op_claim hok.1 hl hs hC
  -- erasure: fulfil the pending promise, then claim the message read
  have hnp : ∀ p ∈ cx₁.prom, p ∈ g.pend → ((l, tr), p) ∉ g.claims := fun p hp' _ hcl =>
    E.claimFulf _ p hcl ⟨tid, _, ErAt.get? hn, hp'⟩
  obtain ⟨htrw, hat⟩ := hev.tr tr rfl
  have hun' : ¬ g.Claimed (l, tr) :=
    Erase.not_claimed_noclaim E (ErAt.get? hn) (hev.writeAt hi1) rfl htrw hrd hat hnp hseen
  have E1 : ErAt rF (fun _ => True) c t tid r (unpend g tw) cx' := ErAt.fulfilPend E hn hi1 hev hpd
  have hno := ErAt.not_outstanding_fulfilled E hn hi1 hev hget
  have E2 := Erase.claimPend (tid := tid) (g := unpend g tw) E1 (by rw [Config.withThread_size]; exact hn) htrw
    (show cx'.mem.get? tw = some ⟨l, v, tid⟩ by rw [hmeq]; exact hget) rfl hno
    (fun ts w' h1 h2 hw' hl' => atomic_between hat hrd h1 h2 (by rw [← hmeq]; exact hw') hl') hun'
    (by rw [setRes_self]; exact hqr)
  simp only [setRes_setRes, setRes_self] at E2
  have hg' : rmwGhost (unpend g tw) l tr tw false [] = unpend (rmwGhost g l tr tw false []) tw := rfl
  have hcs : claimedSlots (unpend g tw) l tr = claimedSlots g l tr := rfl
  rw [hg', hcs, hreq] at E2
  have E' : ErAt rF (fun _ => True) c t tid (pl.afterRmw l v tr tw g P σ.r) (unpend (rmwGhost g l tr tw false []) tw)
      cx' := E2
  have hR1 : RStep c.mem.last r g (pl.afterRmw l v tr tw g P σ.r) (rmwGhost g l tr tw false [])
      (rmwAfter A k false l cx') :=
    RStep.rmw (FreshSlots.nil _) (by rw [List.map_nil]; exact (Res.op_unit _).trans hreq.symm) htr
  have hR := RStep.trans hR1 (RStep.unpend tw _) (Nat.le_refl _)
  have hmw : ∀ y, mayWrite (pl.afterRmw l v tr tw g P σ.r) (unpend (rmwGhost g l tr tw false []) tw) y →
      mayWrite r g y := fun y hy => by
    rw [← hreq] at hy
    exact SpinCommon.mayWrite_claim (mayWrite_unpend hy)
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
  have hnopd : ∀ ts' ∈ (rmwAfter A k false l cx').prom, ts' ∉ (unpend (rmwGhost g l tr tw false []) tw).pend := by
    intro ts' hts' hpd'
    obtain ⟨h1, h2⟩ := mem_unpend_pend.mp hpd'
    exact h2 (h6 ts' (hprom' ts' (hp4 ▸ hts')) h1)
  have hgle : g.Le (unpend (rmwGhost g l tr tw false []) tw) := ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩
  refine .inr ⟨_, _, { σ with
      snap := snapAfter tid c cxe₂, vs := (rmwAfter A k false l cxe₂).views
      r := pl.afterRmw l v tr tw g P σ.r, g := g
      seen := seenAfter A (A.rmwKind k).loadKind σ g l tr, fencedR := false, fencedW := false },
    ⟨c, (tr, old, cxe₁), h.anchorOk, hx'0, rfl, rfl, rfl, rfl, rfl,
      .inr ⟨v, cxe₂, tw, hop, hc'0, hev', hov, fun _ => .inr hpd, rfl, rfl, ⟨P, hP, rfl⟩, hun'⟩⟩, E', hR,
    ⟨snapLe_snapAfter h.ht (hcl2.mem.trans hm4.symm) (hcl2.prom.trans hp4.symm),
      hgle, ⟨_, hcl2.rmwAfter k false l, rfl⟩, .inl ⟨rfl, hnopd⟩, fun hc0 => h.cl hc0.1,
      ⟨fun e => absurd e Bool.false_ne_true, fun e => absurd e Bool.false_ne_true⟩⟩,
    WpPath.congr ⟨hgle, fun ts' hts' ho => ?_, fun ts' hts' => (mem_unpend_pend.mp hts').1, hmw,
      fun w hw => (hwl w hw) ▸ hqr⟩ hm4 hp4,
    by rw [hm4, ← hm1c]; exact hev.last_le, hnopd, rfl, ⟨tw, rfl, htrw, hm1c ▸ hget, hmeq.trans hm1c⟩, hun',
    Nat.lt_of_lt_of_le htrw (Nat.le_trans (writeSuccs_coh_tw' hc'0 hev') ((vle_rmwAfter A k false l cxe₂).coh l))⟩
  refine mem_unpend_pend.mpr ⟨hts', ?_⟩
  rintro rfl
  rcases ho with ho | ⟨i, t', hne, hi', ho⟩
  · exact hnotin ho
  · exact hnototh i t' hne hi' ho

/-- **RMW transport at an in-flight release** (`pf = some (l, v)`): the
RMW's write fulfilling the pending promise `ts` (then `new = v`) claims the
message read and performs the prepaid write; every other write overtakes
`ts`. For a planned release, `RelRmwGiveOk` makes the claimed slots carry
nothing at the given-away locations, so the actual resource is the env's. -/
theorem NodeRel.rmwRelS (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {l : Loc} {v : Val}
    (hst : StartS tid c t g (some (l, v))) (hG : RelRmwGiveOk I pl g.rel)
    {k : RmwKind} {op : Val → Option Val} (hok : RmwOk A tid pl σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOut A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
      RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') ∧
      WpPath c tid t r g r' g' (rmwAfter A k false l cx') ∧ c.mem.last ≤ (rmwAfter A k false l cx').mem.last ∧
      (∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl :=
  (h.rmwRelSGP hst (fun tr hrl => hG _ g c l tr v rfl h.erase hrl) hok hx hop hc E hi).imp id
    fun ⟨r', g', σ', h1, h2, h3, h4, h5, h6, h7, h8, _⟩ => ⟨r', g', σ', h1, h2, h3, h4, h5, h6, h7, h8⟩

end Transport

/-! ## The instance and the link theorem -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The RMW side condition of the link with release-kind RMWs**: any RMW
without a release in flight; with one in flight (`pf = some (l, v)`), an RMW
of `l` whose operation never fails (**phase-1 limit**: a failing RMW would
leave the pending promise alive after the instruction). -/
abbrev RokR (pf : Option (Loc × Val)) (_k : RmwKind) (l : Loc) (op : Val → Option Val) : Prop :=
  pf = none ∨ ∃ v, pf = some (l, v) ∧ ∀ x, op x ≠ none

/-- The old side conditions imply the new ones. -/
theorem RokS.toR {A : Arch} {pf : Option (Loc × Val)} {k : RmwKind} {l : Loc} {op : Val → Option Val}
    (h : RokS A pf k) : RokR pf k l op :=
  .inl h.1

/-- **The per-node transport of `EnvG` with release-kind RMWs**
(`nodeSimS_envG` with `RokR`); `hG`: the give-away side condition of
planned-release RMWs at the instruction's ghost. -/
theorem nodeSimS2_envG {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    (hG : RelRmwGiveOk I pl gS.rel) :
    NodeSimS2 A tid iv rF (fun _ => True) c t (EnvG I A tid pl) (LokS pf) (SokS pf) (RokR pf) (LokS pf)
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
        exact ⟨σ', ho, hp, WpPath.refl hm hpr, by rw [hm]; exact Nat.le_refl _,
          fun ts hts => hst.none hpf ts (hpr ▸ hts), fun hne => absurd hpf hne⟩
      · rcases h.rmwS' (hst.none hpf) hok hx hop hc E hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, -⟩
        · exact .inl ho
        · exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, fun hne => absurd hpf hne⟩
    · subst hpf
      refine ⟨fun hop => absurd hop (htot _), fun new hop cx' hc E hi _ => ?_⟩
      rcases h.rmwRelS hst hG hok hx hop hc E hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, hcl⟩
      · exact .inl ho
      · exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, fun _ hc0 => hcl ▸ h.cl hc0⟩

/-- **Link theorem 1 for `EnvG` with release-kind RMWs**: as
`treeJ_envG_eraseWPRDS`, for a tree whose single access satisfies the
side conditions `LokS`/`SokS`/`RokR` of the start. -/
theorem treeJ_envG_eraseWPRDSR {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    (hG : RelRmwGiveOk I pl gS.rel) {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDS2 (nodeSimS2_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀)
      (cl₀ := cl₀) (rS := rS) hst hG) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDS2 _ hW ⟨h, rfl, rfl⟩ ha

/-- **Link theorem 1 with release-kind RMWs at an instruction's start**:
from `EnvRel` and the hypotheses of `ThreadRuleRX.wp`, at `ctx₀`. -/
theorem treeJ_envG_eraseWPRDSR_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf) (hG : RelRmwGiveOk I pl g.rel)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDS2 (nodeSimS2_envG (A := A) (pl := pl) (iv := instrViews t d) (rF := rF)
      (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hst hG) Q).W tree σ)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envG_eraseWPRDSR hst hG hW (hrel.toNodeRel rF d E hm) ha

end Link

end Kraken.Promising.SLR.EnvG
