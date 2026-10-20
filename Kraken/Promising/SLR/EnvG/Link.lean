/-
Whole-thread environment (`EnvG`): the **concrete link** for `EnvG`. ISA-neutral.

The per-node transports from `EnvG`'s outcomes (`EnvG/Facts.lean`: `LoadOut`,
`StoreOut`, `RmwOut`, `FenceOut`) and permissions (`EnvG/Env.lean`:
`StoreOk`, `RmwOk`) to the obligations of `EvTree.EraseWPRD` at the
validity-free erasure, through `NodeRel`/`PostRel` (`EnvG/NodeRel.lean`):

- `NodeRel.load`: `CtxLe.read` (`Sim.SimInv.read`); the env reads the same
  timestamp and value at the anchor `(c, g)`.
- `NodeRel.fence`, `PostRel.fence` (in `NodeRel.lean`): `CtxLe.fence`
  (`Sim.SimInv.fence`), `CtxLe.congrT`.
- `NodeRel.store`: `CtxLe.write` (`Sim.afterWrite_rel`, `Sim.CtxRel.fresh`,
  `Sim.writePre_le`), the same write event on both sides; a pending
  promise is fulfilled (`ErAt.fulfilPend`, `RStep.unpend`); otherwise
  `ErAt.store` with no slots (a pure value, `StoreOk`) or the slots of the
  uniform release obligation (`RelOb`, `Erase.slotsFor`, `Plan.keep_op_give`,
  `RStep.store`). A planned release never fulfils an old non-pending own
  promise (`Erase.pure_of_own` against `StoreOk`'s impurity).
- `NodeRel.rmw`: `CtxLe.fenceOpt`, `CtxLe.read`, `CtxLe.write`,
  `CtxLe.rmwAfter`; `ErAt.rmw` with the claim floor from `ClaimOk`
  (`rmw_tr_le_wfloor_acqRel` on the actual write, `rmw_tr_le_wfloor_acq` on
  the env's, transferred by `CtxLe.wfloor`), `RStep.rmw`.
- `nodeSim_envG`: the `NodeSim` instance; `treeJ_envG_eraseWPRD`: **link
  theorem 1** for `EnvG`.

Dead branches: an env outcome that overtakes an own promise is actually
overtaken (`CtxLe.overtaken`); `StoreOut`/`RmwOut` offer only the others.

**Open (phase 1)**: `InflightWritesDead` — while a prepaid release is in
flight (`InflightMode`), a write other than its fulfilment, and every RMW
write, must be a dead branch. Stated as a `Prop` and assumed by the link.
(Unprovable as stated; superseded by the tree-indexed side conditions
of `EnvG/LinkS.lean`, `treeJ_envG_eraseWPRDS_start`.)
The no-fault track (`NodeSimNF` does not hold for `EnvG`: it offers no
overtaken outcome) is in `EnvG/NoFault.lean`, under the weaker `EnvGAnswers`.
-/
import Kraken.Promising.SLR.EnvG.NodeRel
import Kraken.Promising.SLR.EnvG.TreeLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

theorem getLastD_le' {xs : List View} {n : Nat} (h : ∀ x ∈ xs, x ≤ n) : xs.getLastD 0 ≤ n := by
  rw [List.getLastD_eq_getLast?]
  cases hx : xs.getLast? with
  | none => exact Nat.zero_le _
  | some a => exact h a (List.mem_of_getLast? hx)

/-- The read facts of an RMW's env read (as in `rmwOut_facts`): `ReadAt`
from the RMW's read views, and the views after the read above `vs`. -/
theorem readAt_rmw {A : Arch} {tid : Nat} {vs : Views} {c : Config I} {kk : LoadKind} {l : Loc} {tr : Time}
    {old : Val} {cxe : Ctx} (hx : (tr, old, cxe) ∈ readSuccs A iv0 (fenceOptCtx A (envCtx tid vs c)) kk false l false) :
    ReadAt A tid (rmwReadViews A vs) c kk l tr old ∧ VLe vs cxe.views := by
  obtain ⟨t', v', he, -, hrd, hwi, hp⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hc0v := fenceOptCtx_views A (envCtx tid vs c)
  obtain ⟨hc0m, hc0p⟩ := fenceOptCtx_memProm (A := A) (envCtx tid vs c)
  rw [readBound_eq, hc0v, hc0m] at hwi
  rw [hc0m] at hrd
  rw [hc0p] at hp
  exact ⟨⟨hrd, hp, hwi⟩, (vle_fenceOpt A (envCtx tid vs c)).trans (vle_readNext A iv0 _ _ _ _ _ _ _)⟩

/-! ## The open phase-1 restriction -/

/-- **Open (phase 1, for the rule link).** While a prepaid release is in flight
(`InflightMode`: the env's virtual resource counts the pending release as
performed), every write outcome of the instruction's access other than the
fulfilment of the pending promise is a dead branch: a non-pending store
outcome, and every RMW write outcome. (A store of the released location
above the promise is dead by coherence; a store to another location, or an
RMW, would need the in-flight relation to commute with the write's
resource change, which phase 1 does not provide.) -/
def InflightWritesDead (A : Arch) (tid : Nat) (pl : Plan) (iv : InstrViews) (rF : Nat → Res) (c : Config I)
    (t : Thread I) : Prop :=
  ∀ (rv₀ : Res) (g₀ : Ghost) (cl₀ : Prop) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx),
    NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx → InflightMode tid pl σ.cl σ.r r g t.prom c.mem →
    (∀ (k : StoreKind) (l : Loc) (v : Val) (cx' : Ctx) (tw : Time),
      cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none → WriteEv tid cx cx' l v none tw →
      tw ∉ g.pend → cx'.Overtaken) ∧
    (∀ (k : RmwKind) (l : Loc) (x : Time × Val × Ctx) (new : Val) (cx' : Ctx) (tw : Time),
      x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false →
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → cx'.Overtaken)

/-! ## The transports -/

/-- **The message an RMW reads is unclaimed** (context level): from erasure
at the context after the RMW's read and the machine side of the event
(`rmw_event`), with no pending promise of the thread claiming `(l, tr)`
(`Erase.not_claimed_noclaim`). The producer of `RmwOut`'s claim fact. -/
theorem ErAt.not_claimed_rmw {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I} {tid : Nat}
    {r : Res} {g : Ghost} {cx cx' : Ctx} (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size)
    (hi : cx.Inv tid) {l : Loc} {new old : Val} {tr tw : Time} (hev : WriteEv tid cx cx' l new (some tr) tw)
    (hrd : cx.mem.read? l tr = some old)
    (hseen : ∀ ts w, cx.mem.get? ts = some w → w.loc = l → w.tid = tid → ts ∉ cx.prom → ts ≤ tr)
    (hnp : ∀ p ∈ cx.prom, p ∈ g.pend → ((l, tr), p) ∉ g.claims) : ¬ g.Claimed (l, tr) := by
  obtain ⟨htr, hat⟩ := hev.tr tr rfl
  exact Erase.not_claimed_noclaim E (ErAt.get? hn) (hev.writeAt (c := c) (t := t) hi) rfl htr hrd hat hnp hseen

section Transport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}

/-- **Load transport.** -/
theorem NodeRel.load (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {k : LoadKind} {xcl : Bool} {l : Loc}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l) :
    ∃ σ', LoadOut A tid σ σ' k xcl l x.2.1 ∧ PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r g x.2.2 := by
  obtain ⟨tr, v, cx₁⟩ := x
  obtain ⟨cxe₁, hx', hc⟩ := h.ctx.read hx
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  simp only at hm1 hp1 ⊢
  refine ⟨{ σ with
      snap := c, g := g, vs := cxe₁.views, cl := (σ.cl ∧ ClAt tid σ.r g c)
      seen := seenAfter A k σ g l tr, fencedR := false }, ⟨h.anchorOk, rfl, rfl, tr, cxe₁, hx', rfl, rfl, rfl, rfl⟩,
    ?_, Ghost.Le.refl g, ⟨cxe₁, hc, rfl⟩, (h.res.congr (hp1.trans h.prom) (hm1.trans h.mem)).mono_cl And.left, ?_,
      h.fenced.read hx⟩
  · rw [withThread_ctx h.ht (hm1.trans h.mem) (hp1.trans h.prom)]; exact SnapLe.refl tid c
  · rintro ⟨h0, hcl⟩
    refine ⟨h.cl h0, ?_⟩
    rw [h.rv, h.g0]; exact hcl

/-- The env state after a store at anchor `c` with outcome `cxe₂` at `tw`. -/
def storeState (pl : Plan) (σ : State I) (tid : Nat) (c : Config I) (g : Ghost) (l : Loc) (v : Val) (tw : Time)
    (P : Prop) (cxe₂ : Ctx) : State I :=
  { σ with snap := snapAfter tid c cxe₂, vs := cxe₂.views, r := pl.after l v tw P σ.r, g := g, fencedW := false }

/-- **Store transport** (non-exclusive, as `StoreOk` requires). -/
theorem NodeRel.store (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx)
    (hIW : InflightWritesDead A tid pl iv rF c t) {k : StoreKind} {l : Loc} {v : Val}
    (hok : StoreOk A tid pl σ k false l v) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', StoreOut A tid pl σ σ' k false l v true ∧
      ErAt rF (fun _ => True) c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' cx' ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' cx' := by
  obtain ⟨-, hpos, hpure, hrel⟩ := hok
  have hn := lt_size_of_get? h.ht
  have E := h.erAt
  obtain ⟨cxe₂, tw, hc', hev, hev', hcl⟩ := h.ctx.write (A := A) hi (ivLe_envIv _ (iv.forStore cx.stores))
    (h.ctx.sim.ivb.forStore cx.stores) (Nat.le_refl 0) (Nat.zero_le _) hc
  have hc'0 : cxe₂ ∈ writeSuccs A tid iv0 (envCtx tid σ.vs c) k false l v none := hc'
  by_cases hov : cxe₂.Overtaken
  · exact .inl (hcl.overtaken hov)
  have hgr : g.rel = σ.g.rel := h.ghost.rel
  have hpc : cx.prom = t.prom := h.prom
  have hmc : cx.mem = c.mem := h.mem
  have hout : ∀ P : Prop, (σ.cl → P) → (pl.rel l v = true → tw ∉ ownProm tid c ∨ tw ∈ g.pend) →
      StoreOut A tid pl σ (storeState pl σ tid c g l v tw P cxe₂) k false l v true :=
    fun P hP hpl => ⟨rfl, rfl, c, cxe₂, tw, h.anchorOk, hc'0, hev', hov, hpl, rfl, rfl, ⟨P, hP, rfl⟩, rfl, rfl, rfl,
      rfl⟩
  have hpost : ∀ (P : Prop) r' g', g.Le g' → Inflight tid pl σ.cl (pl.after l v tw P σ.r) r' g' cx'.prom cx'.mem →
      PostRel tid pl iv c t rv₀ g₀ cl₀ (storeState pl σ tid c g l v tw P cxe₂) r' g' cx' := fun P r' g' hg hres =>
    ⟨snapLe_snapAfter h.ht hcl.mem hcl.prom, hg, ⟨cxe₂, hcl, rfl⟩, hres, fun hc0 => h.cl hc0.1,
      h.fenced.write hc⟩
  have hprom' : ∀ ts ∈ cx'.prom, ts ∈ t.prom := fun ts hts => by
    rw [hev.prom] at hts; exact hpc ▸ List.mem_of_mem_erase hts
  by_cases hpd : tw ∈ g.pend
  · -- fulfilling the pending promise
    obtain ⟨-, htp, hget⟩ : cx'.mem = cx.mem ∧ tw ∈ cx.prom ∧ cx.mem.get? tw = some ⟨l, v, tid⟩ := by
      rcases hev.cases with h' | ⟨-, rfl⟩
      · exact h'
      · have h1 := h.erase.pend_le hpd; rw [← hmc] at h1; omega_t
    rcases h.res with ⟨-, hn'⟩ | ⟨ts, l₀, v₀, h1, -, h3, h5, h6⟩
    · exact absurd hpd (hn' tw (hpc ▸ htp))
    obtain rfl : tw = ts := h6 tw (hpc ▸ htp) hpd
    have hmsg := hget
    rw [hmc, h3] at hmsg
    simp only [Option.some.injEq, Msg.mk.injEq] at hmsg
    obtain ⟨rfl, rfl, -⟩ := hmsg
    obtain ⟨P, hP, h5⟩ := h5
    refine .inr ⟨r, unpend g tw, _, hout P hP fun _ => .inr hpd, E.fulfilPend hn hi hev hpd, RStep.unpend tw cx',
      hpost P _ _ (Ghost.Le.unpend g tw) (.inl ⟨h5, fun ts' hts' hpd' => ?_⟩)⟩
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hpd'
    exact hpd'.2 (h6 ts' (hprom' ts' hts') hpd'.1)
  · by_cases hmode : InflightMode tid pl σ.cl σ.r r g t.prom c.mem
    · exact .inl ((hIW rv₀ g₀ cl₀ σ r g cx h hmode).1 k l v cx' tw hc hev hpd)
    obtain ⟨hr, hn'⟩ := h.res.resolve_right hmode
    have hown : tw ∈ cx.prom → Pred.Pure (g.rel l) v := fun htp => by
      rcases hev.cases with ⟨-, -, hget⟩ | ⟨-, rfl⟩
      · exact Erase.pure_of_own h.erase h.ht (hpc ▸ htp) hpd (hmc ▸ hget)
      · obtain ⟨w, hw, -⟩ := hi.prom _ htp
        have := cx.mem.last_le_of_get?_eq_some hw
        omega_t
    have hposr : 0 < (r.wr l).q := hr ▸ hpos
    -- the erasure and reach obligations, per release kind
    obtain ⟨rel, ss, E', hR, hpl⟩ : ∃ rel ss, ErAt rF (fun _ => True) c t tid (pl.after l v tw σ.cl σ.r)
        (storeGhost g l tw rel ss) cx' ∧ RStep c.mem.last r g (pl.after l v tw σ.cl σ.r) (storeGhost g l tw rel ss) cx' ∧
        (pl.rel l v = true → tw ∉ ownProm tid c ∨ tw ∈ g.pend) := by
      cases hrl : pl.rel l v with
      | false =>
        have hres : (pl.after l v tw σ.cl σ.r).op (Res.prod (([] : List Slot).map (·.res))) = r.addW l (v, tw) := by
          simp [Plan.after, hrl, Res.op_unit, hr]
        exact ⟨false, [], E.store hn hi hev hpd hposr (fun h => absurd h Bool.false_ne_true)
          (fun _ => ⟨rfl, hgr ▸ hpure hrl⟩) hres (fun _ _ _ h => absurd trivial h), RStep.store (FreshSlots.nil _) hres cx',
          fun h => absurd h Bool.false_ne_true⟩
      | true =>
        obtain ⟨-, himp, hgl, hob⟩ := hrel hrl
        have hnotown : tw ∉ cx.prom := fun htp => himp (hgr ▸ hown htp)
        obtain ⟨hm', rfl⟩ : cx'.mem = (cx.mem.append ⟨l, v, tid⟩).1 ∧ tw = cx.mem.last + 1 := by
          rcases hev.cases with ⟨-, htp, -⟩ | h'
          · exact absurd htp hnotown
          · exact h'
        obtain ⟨hwok, -⟩ := writeSuccs_at A tid hc'0 hev'
        have hwb := writeBound_of_writeOk A tid hwok (VLe.refl σ.vs)
        rw [hmc] at hwb
        have hP := hob c g h.anchorOk hwb
        have hP' : (g.rel l).P v cx'.mem (cx.mem.last + 1) (pl.give l v σ.cl σ.r) := by
          rw [hgr, hm', hmc]; exact hP
        obtain ⟨ss, hss, hprod⟩ := Erase.slotsFor E hP'
        rw [total_withThread] at hss
        have hncl : ¬ g.Claimed (l, cx.mem.last + 1) :=
          Erase.not_claimed_fresh E (show cx.mem.last < cx.mem.last + 1 by omega_t)
        have hres : (pl.after l v (cx.mem.last + 1) σ.cl σ.r).op (Res.prod (ss.map (·.res))) =
            r.addW l (v, cx.mem.last + 1) := by
          rw [hprod, hr]; simp only [Plan.after, hrl, ↓reduceIte, Plan.give]
          exact pl.keep_op_give hgl σ.cl σ.r _
        have hfs : FreshSlots c.mem.last ss :=
          hev.freshSlots (by rw [hmc]; exact Nat.le_refl _) hss.key (fun htp => absurd htp hnotown)
        exact ⟨true, ss, E.store hn hi hev hpd hposr (rel := true) (fun _ => ⟨hss, hncl⟩) (fun h => Bool.noConfusion h) hres
          (fun _ _ _ h => absurd trivial h), RStep.store hfs hres cx', fun _ => .inl (by rw [ownProm_eq h.ht, ← hpc]; exact hnotown)⟩
    exact .inr ⟨_, _, _, hout σ.cl id hpl, E', hR, hpost σ.cl _ _ (Ghost.Le.storeGhost g l tw rel ss)
      (.inl ⟨rfl, fun ts hts hpd' => hn' ts (hprom' ts hts) hpd'⟩)⟩

/-- **RMW transport, failing operation** (`CtxLe.fenceOpt`, `CtxLe.read`). -/
theorem NodeRel.rmwFail (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false) (hop : op x.2.1 = none) :
    ∃ σ', RmwOut A tid pl σ σ' k l op x.2.1 ∧ PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r g (fenceOptCtx A x.2.2) := by
  obtain ⟨tr, old, cx₁⟩ := x
  obtain ⟨cxe₁, hx', hc1⟩ := (h.ctx.fenceOpt (A := A)).read hx
  have hx'0 : (tr, old, cxe₁) ∈ readSuccs A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l
      false := hx'
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
  simp only at hm1 hp1 hop ⊢
  have hm1c : cx₁.mem = c.mem := hm1.trans (hm0.trans h.mem)
  have hp1t : cx₁.prom = t.prom := hp1.trans (hp0.trans h.prom)
  obtain ⟨hm2, hp2⟩ := fenceOptCtx_memProm (A := A) cx₁
  refine ⟨{ σ with
      snap := c, g := g, vs := (fenceOptCtx A cxe₁).views
      seen := seenAfter A (A.rmwKind k).loadKind σ g l tr, fencedR := false, fencedW := false },
    ⟨c, (tr, old, cxe₁), h.anchorOk, hx'0, rfl, rfl, rfl, rfl, rfl, .inl ⟨hop, rfl, rfl, rfl⟩⟩,
    ?_, Ghost.Le.refl g, ⟨_, hc1.fenceOpt, rfl⟩, h.res.congr (hp2.trans hp1t) (hm2.trans hm1c),
    fun hc0 => h.cl hc0.1, ⟨fun e => absurd e Bool.false_ne_true, fun e => absurd e Bool.false_ne_true⟩⟩
  rw [withThread_ctx h.ht (hm2.trans hm1c) (hp2.trans hp1t)]; exact SnapLe.refl tid c

/-- **RMW transport** (live: `noRet = false`). -/
theorem NodeRel.rmw (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx)
    (hIW : InflightWritesDead A tid pl iv rF c t) {k : RmwKind} {l : Loc} {op : Val → Option Val}
    (hok : RmwOk A tid pl σ k l op) {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false) :
    (op x.2.1 = none →
      ∃ σ', RmwOut A tid pl σ σ' k l op x.2.1 ∧ PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r g (fenceOptCtx A x.2.2)) ∧
    ∀ new, op x.2.1 = some new →
      ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
        ErAt rF (fun _ => True) c t tid r g x.2.2 → cx.Inv tid →
        cx'.Overtaken ∨ ∃ r' g' σ', RmwOut A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
          RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
          PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') := by
  obtain ⟨tr, old, cx₁⟩ := x
  obtain ⟨cxe₁, hx', hc1⟩ := (h.ctx.fenceOpt (A := A)).read hx
  have hx'0 : (tr, old, cxe₁) ∈ readSuccs A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l
      false := hx'
  obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
  obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
  simp only at hm1 hp1 ⊢
  have hm1c : cx₁.mem = c.mem := hm1.trans (hm0.trans h.mem)
  have hp1t : cx₁.prom = t.prom := hp1.trans (hp0.trans h.prom)
  refine ⟨fun hop => ?_, fun new hop cx' hc E hi => ?_⟩
  · exact h.rmwFail hx hop
  -- the operation writes
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
  by_cases hmode : InflightMode tid pl σ.cl σ.r r g t.prom c.mem
  · exact .inl ((hIW rv₀ g₀ cl₀ σ r g cx h hmode).2 k l (tr, old, cx₁) new cx' tw hx hc hev)
  obtain ⟨hr, hn'⟩ := h.res.resolve_right hmode
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
  have hown : tw ∈ cx₁.prom → Pred.Pure (g.rel l) new := fun htp => by
    rcases hev.cases with ⟨-, -, hget⟩ | ⟨-, rfl⟩
    · exact Erase.pure_of_own h.erase h.ht (hp1t ▸ htp) hpd (hm1c ▸ hget)
    · obtain ⟨w, hw, -⟩ := hi1.prom _ htp
      have := cx₁.mem.last_le_of_get?_eq_some hw
      omega_t
  have htrl : tr ≤ c.mem.last := by
    obtain ⟨t', v', he, hle, -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    rw [hm0, h.mem] at hle; exact hle
  obtain ⟨rel, ss, E', hR, hpl⟩ : ∃ rel ss, ErAt rF (fun _ => True) c t tid (pl.afterRmw l new tr tw g σ.cl σ.r)
      (rmwGhost g l tr tw rel ss) cx' ∧
      RStep c.mem.last r g (pl.afterRmw l new tr tw g σ.cl σ.r) (rmwGhost g l tr tw rel ss) (rmwAfter A k false l cx') ∧
      (pl.rel l new = true → tw ∉ ownProm tid c ∨ tw ∈ g.pend) := by
    cases hrl : pl.rel l new with
    | false =>
      have hres : (pl.afterRmw l new tr tw g σ.cl σ.r).op (Res.prod (([] : List Slot).map (·.res))) =
          (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (new, tw) := by
        simp [Plan.afterRmw, Plan.after, hrl, Res.op_unit, hr]
      exact ⟨false, [], E.rmw hn hi1 hev hrd hseen hnp hposr (fun h => absurd h Bool.false_ne_true)
        (fun _ => ⟨rfl, hgr ▸ hpure hrl⟩) hres (fun _ _ _ h => absurd trivial h), RStep.rmw (FreshSlots.nil _) hres htr,
        fun h => absurd h Bool.false_ne_true⟩
    | true =>
      obtain ⟨-, himp, hgl, -, hob⟩ := hrel hrl
      have hnotown : tw ∉ cx₁.prom := fun htp => himp (hgr ▸ hown htp)
      obtain ⟨hm', rfl⟩ : cx'.mem = (cx₁.mem.append ⟨l, new, tid⟩).1 ∧ tw = cx₁.mem.last + 1 := by
        rcases hev.cases with ⟨-, htp, -⟩ | h'
        · exact absurd htp hnotown
        · exact h'
      obtain ⟨hwok, -⟩ := writeSuccs_at A tid hc'0 hev'
      have hwb := writeBound_of_writeOk A tid hwok hvle
      rw [hm1c] at hwb
      have hP := hob (by omega_t) hwb
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
      exact ⟨true, ss, E.rmw hn hi1 hev hrd hseen hnp hposr (rel := true) (fun _ => ⟨hss, hncl⟩) (fun h => Bool.noConfusion h)
        hres (fun _ _ _ h => absurd trivial h), RStep.rmw hfs hres htr,
        fun _ => .inl (by rw [ownProm_eq h.ht, ← hp1t]; exact hnotown)⟩
  obtain ⟨hm4, hp4⟩ := rmwAfter_memProm (A := A) k false l cx'
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
      ⟨fun e => absurd e Bool.false_ne_true, fun e => absurd e Bool.false_ne_true⟩⟩⟩

end Transport

/-! ## The instance and link theorem 1 -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The per-node transport of `EnvG`** at the validity-free erasure, through
`NodeRel`/`PostRel`, under the phase-1 restriction `InflightWritesDead`. -/
theorem nodeSim_envG (hIW : InflightWritesDead A tid pl iv rF c t) :
    NodeSim A tid iv rF (fun _ => True) c t (EnvG I A tid pl)
      (fun σ r g cx => NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx)
      (fun σ r g cx => PostRel tid pl iv c t rv₀ g₀ cl₀ σ r g cx) where
  pre_post h := h.post
  fence_pre {k} {σ} _ _ _ h _ := ⟨fenceState σ k, fenceOut_fenceState σ k, h.fence k⟩
  fence_post {k} {σ} _ _ _ h _ := ⟨fenceState σ k, fenceOut_fenceState σ k, h.fence k⟩
  load h _ x hx := h.load hx
  store := by
    intro k xcl addr n v σ r g cx h hok
    obtain rfl : xcl = false := hok.1
    refine ⟨fun cx' hc E hi _ => ?_, fun hx => absurd hx Bool.false_ne_true⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    rcases h.store hIW hok hc hi with ho | ⟨r', g', σ', hst, E', hR, hp⟩
    · exact .inl ho
    · exact .inr ⟨r', g', σ', hst, E', hR, hp⟩
  rmw := by
    intro k addr n op σ r g cx h hok x hx
    obtain ⟨hf, hw⟩ := h.rmw hIW hok hx
    refine ⟨hf, fun new hop cx' hc E hi _ => ?_⟩
    rcases hw new hop cx' hc E hi with ho | ⟨r', g', σ', hst, E', hR, hp⟩
    · exact .inl ho
    · exact .inr ⟨r', g', σ', hst, E', hR, hp⟩

/-- **Link theorem 1 for `EnvG`.** A live tree judgment of `EnvG` for the
instruction's tree (any judgment the environment's run proves, at
`TreeJLive.eraseWPRD (nodeSim_envG hIW) Q`), from an env state related to the
instruction's start by `NodeRel` (`EnvRel.toNodeRel` at `ctx₀`), gives the
erasure WP with dead branches at the validity-free erasure, for a
single-access tree; the postcondition is the judgment's at an env state
related to the final context by `PostRel` (`PostRel.finish` re-establishes
`EnvRel`). Assumes the phase-1 restriction `InflightWritesDead`. -/
theorem treeJ_envG_eraseWPRD (hIW : InflightWritesDead A tid pl iv rF c t) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRD (nodeSim_envG (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀) hIW) Q).W tree σ)
    {r : Res} {g : Ghost} {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (ha : SingleAccess tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q (fun (σ' : State I) r' g' cx' => PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' cx')) r g cx :=
  treeJ_eraseWPRD _ hW h ha

/-- **Link theorem 1 at an instruction's start**: from `EnvRel` and the
hypotheses of `ThreadRuleRX.wp` (erasure, machine invariants), at the start
context `ctx₀` with the instruction's views. -/
theorem treeJ_envG_eraseWPRD_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId)
    (hIW : InflightWritesDead A tid pl (instrViews t d) rF c t)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRD (nodeSim_envG (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) hIW) Q).W tree σ)
    (ha : SingleAccess tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q (fun (σ' : State I) r' g' cx' => PostRel tid pl (instrViews t d) c t σ.r g cl σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envG_eraseWPRD hIW hW (hrel.toNodeRel rF d E hm) ha

end Link

end Kraken.Promising.SLR.EnvG
