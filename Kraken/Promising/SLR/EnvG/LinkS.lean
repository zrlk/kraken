/-
Whole-thread environment (`EnvG`): the **concrete link with
in-flight releases**. ISA-neutral.

`EnvG/Link.lean`'s `treeJ_envG_eraseWPRD` assumes `InflightWritesDead`,
which does not mention the instruction and is not provable (a store to
another location while a release is in flight is not overtaken). Here the
in-flight case is handled per instruction, through the side conditions of
`SingleAccessS` (`EnvG/TreeLinkS.lean`), indexed by the in-flight message
`pf : Option (Loc × Val)` of the instruction's start:

- `pf = none` (no own pending promise): every access is allowed, except
  release-kind RMWs (**phase 1: releases are stores**, `KNOWN_GAPS.md`);
- `pf = some (l, v)`: the instruction's single access is a store of `v` to
  `l`; it fulfils the pending promise, and every other outcome overtakes it
  (`overtaken_of_inflight`: coherence, plus the start fact that every other
  own promise to `l` lies above it, which prepay gets from
  `RelFulfilsLive`'s `NoDead`).

The post relation `PostS` adds to `PostRel` what `ThreadRuleRX.wp`'s
`WpPostR` needs along the path (`WpPath`: world growth, pending marks,
`acqLe`, written permissions), that no own promise is pending afterwards, and
the **clean flag under an in-flight release** (`cl`): the in-flight
tree has no load, so the env's `cl` is unchanged and the actual new flag
`cl₀ ∧ Erase(r₀)⊥` implies it through `cl₀`.

- `NodeRel.storeS`, `NodeRel.rmwS`: the store and (non-release) RMW
  transports with the path facts; `nodeSimS_envG`: the `NodeSimS` instance;
  `treeJ_envG_eraseWPRDS(_start)`: **link theorem 1** without
  `InflightWritesDead`.
-/
import Kraken.Promising.SLR.EnvG.Link
import Kraken.Promising.SLR.EnvG.TreeLinkS
import Kraken.Promising.SLR.SpinAcquire

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Helpers -/

/-- A write event's timestamp is below the written location's `coh`
afterwards (as `X64SpinXchg.writeSuccs_coh_tw`, which sits in a program
file). -/
theorem writeSuccs_coh_tw' {A : Arch} {tid : Nat} {iv : InstrViews} {cx cx' : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} {tw : Time}
    (hc : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra) (hev : WriteEv tid cx cx' l v tr tw) :
    tw ≤ cx'.views.getCoh l := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, ht, w, hw, -, -, -, hok, rfl⟩ | ⟨hok, rfl⟩
  · rcases hev.cases with ⟨-, htw, -⟩ | ⟨hm, -⟩
    · obtain rfl : t = tw := count_erase_eq ht hev.prom
      rw [afterWrite_getCoh]
      simp only [↓reduceIte]
      exact Nat.le_max_right _ _
    · exact absurd hm.symm (fun h => last_append_ne h)
  · rcases hev.cases with ⟨hm, -, -⟩ | ⟨-, rfl⟩
    · exact absurd hm (fun h => last_append_ne h)
    · rw [afterWrite_getCoh]
      simp only [↓reduceIte]
      exact Nat.le_max_right _ _

/-- Adding slots whose acquire ids the thread held, on fresh keys: what is
acquirable afterwards was acquirable before, or is a new slot. -/
theorem canAcq_append_le {u ss : List Slot} {U : Loc → List PredId} {A A' : Loc → PredId → Nat}
    (hA : ∀ y ι, A' y ι ≤ A y ι) (h0 : ∀ s ∈ ss, ∀ y ι, s.res.acq y ι ≤ A y ι)
    (hdisj : ∀ s ∈ u, ∀ s' ∈ ss, s.key ≠ s'.key)
    {k : Key} {ι : PredId} (h : CanAcq (u ++ ss) U A' k ι) : CanAcq u U A k ι ∨ ∃ s ∈ ss, s.key = k := by
  induction h with
  | base hs ha =>
    rcases List.mem_append.mp hs with hs | hs
    · exact .inl (.base hs (Nat.le_trans ha (hA _ _)))
    · exact .inr ⟨_, hs, rfl⟩
  | upd hs hu =>
    rcases List.mem_append.mp hs with hs | hs
    · exact .inl (.upd hs hu)
    · exact .inr ⟨_, hs, rfl⟩
  | @step s s' _ hs hs' ha ih =>
    rcases List.mem_append.mp hs' with hs' | hs'
    · rcases List.mem_append.mp hs with hs | hs
      · rcases ih with ih | ⟨s0, hs0, hk⟩
        · exact .inl (.step ih hs hs' ha)
        · exact absurd hk.symm (hdisj s hs s0 hs0)
      · exact .inl (.base hs' (Nat.le_trans ha (h0 s hs _ _)))
    · exact .inr ⟨s', hs', rfl⟩

/-- **`acqLe` for a store** (a release giving away `R`, acquire ids
included, to fresh slots `ss`, or a relaxed store with `ss = []`). -/
theorem mayWrite_store_le {g : Ghost} {r r' R : Res} {x : Loc} {tw : Time} {rel : Bool} {p : Val × Time}
    {ss : List Slot} (hres : r'.op R = r.addW x p) (hprod : Res.prod (ss.map (·.res)) = R)
    (hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key) {y : Loc}
    (h : mayWrite r' (storeGhost g x tw rel ss) y) : mayWrite r g y := by
  have hq : ∀ z, (r'.wr z).q + (R.wr z).q = (r.wr z).q := by
    intro z
    have := congrArg (fun ρ => (ρ.wr z).q) hres
    simpa [Res.op, Perm.op] using this
  have hacq : ∀ z ι, r'.acq z ι + R.acq z ι = r.acq z ι := by
    intro z ι
    have := congrArg (fun ρ => ρ.acq z ι) hres
    simpa [Res.op] using this
  have h0 : ∀ s ∈ ss, ∀ y ι, s.res.acq y ι ≤ r.acq y ι := by
    intro s hs y ι
    have := acq_le_prod_slots hs y ι
    rw [hprod] at this
    have := hacq y ι
    omega
  rcases h with h | ⟨s, hs, hc, hpos⟩
  · have := hq y; have := (R.wr y).nonneg
    exact .inl (by grind)
  · rcases mem_store_u.mp hs with hs | hs
    · rcases canAcq_append_le (fun y ι => by have := hacq y ι; omega) h0 hdisj hc with hc | ⟨s0, hs0, hk⟩
      · exact .inr ⟨s, hs, hc, hpos⟩
      · exact absurd hk.symm (hdisj s hs s0 hs0)
    · have h1 : 0 < (R.wr y).q := by
        rw [← hprod]
        exact Res.pos_prod_of_mem (List.mem_map_of_mem hs) hpos
      have := hq y; have := (r'.wr y).nonneg
      exact .inl (by grind)

/-- `mayWrite` does not see pending marks. -/
theorem mayWrite_unpend {r : Res} {g : Ghost} {ts : Time} {y : Loc} (h : mayWrite r (unpend g ts) y) :
    mayWrite r g y := h

/-- The messages a single write event writes (at context level, from the
instruction's start memory and promises): only its own message. -/
theorem writtenCx_loc {c : Config I} {t : Thread I} {tid : Nat} {cx cx' : Ctx} {l : Loc} {v : Val}
    {trOpt : Option Time} {tw : Time} (hm : cx.mem = c.mem) (hp : cx.prom = t.prom)
    (hev : WriteEv tid cx cx' l v trOpt tw) {w : Msg} (hw : WrittenCx c t cx' w) : w.loc = l := by
  obtain ⟨ts, hget, hnp, hnew⟩ := hw
  by_cases hts : ts = tw
  · subst hts
    rcases hev.cases with ⟨hm', -, hg⟩ | ⟨hm', rfl⟩
    · rw [hm'] at hget; rw [hget] at hg; cases hg; rfl
    · rw [hm', Memory.get?_append_last] at hget; cases hget; rfl
  · exfalso
    have hnp' : ts ∉ t.prom := fun h => hnp (by rw [hev.prom, hp]; exact (List.mem_erase_of_ne hts).mpr h)
    have hlt : c.mem.last < ts := hnew.resolve_right hnp'
    have hle := cx'.mem.last_le_of_get?_eq_some hget
    rcases hev.cases with ⟨hm', -⟩ | ⟨hm', htw⟩
    · rw [hm', hm] at hle; omega_t
    · rw [hm', Memory.last_append, hm] at hle; rw [hm] at htw; exact hts (by omega_t)

/-- No message is written by an access-free run (memory and promises of the
start). -/
theorem not_writtenCx_start {c : Config I} {t : Thread I} {cx : Ctx} (hm : cx.mem = c.mem) (hp : cx.prom = t.prom)
    {w : Msg} (hw : WrittenCx c t cx w) : False := by
  obtain ⟨ts, hget, hnp, hnew⟩ := hw
  rw [hm] at hget
  rcases hnew with hlt | hpr
  · exact absurd (Memory.last_le_of_get?_eq_some _ hget) (Nat.not_le.mpr hlt)
  · exact hnp (hp ▸ hpr)

/-! ## Path facts -/

/-- **The path facts of `WpPostR`** (its first five conjuncts), from the
instruction's start (thread `t` in `c`, resource `r`, ghost `g`) to
`(r', g', cx')`. -/
def WpPath (c : Config I) (tid : Nat) (t : Thread I) (r : Res) (g : Ghost) (r' : Res) (g' : Ghost) (cx' : Ctx) :
    Prop :=
  g.Le g' ∧
    (∀ ts, ts ∈ g.pend → (ts ∈ cx'.prom ∨ ∃ (i : Nat) (t' : Thread I), i ≠ tid ∧ c.threads[i]? = some t' ∧ ts ∈ t'.prom) →
      ts ∈ g'.pend) ∧
    (∀ ts, ts ∈ g'.pend → ts ∈ g.pend) ∧ (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
    (∀ w, WrittenCx c t cx' w → 0 < (r.wr w.loc).q)

theorem WpPath.refl {c : Config I} {tid : Nat} {t : Thread I} {r : Res} {g : Ghost} {cx : Ctx}
    (hm : cx.mem = c.mem) (hp : cx.prom = t.prom) : WpPath c tid t r g r g cx :=
  ⟨Ghost.Le.refl g, fun _ h _ => h, fun _ h => h, fun _ h => h, fun _ hw => (not_writtenCx_start hm hp hw).elim⟩

theorem WpPath.congr {c : Config I} {tid : Nat} {t : Thread I} {r r' : Res} {g g' : Ghost} {cx cx' : Ctx}
    (h : WpPath c tid t r g r' g' cx) (hm : cx'.mem = cx.mem) (hp : cx'.prom = cx.prom) :
    WpPath c tid t r g r' g' cx' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, fun ts hts ho => h2 ts hts (by rw [← hp]; exact ho), h3, h4, fun w ⟨ts, hg, hn, hw⟩ => h5 w ?_⟩
  exact ⟨ts, hm ▸ hg, hp ▸ hn, hw⟩

/-! ## The in-flight start -/

/-- **The start of an instruction, by in-flight message** `pf`: `none` when
the thread has no own pending promise; `some (l, v)` when its pending
promise `ts` is the message `⟨l, v⟩` and every other own promise to `l` lies
above `ts` (prepay's `NoDead`). -/
structure StartS (tid : Nat) (c : Config I) (t : Thread I) (g : Ghost) (pf : Option (Loc × Val)) : Prop where
  none : pf = none → ∀ ts ∈ t.prom, ts ∉ g.pend
  some : ∀ l v, pf = some (l, v) → ∃ ts, ts ∈ t.prom ∧ ts ∈ g.pend ∧ c.mem.get? ts = some ⟨l, v, tid⟩ ∧
    ∀ p ∈ t.prom, p ≠ ts → ∀ w, c.mem.get? p = some w → w.loc = l → ts < p

/-- **Every write of the in-flight location other than the fulfilment
overtakes the pending promise** (coherence). -/
theorem overtaken_of_inflight {A : Arch} {tid : Nat} {iv : InstrViews} {cx cx' : Ctx} {k : StoreKind}
    {xcl : Bool} {l : Loc} {v : Val} {trOpt : Option Time} {extra : View} {tw ts : Time}
    (hc : cx' ∈ writeSuccs A tid iv cx k xcl l v trOpt extra) (hev : WriteEv tid cx cx' l v trOpt tw)
    (hts : ts ∈ cx.prom) (hget : cx.mem.get? ts = some ⟨l, v, tid⟩) (hlt : ts < tw) : cx'.Overtaken := by
  have hne : ts ≠ tw := by omega_t
  refine ⟨ts, by rw [hev.prom]; exact (List.mem_erase_of_ne hne).mpr hts, ⟨l, v, tid⟩, ?_,
    Nat.le_trans (Nat.le_of_lt hlt) (writeSuccs_coh_tw' hc hev)⟩
  rcases hev.cases with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm]; exact hget
  · rw [hm, Memory.get?_append_of_le _ _ _ (cx.mem.last_le_of_get?_eq_some hget)]; exact hget

/-! ## Coherence views of other locations (from `EnvG/TicketLink.lean`) -/

/-- A read keeps the coherence views of the other locations. -/
theorem readSuccs_getCoh_ne {A : Arch} {iv : InstrViews} {cx : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l noRet) {l' : Loc} (hne : l' ≠ l) :
    x.2.2.views.getCoh l' = cx.views.getCoh l' := by
  obtain ⟨tr, v, rfl, -⟩ := (mem_readSuccs A).mp hx
  show (cx.views.setCoh l _).getCoh l' = _
  rw [Views.getCoh_setCoh]
  simp [hne]

/-- A write keeps the coherence views of the other locations. -/
theorem writeSuccs_getCoh_ne {A : Arch} {tid : Nat} {iv : InstrViews} {cx cx' : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} (hc : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra)
    {l' : Loc} (hne : l' ≠ l) : cx'.views.getCoh l' = cx.views.getCoh l' := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, -, w, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · rw [afterWrite_getCoh]; simp [hne]
  · rw [afterWrite_getCoh]; simp [hne]

/-- The env's store keeps its coherence views of the other locations. -/
theorem storeOut_getCoh_ne {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {b : Bool} (h : StoreOut A tid pl σ σ' k xcl l v b) {l' : Loc} (hne : l' ≠ l) :
    σ'.vs.getCoh l' = σ.vs.getCoh l' := by
  obtain ⟨-, -, c, cx', tw, -, hc, -, -, -, -, hvs, -⟩ := h
  rw [hvs, writeSuccs_getCoh_ne hc hne]; rfl

/-! ## The store transport with path facts -/

section Transport

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}

/-- **Store transport, exposing the ghost step**: `NodeRel.storeS`'s
conclusion, and the ghost after the store keeps the claims, the acquire table
and the update ids and grows the update slots `u` (`storeGhost` or
`unpend`). Extensions of the erasure kept by such ghost steps (e.g. the
ticket dispenser's `TX`, `NodeRel.storeTD`) are transported from it. -/
theorem NodeRel.storeSG (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf) {k : StoreKind} {l : Loc} {v : Val} (hS : pf = none ∨ pf = some (l, v))
    (hok : StoreOk A tid pl σ k false l v) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', StoreOut A tid pl σ σ' k false l v true ∧
      ErAt rF (fun _ => True) c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' cx' ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' cx' ∧ WpPath c tid t r g r' g' cx' ∧
      c.mem.last ≤ cx'.mem.last ∧ (∀ ts ∈ cx'.prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl ∧
      (g'.claims = g.claims ∧ g'.acqTab = g.acqTab ∧ g'.upd = g.upd ∧ ∀ s ∈ g.u, s ∈ g'.u) := by
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
  have hlast : c.mem.last ≤ cx'.mem.last := hmc ▸ hev.last_le
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
  have hwl : ∀ w, WrittenCx c t cx' w → w.loc = l := fun w hw => writtenCx_loc hmc hpc hev hw
  rcases hS with hpf | hpf
  · ---- no release in flight
    have hnp0 := hst.none hpf
    obtain ⟨hr, hn'⟩ : r = σ.r ∧ ∀ ts ∈ t.prom, ts ∉ g.pend := by
      rcases h.res with h' | ⟨ts, -, -, h1, h2, -⟩
      · exact h'
      · exact absurd h2 (hnp0 ts h1)
    have hpd : tw ∉ g.pend := fun hpd => by
      rcases hev.cases with ⟨-, htp, -⟩ | ⟨-, rfl⟩
      · exact hn' tw (hpc ▸ htp) hpd
      · have h1 := h.erase.pend_le hpd; rw [← hmc] at h1; omega_t
    have hown : tw ∈ cx.prom → Pred.Pure (g.rel l) v := fun htp => by
      rcases hev.cases with ⟨-, -, hget⟩ | ⟨-, rfl⟩
      · exact Erase.pure_of_own h.erase h.ht (hpc ▸ htp) hpd (hmc ▸ hget)
      · obtain ⟨w, hw, -⟩ := hi.prom _ htp
        have := cx.mem.last_le_of_get?_eq_some hw
        omega_t
    have hposr : 0 < (r.wr l).q := hr ▸ hpos
    -- the erasure and reach obligations, per release kind, with `acqLe`
    obtain ⟨rel, ss, E', hR, hpl, hmw⟩ : ∃ rel ss, ErAt rF (fun _ => True) c t tid (pl.after l v tw σ.cl σ.r)
        (storeGhost g l tw rel ss) cx' ∧ RStep c.mem.last r g (pl.after l v tw σ.cl σ.r) (storeGhost g l tw rel ss) cx' ∧
        (pl.rel l v = true → tw ∉ ownProm tid c ∨ tw ∈ g.pend) ∧
        (∀ x, mayWrite (pl.after l v tw σ.cl σ.r) (storeGhost g l tw rel ss) x → mayWrite r g x) := by
      cases hrl : pl.rel l v with
      | false =>
        have hres : (pl.after l v tw σ.cl σ.r).op (Res.prod (([] : List Slot).map (·.res))) = r.addW l (v, tw) := by
          simp [Plan.after, hrl, Res.op_unit, hr]
        exact ⟨false, [], E.store hn hi hev hpd hposr (fun h => absurd h Bool.false_ne_true)
          (fun _ => ⟨rfl, hgr ▸ hpure hrl⟩) hres (fun _ _ _ h => absurd trivial h), RStep.store (FreshSlots.nil _) hres cx',
          fun h => absurd h Bool.false_ne_true,
          fun x hx => mayWrite_store_le hres rfl (fun _ _ _ h => absurd h List.not_mem_nil) hx⟩
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
        have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he => by
          have h1 := h.erase.slot_key_le hs
          have h2 := hfs s' hs'
          rw [he] at h1; omega_t
        exact ⟨true, ss, E.store hn hi hev hpd hposr (rel := true) (fun _ => ⟨hss, hncl⟩) (fun h => Bool.noConfusion h) hres
          (fun _ _ _ h => absurd trivial h), RStep.store hfs hres cx',
          fun _ => .inl (by rw [ownProm_eq h.ht, ← hpc]; exact hnotown),
          fun x hx => mayWrite_store_le hres rfl hdisj hx⟩
    refine .inr ⟨_, _, _, hout σ.cl id hpl, E', hR, hpost σ.cl _ _ (Ghost.Le.storeGhost g l tw rel ss)
      (.inl ⟨rfl, fun ts hts hpd' => hn' ts (hprom' ts hts) hpd'⟩),
      ⟨Ghost.Le.storeGhost g l tw rel ss, fun _ h _ => h, fun _ h => h, hmw, fun w hw => (hwl w hw) ▸ hposr⟩,
      hlast, fun ts hts hpd' => hn' ts (hprom' ts hts) hpd', rfl, rfl, rfl, rfl, fun s hs => mem_store_u.mpr (.inl hs)⟩
  · ---- the store is the in-flight release
    obtain ⟨ts, hts, hpts, hgts, habove⟩ := hst.some l v hpf
    obtain ⟨P, hPc, hr, h6⟩ : ∃ P : Prop, (σ.cl → P) ∧ r = pl.after l v ts P σ.r ∧
        ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts := by
      rcases h.res with ⟨-, hn'⟩ | ⟨ts₁, l₀, v₀, h1, h2, h3, h5, h6⟩
      · exact absurd hpts (hn' ts hts)
      · obtain rfl := h6 ts hts hpts
        rw [hgts] at h3
        simp only [Option.some.injEq, Msg.mk.injEq] at h3
        obtain ⟨rfl, rfl, -⟩ := h3
        obtain ⟨P, hP, h5⟩ := h5
        exact ⟨P, hP, h5, h6⟩
    have hqr : 0 < (r.wr l).q := by
      rw [hr]; unfold Plan.after
      cases hrl : pl.rel l v with
      | false => simp only [Bool.false_eq_true, ↓reduceIte, Res.addW_q]; exact hpos
      | true =>
        simp only [↓reduceIte, Res.addW_q]
        exact pl.keep_q_pos (hrel hrl).2.2.1 _ _ hpos
    by_cases hpd : tw ∈ g.pend
    · -- fulfilling the pending promise
      obtain ⟨-, htp, hget⟩ : cx'.mem = cx.mem ∧ tw ∈ cx.prom ∧ cx.mem.get? tw = some ⟨l, v, tid⟩ := by
        rcases hev.cases with h' | ⟨-, rfl⟩
        · exact h'
        · have h1 := h.erase.pend_le hpd; rw [← hmc] at h1; omega_t
      obtain rfl : tw = ts := h6 tw (hpc ▸ htp) hpd
      have hnotin : tw ∉ cx'.prom := by
        rw [hev.prom]; exact fun hm => ((List.Nodup.mem_erase_iff hi.nodup).mp hm).1 rfl
      have hnototh : ∀ (i : Nat) (t' : Thread I), i ≠ tid → c.threads[i]? = some t' → tw ∉ t'.prom := by
        intro i t' hne hi' htp'
        obtain ⟨w', hw', htid⟩ := h.erase.promWf i t' hi' tw htp'
        rw [hgts] at hw'
        cases hw'
        exact hne htid.symm
      refine .inr ⟨r, unpend g tw, _, hout P hPc fun _ => .inr hpd, E.fulfilPend hn hi hev hpd, RStep.unpend tw cx',
        hpost P _ _ (Ghost.Le.unpend g tw) (.inl ⟨by rw [hr], fun ts' hts' hpd' => ?_⟩), ⟨Ghost.Le.unpend g tw,
          fun ts' hts' ho => ?_, fun ts' hts' => (List.mem_filter.mp hts').1, fun x hx => hx,
          fun w hw => (hwl w hw) ▸ hqr⟩, hlast, fun ts' hts' hpd' => ?_, rfl, rfl, rfl, rfl, fun s hs => hs⟩
      · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hpd'
        exact hpd'.2 (h6 ts' (hprom' ts' hts') hpd'.1)
      · refine List.mem_filter.mpr ⟨hts', ?_⟩
        simp only [bne_iff_ne, ne_eq]
        rintro rfl
        rcases ho with ho | ⟨i, t', hne, hi', ho⟩
        · exact hnotin ho
        · exact hnototh i t' hne hi' ho
      · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hpd'
        exact hpd'.2 (h6 ts' (hprom' ts' hts') hpd'.1)
    · -- any other outcome overtakes the pending promise
      refine .inl (overtaken_of_inflight hc hev (hpc ▸ hts) (hmc ▸ hgts) ?_)
      rcases hev.cases with ⟨-, htp, hget⟩ | ⟨-, rfl⟩
      · have hne : tw ≠ ts := fun e => hpd (e ▸ hpts)
        exact habove tw (hpc ▸ htp) hne _ (hmc ▸ hget) rfl
      · have := cx.mem.last_le_of_get?_eq_some (hmc ▸ hgts : cx.mem.get? ts = _)
        omega_t

/-- **Store transport** (`NodeRel.store` without `InflightWritesDead`), with
the path facts: no in-flight release (`pf = none`), or the store is the
in-flight release (`pf = some (l, v)`). -/
theorem NodeRel.storeS (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf) {k : StoreKind} {l : Loc} {v : Val} (hS : pf = none ∨ pf = some (l, v))
    (hok : StoreOk A tid pl σ k false l v) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', StoreOut A tid pl σ σ' k false l v true ∧
      ErAt rF (fun _ => True) c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' cx' ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' cx' ∧ WpPath c tid t r g r' g' cx' ∧
      c.mem.last ≤ cx'.mem.last ∧ (∀ ts ∈ cx'.prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl :=
  (h.storeSG hst hS hok hc hi).imp id fun ⟨r', g', σ', h1, h2, h3, h4, h5, h6, h7, h8, _⟩ =>
    ⟨r', g', σ', h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **RMW transport at a written value the plan does not release, exposing
the ghost step** (generic form of `NodeRel.rmwSG` and
`NodeRel.rmwSGR`): `hrl0` says that a written value the plan releases would
make the RMW an effective release; `rmwSG` discharges it by `¬ effRelRmw A k`,
`rmwSGR` by a location the plan never releases. -/
theorem NodeRel.rmwSGP (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : RmwKind} {l : Loc} (hrl0 : ∀ v, (pl.rel l v = true → effRelRmw A k) → pl.rel l v = false)
    {op : Val → Option Val} (hok : RmwOk A tid pl σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOut A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
      RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') ∧
      WpPath c tid t r g r' g' (rmwAfter A k false l cx') ∧ c.mem.last ≤ (rmwAfter A k false l cx').mem.last ∧
      (∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl ∧
      (∃ tw, g' = rmwGhost g l x.1 tw false []) ∧ ¬ g.Claimed (l, x.1) ∧ x.1 < σ'.vs.getCoh l := by
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
  have hrl : pl.rel l new = false := hrl0 new fun e => (hrel e).1
  have htr : claimedSlots g l tr ≠ [] → tr ≤ (rmwAfter A k false l cx').views.wfloor := fun hne => by
    rcases hcond hne with hk | ⟨hk, hnf⟩
    · exact rmw_tr_le_wfloor_acqRel hc (by rw [hk]; rfl)
    · have hfw : ∀ f, (fenceOptCtx A (envCtx tid σ.vs c)).views.getFwd l = some f → f.time ≠ tr := by
        intro f hf ht
        rw [fenceOptCtx_views, rmwReadViews_getFwd] at hf
        exact hnf ⟨f, hf, ht⟩
      exact Nat.le_trans (rmw_tr_le_wfloor_acq hx'0 hk hfw hc'0 k false) (hcl2.rmwAfter k false l).wfloor
  have hres : (pl.afterRmw l new tr tw g σ.cl σ.r).op (Res.prod (([] : List Slot).map (·.res))) =
      (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (new, tw) := by
    simp [Plan.afterRmw, Plan.after, hrl, Res.op_unit, hr]
  have E' := E.rmw hn hi1 hev hrd hseen hnp hposr (rel := false) (fun h => absurd h Bool.false_ne_true)
    (fun _ => ⟨rfl, hgr ▸ hpure hrl⟩) hres (fun _ _ _ h => absurd trivial h)
  have hR := RStep.rmw (B := c.mem.last) (tw := tw) (rel := false) (FreshSlots.nil _) hres htr
  have hpl : pl.rel l new = true → tw ∉ ownProm tid c ∨ tw ∈ g.pend := fun h => absurd (hrl ▸ h) Bool.false_ne_true
  have hmw : ∀ y, mayWrite (pl.afterRmw l new tr tw g σ.cl σ.r) (rmwGhost g l tr tw false []) y → mayWrite r g y := by
    intro y hy
    have e : pl.afterRmw l new tr tw g σ.cl σ.r = (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (new, tw) := by
      simp [Plan.afterRmw, Plan.after, hrl, hr]
    rw [e] at hy
    exact SpinCommon.mayWrite_claim hy
  obtain ⟨hm4, hp4⟩ := rmwAfter_memProm (A := A) k false l cx'
  have hwl : ∀ w, WrittenCx c t cx' w → w.loc = l := fun w hw => writtenCx_loc hm1c hp1t hev hw
  obtain ⟨htrw, -⟩ := hev.tr tr rfl
  refine .inr ⟨_, _, { σ with
      snap := snapAfter tid c cxe₂, vs := (rmwAfter A k false l cxe₂).views
      r := pl.afterRmw l new tr tw g σ.cl σ.r, g := g
      seen := seenAfter A (A.rmwKind k).loadKind σ g l tr, fencedR := false, fencedW := false },
    ⟨c, (tr, old, cxe₁), h.anchorOk, hx'0, rfl, rfl, rfl, rfl, rfl,
      .inr ⟨new, cxe₂, tw, hop, hc'0, hev', hov, hpl, rfl, rfl, ⟨σ.cl, id, rfl⟩,
        ErAt.not_claimed_rmw E hn hi1 hev hrd hseen fun p hp hpd => absurd hpd (hnp p hp)⟩⟩, E', hR,
    ⟨snapLe_snapAfter h.ht (hcl2.mem.trans hm4.symm) (hcl2.prom.trans hp4.symm),
      Ghost.Le.rmwGhost g l tr tw false [], ⟨_, hcl2.rmwAfter k false l, rfl⟩,
      .inl ⟨rfl, fun ts hts hpd' => hn' ts (hprom' ts (hp4 ▸ hts)) hpd'⟩, fun hc0 => h.cl hc0.1,
      ⟨fun e => absurd e Bool.false_ne_true, fun e => absurd e Bool.false_ne_true⟩⟩,
    WpPath.congr ⟨Ghost.Le.rmwGhost g l tr tw false [], fun _ h _ => h, fun _ h => h, hmw,
      fun w hw => (hwl w hw) ▸ hposr⟩ hm4 hp4,
    by rw [hm4, ← hm1c]; exact hev.last_le, fun ts hts hpd' => hn' ts (hprom' ts (hp4 ▸ hts)) hpd', rfl, ⟨tw, rfl⟩,
    ErAt.not_claimed_rmw E hn hi1 hev hrd hseen (fun p hp hpd => absurd hpd (hnp p hp)),
    Nat.lt_of_lt_of_le htrw (Nat.le_trans (writeSuccs_coh_tw' hc'0 hev') ((vle_rmwAfter A k false l cxe₂).coh l))⟩

/-- **RMW transport, exposing the ghost step**: `NodeRel.rmwS`'s
conclusion, and the ghost after the RMW is `rmwGhost g l x.1 tw false []`,
the read message `(l, x.1)` was not claimed in `g`, and the env's `coh l`
after the RMW is above `x.1`. Steps that follow the RMW in the same node
(e.g. the ticket dispenser's hand-out, `NodeRel.rmwTD`) are built from it. -/
theorem NodeRel.rmwSG (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : RmwKind} (hkr : ¬ effRelRmw A k) {l : Loc} {op : Val → Option Val} (hok : RmwOk A tid pl σ k l op)
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
  h.rmwSGP hnp0 (fun v hv => by cases e : pl.rel l v with | false => rfl | true => exact absurd (hv e) hkr) hok hx hop
    hc E hi

/-- **RMW transport** (`NodeRel.rmw` without `InflightWritesDead`), with the
path facts: no release in flight, and not a release-kind RMW (**phase 1:
releases are stores**), so the written value is pure (`RmwOk`). -/
theorem NodeRel.rmwS (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hnp0 : ∀ ts ∈ t.prom, ts ∉ g.pend)
    {k : RmwKind} (hkr : ¬ effRelRmw A k) {l : Loc} {op : Val → Option Val} (hok : RmwOk A tid pl σ k l op)
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false)
    {new : Val} (hop : op x.2.1 = some new) {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0))
    (E : ErAt rF (fun _ => True) c t tid r g x.2.2) (hi : cx.Inv tid) :
    cx'.Overtaken ∨ ∃ r' g' σ', RmwOut A tid pl σ σ' k l op x.2.1 ∧ ErAt rF (fun _ => True) c t tid r' g' cx' ∧
      RStep c.mem.last r g r' g' (rmwAfter A k false l cx') ∧
      PostRel tid pl iv c t rv₀ g₀ cl₀ σ' r' g' (rmwAfter A k false l cx') ∧
      WpPath c tid t r g r' g' (rmwAfter A k false l cx') ∧ c.mem.last ≤ (rmwAfter A k false l cx').mem.last ∧
      (∀ ts ∈ (rmwAfter A k false l cx').prom, ts ∉ g'.pend) ∧ σ'.cl = σ.cl :=
  (h.rmwSG hnp0 hkr hok hx hop hc E hi).imp id fun ⟨r', g', σ', h1, h2, h3, h4, h5, h6, h7, h8, _⟩ =>
    ⟨r', g', σ', h1, h2, h3, h4, h5, h6, h7, h8⟩

end Transport

/-! ## The instance and link theorem 1 -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **Pre relation** of the side-conditioned link: `NodeRel`, with the
resource and ghost still those of the instruction's start `(rS, gS)` (no
access has happened yet). -/
def PreS (tid : Nat) (pl : Plan) (iv : InstrViews) (rF : Nat → Res) (c : Config I) (t : Thread I) (rv₀ : Res)
    (g₀ : Ghost) (cl₀ : Prop) (rS : Res) (gS : Ghost) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx) : Prop :=
  NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx ∧ r = rS ∧ g = gS

/-- **Post relation** of the side-conditioned link: `PostRel`, the path
facts from the start `(rS, gS)` (`WpPath`), world growth, no own pending
promise, and, with a release in flight (`pf ≠ none`), the env's clean flag
from `cl₀` alone. -/
def PostS (tid : Nat) (pl : Plan) (iv : InstrViews) (c : Config I) (t : Thread I) (rv₀ : Res) (g₀ : Ghost)
    (cl₀ : Prop) (pf : Option (Loc × Val)) (rS : Res) (gS : Ghost) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx) :
    Prop :=
  PostRel tid pl iv c t rv₀ g₀ cl₀ σ r g cx ∧ WpPath c tid t rS gS r g cx ∧ c.mem.last ≤ cx.mem.last ∧
    (∀ ts ∈ cx.prom, ts ∉ g.pend) ∧ (pf ≠ none → cl₀ → σ.cl)

/-- Side conditions of the link, by in-flight message `pf`: loads, RMWs and
access-free leaves only without a release in flight (RMWs not of release
kind: phase 1); stores of anything without a release in flight, else only
the in-flight store. -/
abbrev LokS (pf : Option (Loc × Val)) : Prop := pf = none
abbrev SokS (pf : Option (Loc × Val)) (l : Loc) (v : Val) : Prop := pf = none ∨ pf = some (l, v)
abbrev RokS (A : Arch) (pf : Option (Loc × Val)) (k : RmwKind) : Prop := pf = none ∧ ¬ effRelRmw A k

/-- **The per-node transport of `EnvG` with side conditions**, without
`InflightWritesDead`. -/
theorem nodeSimS_envG {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf) :
    NodeSimS A tid iv rF (fun _ => True) c t (EnvG I A tid pl) (LokS pf) (SokS pf) (RokS A pf) (LokS pf)
      (fun σ r g cx => PreS tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ r g cx) where
  pre_post := by
    rintro σ r g cx hpf ⟨h, rfl, rfl⟩
    refine ⟨h.post, WpPath.refl h.mem h.prom, by rw [h.mem]; exact Nat.le_refl _,
      fun ts hts => hst.none hpf ts (h.prom ▸ hts), fun hne => absurd hpf hne⟩
  fence_pre {k} {σ} _ _ _ h _ := ⟨fenceState σ k, fenceOut_fenceState σ k, h.1.fence k, h.2⟩
  fence_post {k} {σ} _ _ cx h _ := by
    have hm := fenceStep_mem cx k; have hp := fenceStep_prom cx k
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨fenceState σ k, fenceOut_fenceState σ k, h1.fence k, h2.congr hm hp, hm ▸ h3, hp ▸ h4, h5⟩
  load := by
    rintro k xcl addr n σ r g cx hpf ⟨h, rfl, rfl⟩ - x hx
    obtain ⟨σ', ho, hp⟩ := h.load hx
    obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
    have hm : x.2.2.mem = c.mem := hm1.trans h.mem
    have hpr : x.2.2.prom = t.prom := hp1.trans h.prom
    exact ⟨σ', ho, hp, WpPath.refl hm hpr, by rw [hm]; exact Nat.le_refl _,
      fun ts hts => hst.none hpf ts (hpr ▸ hts), fun hne => absurd hpf hne⟩
  store := by
    rintro k xcl addr n v σ r g cx hS ⟨h, rfl, rfl⟩ hok
    obtain rfl : xcl = false := hok.1
    refine ⟨fun cx' hc _ hi _ => ?_, fun hx => absurd hx Bool.false_ne_true⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    rcases h.storeS hst hS hok hc hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, hcl⟩
    · exact .inl ho
    · exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, fun _ hc0 => hcl ▸ h.cl hc0⟩
  rmw := by
    rintro k addr n op σ r g cx ⟨hpf, hkr⟩ ⟨h, rfl, rfl⟩ hok x hx
    refine ⟨fun hop => ?_, fun new hop cx' hc E hi _ => ?_⟩
    · obtain ⟨σ', ho, hp⟩ := h.rmwFail hx hop
      obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
      obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
      obtain ⟨hm2, hp2⟩ := fenceOptCtx_memProm (A := A) x.2.2
      have hm : (fenceOptCtx A x.2.2).mem = c.mem := hm2.trans (hm1.trans (hm0.trans h.mem))
      have hpr : (fenceOptCtx A x.2.2).prom = t.prom := hp2.trans (hp1.trans (hp0.trans h.prom))
      exact ⟨σ', ho, hp, WpPath.refl hm hpr, by rw [hm]; exact Nat.le_refl _,
        fun ts hts => hst.none hpf ts (hpr ▸ hts), fun hne => absurd hpf hne⟩
    · rcases h.rmwS (hst.none hpf) hkr hok hx hop hc E hi with ho | ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, -⟩
      · exact .inl ho
      · exact .inr ⟨r', g', σ', hst', E', hR, hp, hw, hl, hpd, fun hne => absurd hpf hne⟩

/-- **Link theorem 1 for `EnvG`, without `InflightWritesDead`**: as
`treeJ_envG_eraseWPRD`, for a tree whose single access satisfies the
in-flight side conditions of the start (`StartS`). -/
theorem treeJ_envG_eraseWPRDS {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDS (nodeSimS_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀)
      (cl₀ := cl₀) (rS := rS) hst) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (ha : SingleAccessS (LokS pf) (SokS pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDS _ hW ⟨h, rfl, rfl⟩ ha

/-- **Link theorem 1 at an instruction's start, without
`InflightWritesDead`**: from `EnvRel` and the hypotheses of
`ThreadRuleRX.wp`, at the start context `ctx₀`. -/
theorem treeJ_envG_eraseWPRDS_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDS (nodeSimS_envG (A := A) (pl := pl) (iv := instrViews t d) (rF := rF) (rv₀ := σ.r)
      (g₀ := g) (cl₀ := cl) (rS := r) hst) Q).W tree σ)
    (ha : SingleAccessS (LokS pf) (SokS pf) (RokS A pf) (LokS pf) tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envG_eraseWPRDS hst hW (hrel.toNodeRel rF d E hm) ha

end Link

end Kraken.Promising.SLR.EnvG
