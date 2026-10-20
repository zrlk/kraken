/-
**Part 7: the per-access verification
conditions of the x64 two-thread Treiber stack** on the adjacency environment
`EnvGCAdj`, x64 (`Arch.tso`). Thread `w` on `plan P w`
(`EnvG/X64Treiber2Ghost.lean`).

A copy of the Treiber node proof's `EnvG/Treiber2VC.lean` (same tables and proofs) at
`I := X64.isa`, `A := Arch.tso`, for the x64 program of
`Kraken/Examples/LockFree/X64/treiber2.kl`:
- the compare-and-swap is `lock cmpxchgq`'s `cmpxOp64 x y`
  (`EnvG/X64TreiberVC.lean`; `cmpxOp64_casMatch`);
- the loads of `top` are plain `movq` (kind `.acqPc` under `Arch.tso`, an
  acquire);
- the node's link is at `[n w]` (offset `0`), no data word (so no `DataOK`);
- the pop spins on an empty stack (`je pop`): `Pl.po` goes back to `Po`
  (the Treiber node proof's `vc_pop_cbz` has no counterpart);
- `rmw_success_fwd_tso`: a successful TSO RMW (fences around it) leaves its
  forwarding item at or below `vrNew` (the Treiber node proof's lemma is armv8's).

The VCs are stated at the unrestricted `EnvGCAdj`; the program runs in
`EnvGCAdjX … sAll` (`within`: `ok` gains `AccessIn sAll`, always true;
`step` unchanged), see `EnvG/X64Treiber2VCGen.lean`.

**Table predicates** (all with `Com`: the ghost facts, a share of `top`,
acquire id `w` of `top`, `top` initially `0`, `top`'s forwarding item at or
below `vrNew`): `Pu`, `Pu2 y`, `Po`, `Pl y0`, `Pr y0 u`, `DnB x`, `Dn x`.

**VCs**: `vc_push_load`, `vc_push_str`, `vc_push_cas`, `vc_pop_ldar`,
`Pl.po`, `vc_pop_ldr`, `vc_pop_cas`. The push `lock cmpxchgq`'s release
obligation uses the adjacency (`AdjAt.lastAt`).
-/
import Kraken.Promising.SLR.EnvG.X64Treiber2Final
import Kraken.Promising.SLR.EnvG.X64AdjVCGen
import Kraken.Promising.SLR.EnvG.X64TreiberVC

namespace Kraken.Promising.X64.EnvG.Treiber2X

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read? initVal_eq read?_mono read?_le_last
  prefix_append get?_of_anchor envGC_rmw_fail_getFwd)
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64 cmpxOp64_casMatch)

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- Thread `w`'s environment. -/
noncomputable abbrev EW (P : Params) (w : Nat) : SharedEnv := EnvGCAdj isa Arch.tso w (plan P w)

/-! ## Memory and step helpers -/

/-! The memory helpers are the generic `TreiberCommon` ones,
instances at `X64.isa`. -/

theorem WriteSnap.prefix {tid : Nat} {c c' : Config isa} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) : c.mem.Prefix c'.mem :=
  TreiberCommon.WriteSnap.prefix h

theorem WriteSnap.tw_le {tid : Nat} {c c' : Config isa} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) : tw ≤ c.mem.last + 1 :=
  TreiberCommon.WriteSnap.tw_le h

theorem AnchorOk.prefix {tid : Nat} {σ : EStateX} {c : Config isa} {g : Ghost} (h : AnchorOk tid σ c g) :
    σ.snap.mem.Prefix c.mem :=
  TreiberCommon.AnchorOk.prefix h

theorem DonePopAt.mono {P : Params} {w : Nat} {m m' : Memory} (h : m.Prefix m') {v : BitVec 64} {Pw tr0 : Time}
    (hd : DonePopAt P w m v Pw tr0) : DonePopAt P w m' v Pw tr0 := by
  obtain ⟨tr, Q, y0, y1, x4, tl, u, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hd
  have hQ := m.last_le_of_get?_eq_some h11
  have h0 := read?_le_last h5
  refine ⟨tr, Q, y0, y1, x4, tl, u, Memory.get?_of_prefix h.2 h1, h2, h3, h4, read?_mono h h5, h6,
    read?_mono h h7, h8, h9, fun p wm a b hg => h10 p wm a b (Memory.get?_of_prefix_le h.2 (by omega_t) hg),
    Memory.get?_of_prefix h.2 h11, read?_mono h h12, h13,
    fun p wm a b hg => h14 p wm a b (Memory.get?_of_prefix_le h.2 (by omega_t) hg)⟩

theorem DonePop.mono {P : Params} {w : Nat} {m m' : Memory} (h : m.Prefix m') {v : BitVec 64}
    (hd : DonePop P w m v) : DonePop P w m' v :=
  let ⟨Pw, tr0, hd⟩ := hd; ⟨Pw, tr0, hd.mono h⟩

theorem DoneCbz.mono {P : Params} {w : Nat} {m m' : Memory} (h : m.Prefix m') {R : Res}
    (hd : DoneCbz P w m R) : DoneCbz P w m' R := by
  obtain ⟨hq, Pw, r, y0, h1, h2, h3, h4⟩ := hd
  exact ⟨hq, Pw, r, y0, Memory.get?_of_prefix h.2 h1, h2, read?_mono h h3, h4⟩

/-- **A successful TSO RMW** (`lock`-prefixed, fenced: `rmwFence`) leaves its
forwarding item at or below `vrNew` (the TSO counterpart of
`TreiberCommon.rmw_success_fwd`, armv8's). -/
theorem rmw_success_fwd_tso {tid : Nat} {pl : Plan} {σ σ' : EStateX} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old new : Val} (h : (EnvGC isa Arch.tso tid pl).step (.rmw .acqRel addr n op) σ old σ')
    (hop : op old = some new) : ∀ f, σ'.vs.getFwd ⟨addr, n⟩ = some f → f.time ≤ σ'.vs.vrNew := by
  obtain ⟨c, x, -, -, -, -, -, -, -, hbr⟩ := (h : RmwOutC Arch.tso tid pl σ σ' .acqRel ⟨addr, n⟩ op old)
  rcases hbr with ⟨hon, -⟩ | ⟨new', cx', tw, -, hc, hev, -, -, -, hvs, -⟩
  · rw [hop] at hon; cases hon
  intro f hf
  obtain ⟨-, hwv⟩ := writeSuccs_at Arch.tso tid hc hev
  obtain ⟨f0, hf0, ht0⟩ := hwv.fwd
  have hcoh := hwv.coh
  rw [hvs] at hf ⊢
  simp only [rmwAfter, rmwPost, show Arch.tso.rmwFence = true from rfl,
    show (Arch.tso.rmwKind .acqRel == .acqRel) = true from rfl, Bool.not_false, Bool.and_self, ↓reduceIte,
    fenceStep] at hf ⊢
  change cx'.views.getFwd ⟨addr, n⟩ = some f at hf
  rw [hf0] at hf
  cases hf
  rw [ht0]
  omega_t

/-! ## The table predicates -/

/-- `top`'s forwarding item is at or below `vrNew`. -/
def FwdOK (P : Params) (σ : EStateX) : Prop := ∀ f, σ.vs.getFwd P.top = some f → f.time ≤ σ.vs.vrNew

/-- **The common facts** of thread `w`. -/
def Com (P : Params) (w : Nat) (σ : EStateX) : Prop :=
  GW P σ.g ∧ 0 < (σ.r.wr P.top).q ∧ 1 ≤ σ.r.acq P.top w ∧ σ.snap.mem.initVal P.top = 0 ∧ FwdOK P σ

/-- **`push`**. -/
def Pu (P : Params) (w : Nat) (σ : EStateX) : Prop :=
  Com P w σ ∧ ¬ Pushed P σ.r ∧ (σ.r.wr (P.nd w)).q = 1 ∧
    (∀ p, (σ.r.wr (P.nd w)).X p → p.2 ≤ σ.vs.getCoh (P.nd w)) ∧ (σ.r.wr (P.pt w)).q = 1

/-- **After the link store** of `y`. -/
def Pu2 (P : Params) (w : Nat) (y : Val) (σ : EStateX) : Prop :=
  Com P w σ ∧ ¬ Pushed P σ.r ∧ (σ.r.wr (P.nd w)).q = 1 ∧
    (∃ t, (σ.r.wr (P.nd w)).X (y, t) ∧ (∀ p, (σ.r.wr (P.nd w)).X p → p.2 ≤ t) ∧ t ≤ σ.vs.vwOld ∧
      t ≤ σ.vs.getCoh (P.nd w)) ∧ (σ.r.wr (P.pt w)).q = 1

/-- The push message `Pw` and the pop token. -/
def PoF (P : Params) (w : Nat) (σ : EStateX) (Pw : Time) : Prop :=
  σ.snap.mem.get? Pw = some ⟨P.top, P.nv w, w⟩ ∧ Pw ≤ σ.vs.getCoh P.top ∧ (σ.r.wr P.top).X (P.nv w, Pw) ∧
    1 ≤ (σ.r.wr (P.pt w)).q

/-- **`pop`**. -/
def Po (P : Params) (w : Nat) (σ : EStateX) : Prop := Com P w σ ∧ ∃ Pw, PoF P w σ Pw

/-- **After `movq (top),%rax`** of `y0`. -/
def Pl (P : Params) (w : Nat) (y0 : Val) (σ : EStateX) : Prop :=
  Com P w σ ∧ ∃ Pw tr0, PoF P w σ Pw ∧ Pw ≤ tr0 ∧ σ.snap.mem.read? P.top tr0 = some y0 ∧ tr0 ≤ σ.vs.vrNew

/-- **After `movq (%rax),%rcx`** of `u`. -/
def Pr (P : Params) (w : Nat) (y0 u : Val) (σ : EStateX) : Prop :=
  Com P w σ ∧ ∃ Pw tr0 tl, PoF P w σ Pw ∧ Pw ≤ tr0 ∧ σ.snap.mem.read? P.top tr0 = some y0 ∧ tr0 ≤ σ.vs.vrNew ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y0, 8⟩ tl = some u ∧
    ∀ p wm, tl < p → p ≤ tr0 → σ.snap.mem.get? p = some wm → wm.loc ≠ ⟨BitVec.setWidth 64 y0, 8⟩

/-- **`done`** with `r12 = x10`. -/
def Dn (P : Params) (w : Nat) (x10 : BitVec 64) (σ : EStateX) : Prop :=
  Com P w σ ∧ (DonePop P w σ.snap.mem x10 ∨ DoneCbz P w σ.snap.mem σ.r)

/-- **After a successful pop `lock cmpxchgq`**: `DonePopAt` with its `ldar` read at
or below `vrNew` (`treiber2`'s data load reads after it). -/
def DnB (P : Params) (w : Nat) (x10 : BitVec 64) (σ : EStateX) : Prop :=
  Com P w σ ∧ ∃ Pw tr0, tr0 ≤ σ.vs.vrNew ∧ DonePopAt P w σ.snap.mem x10 Pw tr0

theorem DnB.dn {P : Params} {w : Nat} {x : BitVec 64} {σ : EStateX} (h : DnB P w x σ) : Dn P w x σ :=
  let ⟨hc, Pw, tr0, _, hd⟩ := h; ⟨hc, .inl ⟨Pw, tr0, hd⟩⟩

/-! ## Fences -/

section Fence

variable {P : Params} {w : Nat} {σ σ' : EStateX}

theorem Com.fence (h : Com P w σ) (hf : FenceLe σ σ') : Com P w σ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨hf.g ▸ h1, hf.r ▸ h2, hf.r ▸ h3, hf.snap ▸ h4, fun f hfw => ?_⟩
  rw [hf.getFwd] at hfw
  exact Nat.le_trans (h5 f hfw) hf.vrNew

theorem PoF.fence {Pw : Time} (h : PoF P w σ Pw) (hf : FenceLe σ σ') : PoF P w σ' Pw := by
  unfold PoF; rw [hf.r, hf.snap, hf.getCoh]; exact h

theorem Pu.fence (h : Pu P w σ) (hf : FenceLe σ σ') : Pu P w σ' := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := h
  refine ⟨h1.fence hf, hf.r ▸ h2, hf.r ▸ h3, ?_, hf.r ▸ h6⟩
  rw [hf.r, hf.getCoh]; exact h4

theorem Pu2.fence {y : Val} (h : Pu2 P w y σ) (hf : FenceLe σ σ') : Pu2 P w y σ' := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := h
  refine ⟨h1.fence hf, hf.r ▸ h2, hf.r ▸ h3, ?_, hf.r ▸ h6⟩
  rw [hf.r, hf.getCoh, hf.vwOld]; exact h4

theorem Po.fence (h : Po P w σ) (hf : FenceLe σ σ') : Po P w σ' :=
  ⟨h.1.fence hf, h.2.imp fun _ h => h.fence hf⟩

theorem Pl.fence {y0 : Val} (h : Pl P w y0 σ) (hf : FenceLe σ σ') : Pl P w y0 σ' := by
  obtain ⟨h1, Pw, tr0, h2, h3, h4, h5⟩ := h
  exact ⟨h1.fence hf, Pw, tr0, h2.fence hf, h3, hf.snap ▸ h4, Nat.le_trans h5 hf.vrNew⟩

theorem Pr.fence {y0 u : Val} (h : Pr P w y0 u σ) (hf : FenceLe σ σ') : Pr P w y0 u σ' := by
  obtain ⟨h1, Pw, tr0, tl, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1.fence hf, Pw, tr0, tl, h2.fence hf, h3, hf.snap ▸ h4, Nat.le_trans h5 hf.vrNew, hf.snap ▸ h6,
    hf.snap ▸ h7⟩

theorem Dn.fence {x : BitVec 64} (h : Dn P w x σ) (hf : FenceLe σ σ') : Dn P w x σ' := by
  unfold Dn; rw [hf.snap, hf.r]; exact ⟨h.1.fence hf, h.2⟩

theorem DnB.fence {x : BitVec 64} (h : DnB P w x σ) (hf : FenceLe σ σ') : DnB P w x σ' := by
  obtain ⟨h1, Pw, tr0, h2, h3⟩ := h
  exact ⟨h1.fence hf, Pw, tr0, Nat.le_trans h2 hf.vrNew, hf.snap ▸ h3⟩

end Fence

/-! ## Steps that keep the resource -/

section Keep

variable {P : Params} {w : Nat} {σ σ' : EStateX}

/-- `Com` after a load. -/
theorem Com.load {k : LoadKind} {l : Loc} {v : Val} (h : Com P w σ)
    (hf : LoadFacts Arch.tso w σ σ' k l v) : Com P w σ' := by
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, by rw [initVal_eq hanc.snap.init]; exact h4, fun f hfw => ?_⟩
  rw [hlv.getFwd] at hfw
  exact Nat.le_trans (h5 f hfw) hlv.mono.vrNew

theorem PoF.load {k : LoadKind} {l : Loc} {v : Val} {Pw : Time} (h : PoF P w σ Pw)
    (hf : LoadFacts Arch.tso w σ σ' k l v) : PoF P w σ' Pw := by
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨get?_of_anchor hanc h1, Nat.le_trans h2 (hlv.mono.coh _), hr ▸ h3, hr ▸ h4⟩

/-- `Com` after a failed RMW. -/
theorem Com.rmwFail {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}
    (h : Com P w σ) (hs : (EnvGC isa Arch.tso w (plan P w)).step (.rmw k addr n op) σ old σ')
    (hop : op old = none) : Com P w σ' := by
  obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs
  rcases hbr with ⟨-, hsnap, hr⟩ | ⟨new, -, hon, -⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, by rw [hsnap, initVal_eq hanc.snap.init]; exact h4,
      fun f hfw => ?_⟩
    rw [envGC_rmw_fail_getFwd hs hop] at hfw
    exact Nat.le_trans (h5 f hfw) hvle.vrNew
  · rw [hop] at hon; cases hon

end Keep

/-! ## The split at `top` -/

theorem keep_wr_top (P : Params) (w : Nat) (cl : Prop) (r : Res) :
    ((split P w).keep cl r).wr P.top = r.wr P.top := by
  by_cases h : Pushed P r
  · rw [split_keep_pushed h]; simp [Res.drop, top_pt]
  · rw [split_keep_fresh h]; simp [Res.drop, top_not_mem_nodeL]

theorem keep_acq_top (P : Params) (w : Nat) (cl : Prop) (r : Res) (ι : PredId) :
    ((split P w).keep cl r).acq P.top ι = r.acq P.top ι := by
  by_cases h : Pushed P r
  · rw [split_keep_pushed h]; simp [Res.drop, top_pt]
  · rw [split_keep_fresh h]; simp [Res.drop, top_not_mem_nodeL]

theorem pt_not_mem_nodeL (P : Params) (w : Nat) : P.pt w ∉ nodeL P w := by
  simp only [nodeL, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_and]
  intro h
  exact absurd h.symm (nd_pt P w w)

/-- The resource after a successful `lock cmpxchgq` on `top`. -/
theorem after_top_facts (P : Params) (w : Nat) (new : Val) (tw : Time) (cl : Prop) (r C : Res)
    (hq : 0 < (r.wr P.top).q) :
    0 < ((((plan P w).after P.top new tw cl r).op C).wr P.top).q ∧
      r.acq P.top w ≤ (((plan P w).after P.top new tw cl r).op C).acq P.top w ∧
      ((((plan P w).after P.top new tw cl r).op C).wr P.top).X (new, tw) := by
  rw [plan_after_top]
  refine ⟨?_, ?_, ?_⟩
  · show 0 < ((((split P w).keep cl r).addW P.top (new, tw)).wr P.top).q + (C.wr P.top).q
    rw [Res.addW_q, keep_wr_top]
    have := (C.wr P.top).nonneg
    grind
  · show r.acq P.top w ≤ (((split P w).keep cl r).addW P.top (new, tw)).acq P.top w + C.acq P.top w
    rw [Res.addW_acq, keep_acq_top]; omega
  · refine .inl ?_
    rw [Res.addW_X_self, keep_wr_top]
    exact .inr ⟨hq, rfl⟩

/-! ## The push -/

section Push

variable {P : Params} {w : Nat}

/-- **VC of a push load** (`movq (top),%rax`): `Pu` is kept. -/
theorem vc_push_load (σ : EStateX) (h : Pu P w σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64} {n : Nat} :
    ∀ v (σ' : EStateX), (EW P w).step (.load k xcl a n) σ v σ' → Pu P w σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := plan P w) hs
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := id hf
  obtain ⟨h1, h2, h3, h4, h10⟩ := h
  refine ⟨h1.load hf, hr ▸ h2, hr ▸ h3, fun p hp => ?_, hr ▸ h10⟩
  rw [hr] at hp
  exact Nat.le_trans (h4 p hp) (hlv.mono.coh _)

/-- **VC `movq %rax,(%rbx)`** (the link, any value `v`): permitted (pure,
the link whole), and `(v, tw)` is the link's maximal write. -/
theorem vc_push_str (hL : TLocs P) (hw : w < 2) (σ : EStateX) (h : Pu P w σ) (v : Val) :
    (EW P w).ok (.store .plain false (P.nd w).addr (P.nd w).bytes v) σ ∧
      ∀ b (σ' : EStateX), (EW P w).step (.store .plain false (P.nd w).addr (P.nd w).bytes v) σ b σ' →
        Pu2 P w v σ' := by
  obtain ⟨⟨hW, hpos, hacq, hi, hfw⟩, hnp, hq, hX, hpt⟩ := h
  have e : ({ addr := (P.nd w).addr, bytes := (P.nd w).bytes } : Loc) = P.nd w := rfl
  have hne : P.nd w ≠ P.top := Ne.symm (hL.top_nd' hw)
  refine ⟨⟨rfl, by rw [e, hq]; decide, fun _ => by rw [e, hW.rel_ne hne]; exact Pred.emp_pure _,
    fun hr => by rw [e, plan_rel] at hr; simp [hne] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, hws, hwb, hwv, -, ⟨_, -, hr⟩, -, -⟩ := step_storeFacts (pl := plan P w) hs
  rw [e, plan_after_ne P w hne] at hr
  have hwr : ∀ x, x ≠ P.nd w → σ'.r.wr x = σ.r.wr x := fun x hx => by rw [hr, Res.addW_wr_ne _ _ hx]
  refine ⟨⟨hW.mono hanc.ghost, by rw [hwr _ (Ne.symm hne)]; exact hpos, by rw [hr, Res.addW_acq]; exact hacq,
    ?_, fun f hf => ?_⟩, ?_, by rw [hr, Res.addW_q]; exact hq, ⟨tw, ?_, ?_, hwv.vwOld (by decide), hwv.coh⟩,
    by rw [hwr _ (Ne.symm (nd_pt P w w))]; exact hpt⟩
  · rw [initVal_eq (TreiberCommon.WriteSnap.init hws), initVal_eq hanc.snap.init]; exact hi
  · rw [hwv.fwdOther _ (Ne.symm hne)] at hf
    exact Nat.le_trans (hfw f hf) hwv.mono.vrNew
  · unfold Pushed; rw [hwr _ (Ne.symm hne)]; exact hnp
  · rw [hr, Res.addW_X_self]; exact .inr ⟨by rw [hq]; decide, rfl⟩
  · intro p hp
    rw [hr, Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hX p hp) hwb.coh)
    · exact Nat.le_refl _

/-- `NoTopIn` of the push's message from adjacency at the anchor. -/
theorem noTopIn_of_adj {c : Config isa} {g : Ghost} {tr : Time} (hW : GW P g) {rF : Nat → Res} {T : Nat → Prop}
    (E : Erase rF g T c) (hadj : AdjAt w c g P.top tr (c.mem.last + 1)) (v : Val) :
    NoTopIn P (c.mem.append ⟨P.top, v, w⟩).1 tr (c.mem.last + 1) := by
  have hwi := hadj.lastAt E hW.impure
  intro p wm h1 h2 hg hl
  have hle : p ≤ c.mem.last := by omega_t
  rw [Memory.get?_append_of_le _ _ _ hle] at hg
  have : c.mem.writeIn P.top tr (c.mem.last + 1 - 1) = true :=
    (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, h1, by omega_t, hg, hl⟩
  rw [hwi] at this; cases this

/-- **VC `lock cmpxchgq %rbx,(top)`** of the push (`rax = x2`, the link's maximal
write `y` with `x2` its 64 bits, `x1` the node): permitted (the node's
release in push form: `PushF`, with `NoTopIn` from the adjacency), and every
outcome fails (`Pu2` kept) or succeeds (`Po`). -/
theorem vc_push_cas (hL : TLocs P) (hw : w < 2) (σ : EStateX) {y : Val} (h : Pu2 P w y σ) (x2 : BitVec 64)
    (hy : BitVec.setWidth 64 y = x2) :
    (EW P w).ok (.rmw .acqRel P.top.addr P.top.bytes (cmpxOp64 x2 (P.n w))) σ ∧
      ∀ old (σ' : EStateX), (EW P w).step (.rmw .acqRel P.top.addr P.top.bytes (cmpxOp64 x2 (P.n w))) σ old σ' →
        (BitVec.setWidth 64 old ≠ x2 ∧ Pu2 P w y σ') ∨ (BitVec.setWidth 64 old = x2 ∧ Po P w σ') := by
  obtain ⟨⟨hW, hpos, hacq, hi, hfw⟩, hnp, hq, ⟨t, hXt, hmt, htv, htc⟩, hpt⟩ := h
  have e : ({ addr := P.top.addr, bytes := P.top.bytes } : Loc) = P.top := rfl
  refine ⟨⟨hpos, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, ?_⟩
  · rw [e, plan_rel] at hr; simp at hr
  · rw [e]; exact hW.impure new
  · rw [e, plan_gives]; simp
  · obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    rw [e, hW.rel_top, plan_give, split_give_fresh hnp]
    have hnd : P.nd w ∈ nodeL P w := by rw [nodeL_eq hL hw]; simp
    have hon_nd : (Res.only (nodeL P w) σ.r).wr (P.nd w) = σ.r.wr (P.nd w) := by simp [Res.only, hnd]
    have hV : max (max σ.vs.vrOld σ.vs.vrOldNR) σ.vs.vwOld < c.mem.last + 1 := hwb.rel (by decide)
    have hvw : σ.vs.vwOld < c.mem.last + 1 := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hV
    obtain ⟨rF, E⟩ := hanc.erase
    intro _
    refine ⟨w, hw, Memory.get?_append_last _ _, .inl ⟨rfl, by rw [hon_nd]; exact hq,
      ⟨y, t, by rw [hon_nd]; exact hXt, by rw [hon_nd]; exact hmt, Nat.lt_of_le_of_lt htv hvw, tr, old, htr,
        read?_mono (prefix_append _ _) hrd.val, by rw [hx, hy], noTopIn_of_adj (hW.mono hanc.ghost) E hadj _⟩⟩⟩
  intro old σ' hs
  have hs' := envGCAdj_step_iff.mp hs
  rcases Classical.em (cmpxOp64 x2 (P.n w) old = none) with hon | hon
  · refine .inl ⟨(cmpxOp64_casMatch _ _).none _ hon, Com.rmwFail (⟨hW, hpos, hacq, hi, hfw⟩ : Com P w σ) hs' hon, ?_⟩
    obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
    rcases hbr with ⟨-, -, hr⟩ | ⟨new, -, hon', -⟩
    · refine ⟨by unfold Pushed; rw [hr]; exact hnp, hr ▸ hq, ⟨t, hr ▸ hXt, hr ▸ hmt, Nat.le_trans htv hvle.vwOld,
        Nat.le_trans htc (hvle.coh _)⟩, hr ▸ hpt⟩
    · rw [hon] at hon'; cases hon'
  obtain ⟨new, hon⟩ := Option.ne_none_iff_exists'.mp hon
  obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
  refine .inr ⟨hx, ?_⟩
  obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon', -⟩ | ⟨new', tw, hon', htrw, -, hws, -, htwc, -, -, ⟨Pc, -, hr⟩, -⟩
  · rw [hon] at hon'; cases hon'
  rw [hon] at hon'; cases hon'
  rw [e] at hr hws htwc
  obtain ⟨hq', hacq', hX'⟩ := after_top_facts P w (BitVec.setWidth 128 (P.n w)) tw Pc σ.r _ hpos
  rw [← hr] at hq' hacq' hX'
  refine ⟨⟨hW.mono hanc.ghost, hq', Nat.le_trans hacq hacq', ?_, ?_⟩, tw, TreiberCommon.WriteSnap.get?_new hws, htwc, hX', ?_⟩
  · rw [initVal_eq (TreiberCommon.WriteSnap.init hws), initVal_eq hanc.snap.init]; exact hi
  · have := rmw_success_fwd_tso hs' hon
    exact this
  · rw [hr, plan_after_top, split_keep_fresh hnp]
    show 1 ≤ (((Res.drop (nodeL P w) σ.r).addW P.top _).wr (P.pt w)).q + _
    rw [Res.addW_wr_ne _ _ (Ne.symm (top_pt P w))]
    simp only [Res.drop, pt_not_mem_nodeL, ↓reduceIte]
    have := ((Res.prod ((claimSlotsC Arch.tso RmwKind.acqRel σ.vs σ'.g ⟨P.top.addr, P.top.bytes⟩ tr).map (·.res))).wr
      (P.pt w)).nonneg
    rw [hpt]; grind

end Push

/-! ## The pop -/

section Pop

variable {P : Params} {w : Nat}

/-- **VC `movq (top),%rax`** of the pop (a plain load: an acquire under
`Arch.tso`): `Pl` of the value read (at `tr0 ≥ Pw`, `tr0 ≤ vrNew`). -/
theorem vc_pop_ldar (σ : EStateX) (h : Po P w σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (EW P w).step (.load .plain xcl P.top.addr P.top.bytes) σ v σ' → Pl P w v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := plan P w) hs
  obtain ⟨hcom, Pw, hPo⟩ := h
  refine ⟨hcom.load hf, Pw, ?_⟩
  have hPo' := hPo.load hf
  obtain ⟨hanc, hr, -, tr0, hrd, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, h4⟩ := hPo
  have e : ({ addr := P.top.addr, bytes := P.top.bytes } : Loc) = P.top := rfl
  rw [e] at hrd hlv
  refine ⟨tr0, hPo', ?_, hrd.val, ?_⟩
  · refine Nat.le_of_not_lt fun hlt => ?_
    have hB : Pw ≤ readBound Arch.tso σ.vs .plain P.top := Nat.le_trans h2 (Nat.le_max_right _ _)
    have := (Memory.writeIn_iff _ _ _ _).mpr ⟨Pw, _, hlt, hB, get?_of_anchor hanc h1, rfl⟩
    rw [hrd.window] at this; cases this
  · by_cases hfw : Fwded σ.vs P.top tr0
    · obtain ⟨f, hf, rfl⟩ := hfw
      exact Nat.le_trans (hcom.2.2.2.2 f hf) hlv.mono.vrNew
    · exact (hlv.acq (by decide) hfw).1

/-- **`je pop` taken** (the stack read empty): back to `Po`. -/
theorem Pl.po {σ : EStateX} {y0 : Val} (h : Pl P w y0 σ) : Po P w σ :=
  let ⟨hcom, Pw, _, hPo, _⟩ := h; ⟨hcom, Pw, hPo⟩

/-- **VC `movq (%rax),%rcx`** of the pop (`rax` the 64 bits of `y0`): `Pr`
of the value read, its window covering `tr0`. -/
theorem vc_pop_ldr (σ : EStateX) {y0 : Val} (h : Pl P w y0 σ) {xcl : Bool} :
    ∀ u (σ' : EStateX), (EW P w).step (.load .plain xcl (BitVec.setWidth 64 y0) 8) σ u σ' →
      Pr P w y0 u σ' := by
  intro u σ' hs
  have hf := step_loadFacts (pl := plan P w) hs
  obtain ⟨hcom, Pw, tr0, hPo, h1, h2, h3⟩ := h
  refine ⟨hcom.load hf, Pw, tr0, ?_⟩
  have hPo' := hPo.load hf
  obtain ⟨hanc, hr, -, tl, hrd, hlv, -⟩ := hf
  refine ⟨tl, hPo', h1, hanc.read? h2, Nat.le_trans h3 hlv.mono.vrNew, hrd.val, fun p wm a b hg hl => ?_⟩
  have := (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, a, Nat.le_trans b (Nat.le_trans h3
    (le_readBound_vrNew Arch.tso σ.vs .plain ⟨BitVec.setWidth 64 y0, 8⟩)), hg, hl⟩
  rw [hrd.window] at this; cases this

/-- **VC `lock cmpxchgq %rcx,(top)`** of the pop (`rax` the 64 bits of
`y0`, `rax ≠ 0`, `rcx` the 64 bits of `u`): permitted (the pop token's release in
pop form: `PopF` with the push message), and every outcome fails (`Po`) or
succeeds (`DnB x2`: `DonePopAt`, its `ldar` read at or below `vrNew`). -/
theorem vc_pop_cas (hw : w < 2) (σ : EStateX) {y0 u : Val} (h : Pr P w y0 u σ) (hx2 : BitVec.setWidth 64 y0 ≠ 0) :
    (EW P w).ok (.rmw .acqRel P.top.addr P.top.bytes
        (cmpxOp64 (BitVec.setWidth 64 y0) (BitVec.setWidth 64 u))) σ ∧
      ∀ old (σ' : EStateX), (EW P w).step (.rmw .acqRel P.top.addr P.top.bytes
          (cmpxOp64 (BitVec.setWidth 64 y0) (BitVec.setWidth 64 u))) σ old σ' →
        (BitVec.setWidth 64 old ≠ BitVec.setWidth 64 y0 ∧ Po P w σ') ∨
          (BitVec.setWidth 64 old = BitVec.setWidth 64 y0 ∧ DnB P w (BitVec.setWidth 64 y0) σ') := by
  obtain ⟨hcom, Pw, tr0, tl, ⟨h1, h2, h3, h4⟩, h5_le, h5, h6, h7, h8⟩ := h
  obtain ⟨hW, hpos, hacq, hi, hfw⟩ := hcom
  have hpush : Pushed P σ.r := ⟨_, h3, get?_ne_zero h1⟩
  have e : ({ addr := P.top.addr, bytes := P.top.bytes } : Loc) = P.top := rfl
  refine ⟨⟨hpos, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, ?_⟩
  · rw [e, plan_rel] at hr; simp at hr
  · rw [e]; exact hW.impure new
  · rw [e, plan_gives]; simp
  · rw [e, hW.rel_top, plan_give, split_give_pushed hpush]
    intro _
    refine ⟨w, hw, Memory.get?_append_last _ _, .inr ⟨by simpa [Res.only] using h4, Pw,
      Nat.lt_of_le_of_lt h2 hwb.coh, ?_⟩⟩
    have hle : Pw ≤ c.mem.last := c.mem.last_le_of_get?_eq_some (get?_of_anchor hanc h1)
    rw [Memory.get?_append_of_le _ _ _ hle]
    exact get?_of_anchor hanc h1
  intro old σ' hs
  have hs' := envGCAdj_step_iff.mp hs
  obtain ⟨c, tr, hanc, hrd, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, hsnap, hr⟩ | ⟨new, tw, hon, htrw, hat, hws, -, -, -, -, ⟨Pc, -, hr⟩, -⟩
  · -- failure: back to `pop`
    refine .inl ⟨(cmpxOp64_casMatch _ _).none _ hon, Com.rmwFail (⟨hW, hpos, hacq, hi, hfw⟩ : Com P w σ) hs' hon, Pw, ?_, ?_, hr ▸ h3,
      hr ▸ h4⟩
    · rw [hsnap]; exact get?_of_anchor hanc h1
    · exact Nat.le_trans h2 (hvle.coh _)
  -- success
  obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
  refine .inr ⟨hx, ?_⟩
  rw [e] at hrd hat hws hr
  have hpre : σ.snap.mem.Prefix σ'.snap.mem := (AnchorOk.prefix hanc).trans (WriteSnap.prefix hws)
  obtain ⟨hq', hacq', -⟩ := after_top_facts P w (BitVec.setWidth 128 (BitVec.setWidth 64 u)) tw Pc σ.r _ hpos
  rw [← hr] at hq' hacq'
  refine ⟨⟨hW.mono hanc.ghost, hq', Nat.le_trans hacq hacq', ?_, ?_⟩, Pw, tr0, Nat.le_trans h6 hvle.vrNew, ?_⟩
  · rw [initVal_eq (TreiberCommon.WriteSnap.init hws), initVal_eq hanc.snap.init]; exact hi
  · exact rmw_success_fwd_tso hs' hon
  -- the `cmpxchgq` read is at or after the first load's
  have htr0 : tr0 ≤ tr := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have h0 : tr0 ≠ 0 := by omega_t
    obtain ⟨wm, hg, hl, -⟩ := get?_of_read? h0 (hanc.read? h5)
    have hfv : σ.vs.vrNew ≤ (rmwReadViews Arch.tso σ.vs).vrNew := by
      simp only [rmwReadViews, fenceViews, fenceStep, show Arch.tso.rmwFence = true from rfl, ↓reduceIte]
      exact Nat.le_max_left _ _
    have hB : tr0 ≤ readBound Arch.tso (rmwReadViews Arch.tso σ.vs) (Arch.tso.rmwKind .acqRel).loadKind P.top :=
      Nat.le_trans h6 (Nat.le_trans hfv (le_readBound_vrNew _ _ _ _))
    have := (Memory.writeIn_iff _ _ _ _).mpr ⟨tr0, wm, hlt, hB, hg, hl⟩
    rw [hrd.window] at this; cases this
  have hle_tw : tw ≤ c.mem.last + 1 := WriteSnap.tw_le hws
  refine ⟨tr, tw, y0, old, BitVec.setWidth 64 u, tl, u, Memory.get?_of_prefix hpre.2 h1, h5_le, htr0,
    htrw, read?_mono hpre h5, rfl, read?_mono (WriteSnap.prefix hws) hrd.val, hx, hx2, ?_, TreiberCommon.WriteSnap.get?_new hws,
    read?_mono hpre h7, rfl, ?_⟩
  · intro p wm a b hg hl
    have hp : p ≤ c.mem.last := by omega_t
    exact atomic_between hat hrd.val a b (Memory.get?_of_prefix_le (WriteSnap.prefix hws).2 hp hg) hl
  · intro p wm a b hg
    have hp : p ≤ σ.snap.mem.last := Nat.le_trans b (read?_le_last h5)
    exact h8 p wm a b (Memory.get?_of_prefix_le hpre.2 hp hg)

end Pop

end Kraken.Promising.X64.EnvG.Treiber2X
