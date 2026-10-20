/-
Part 4: **the per-access verification conditions
of `treiber2_arm.kl`** on the adjacency environment `EnvGCAdj`, AArch64
(`Arch.armv8`). Thread `w` on the empty plan `planA` with the ghost-free `top`
(`EnvG/Treiber2ArmGhost.lean`).

## Two semantic facts (from the existing `readSuccs`/`writeSuccs`, no hypothesis)

- `rmw_success_fwd_rel`: a successful armv8 **release** RMW (the push `casl`)
  leaves its forwarding item at or below `vRel` (`writeSuccs` with a release
  store kind raises `vRel` to the write's timestamp).
  `Treiber.rmw_success_fwd` (the item at or below `vrNew`) holds only for
  `.acqRel`, whose post-view takes `coh`; a `casl`/`cas` does not raise `vrNew`.
  (`rmw_success_fwd_xcl`: the item of any successful armv8 RMW is exclusive;
  that no longer keeps an acquire load from taking its forwarding view.)
- `load_acq_vrNew`: an armv8 acquire load whose forwarding item is at or below
  `vrNew` or `vRel` reads at or below its new `vrNew`: an acquire load's
  pre-view includes `vRel`. An acquire load may take the forwarding view of
  the thread's own exclusive write (herd's `aarch64.cat` has
  `aob = [Exp & M]; rmw; lrs; [A | Q]`, which orders only the exclusive
  pair's read before it), so the item's timestamp must be bounded by the
  pre-view; the release `casl` is ordered before a later `ldar` by `bob`'s
  `[L]; po; [A]`.

So the table invariant is `FwdOKX` (new, beside the existing `Treiber2.FwdOK`,
which implies it: `FwdOKX.of_fwdOK`). After a successful pop `cas` (a plain
RMW, whose item is bounded by neither) no acquire load of `top` follows, so
`DnBA`/`DnDA` keep only `ComDA` (`ComA` without `FwdOKX`).

## Table predicates (with `ComA`: the ghost facts, half of `top`, acquire id
`w`, `top` initially `0`, `FwdOKX`)

- `Pu0A` (`worker`), `PuA` (`push`), `Pu2A y` (after the link store): `top`'s
  write set initial (`NoWA`), the link whole (and the data word whole, with
  `Treiber2.DataOK` after its store);
- `PoA` (`pop`): `KeptA` at the push message `Pw` (link value `y`), `Pw ≤ coh`,
  `top`'s write set `{0, Pw}`;
- `PlA y0` (after `ldar`), `PrA y0 u` (after the link `ldr`): as
  `Treiber2.Pl`/`Pr` on `PoA`;
- `DnBA x` (after a successful pop `cas`): a popped `SideA` with `v = x`, its
  `ldar` read at or below `vrNew`;
- `DnDA x10 x11` (`done`): `DoneRA` (`EnvG/Treiber2ArmFinal.lean`).

## VCs

`vc_data_strA`, `vc_push_loadA`, `vc_push_strA`, `vc_push_casA` (any RMW kind
that does not claim and stores as a release: `casl`), `vc_pop_ldarA`,
`vc_pop_cbzA`, `vc_pop_ldrA`, `vc_pop_casA` (any non-claiming RMW kind:
`cas`), `vc_ldr_dataA`. The push `casl`'s read `tr` with only own messages of
`top` strictly between it and the push comes from the RMW's atomicity
(`atomic_between`), not from `AdjAt.lastAt` (which needs an impure `top`).
-/
import Kraken.Promising.SLR.EnvG.Treiber2ArmFinal
import Kraken.Promising.SLR.EnvG.Treiber2VC

namespace Kraken.Promising.SLR.EnvG.Treiber2Arm

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.Treiber2 (Params TLocs DataOK DataOK.fence nd_dd dd_pt top_dd Side)
open Kraken.Promising.SLR.EnvG.Treiber (casOp64 casOp64_some casOp64_none initVal_eq get?_of_anchor
  envGC_rmw_fail_getFwd)
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_mono)

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- Thread `w`'s environment: `EnvGCAdj` on the empty plan. -/
noncomputable abbrev EWA (w : Nat) : SharedEnv := EnvGCAdj isa Arch.armv8 w planA

/-! ## Forwarding -/

/-- A write of an exclusive (`xcl = true`) leaves an exclusive forwarding item. -/
theorem writeSuccs_fwd_xcl {A : Arch} {tid : Nat} {iv : InstrViews} {c c2 : Ctx} {k : StoreKind} {l : Loc}
    {v : Val} {tr : Option Time} {extra : View} (hc : c2 ∈ writeSuccs A tid iv c k true l v tr extra)
    {f : FwdItem} (hf : c2.views.getFwd l = some f) : f.xcl = true := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, -, w, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩ <;>
  · simp only [afterWrite, Views.getFwd, Views.setFwd, Views.find?_setSorted] at hf
    simp at hf
    rw [← hf]

/-- **A successful armv8 RMW of any kind** leaves an exclusive forwarding item
at its location (the `_xcl` variant of `Treiber.rmw_success_fwd`). -/
theorem rmw_success_fwd_xcl {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old new : Val} (h : (EnvGC isa Arch.armv8 tid pl).step (.rmw k addr n op) σ old σ')
    (hop : op old = some new) : ∀ f, σ'.vs.getFwd ⟨addr, n⟩ = some f → f.xcl = true := by
  obtain ⟨c, x, -, -, -, -, -, -, -, hbr⟩ := (h : RmwOutC Arch.armv8 tid pl σ σ' k ⟨addr, n⟩ op old)
  rcases hbr with ⟨hon, -⟩ | ⟨new', cx', tw, -, hc, hev, -, -, -, hvs, -⟩
  · rw [hop] at hon; cases hon
  intro f hf
  rw [hvs] at hf
  simp only [rmwAfter, rmwPost, show Arch.armv8.rmwFence = false from rfl, Bool.false_eq_true, ↓reduceIte] at hf
  split at hf <;> exact writeSuccs_fwd_xcl hc hf

/-- A release write leaves a forwarding item at or below `vRel`. -/
theorem writeSuccs_fwd_rel {A : Arch} {tid : Nat} {iv : InstrViews} {c c2 : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} (hc : c2 ∈ writeSuccs A tid iv c k xcl l v tr extra)
    (hk : A.storeKind k = .rel) {f : FwdItem} (hf : c2.views.getFwd l = some f) : f.time ≤ c2.views.vRel := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, -, w, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩ <;>
  · simp only [afterWrite, Views.getFwd, Views.setFwd, Views.find?_setSorted] at hf ⊢
    simp at hf
    rw [← hf]; simp only [hk]; exact Nat.le_max_right _ _

/-- **A successful armv8 release RMW** leaves a forwarding item at or below
`vRel` at its location. -/
theorem rmw_success_fwd_rel {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old new : Val} (h : (EnvGC isa Arch.armv8 tid pl).step (.rmw k addr n op) σ old σ')
    (hrel : Arch.armv8.storeKind (Arch.armv8.rmwKind k).storeKind = .rel)
    (hop : op old = some new) : ∀ f, σ'.vs.getFwd ⟨addr, n⟩ = some f → f.time ≤ σ'.vs.vRel := by
  obtain ⟨c, x, -, -, -, -, -, -, -, hbr⟩ := (h : RmwOutC Arch.armv8 tid pl σ σ' k ⟨addr, n⟩ op old)
  rcases hbr with ⟨hon, -⟩ | ⟨new', cx', tw, -, hc, hev, -, -, -, hvs, -⟩
  · rw [hop] at hon; cases hon
  intro f hf
  rw [hvs] at hf ⊢
  simp only [rmwAfter, rmwPost, show Arch.armv8.rmwFence = false from rfl, Bool.false_eq_true, ↓reduceIte] at hf ⊢
  split at hf <;> split <;> first | exact writeSuccs_fwd_rel hc hrel hf | (simp_all)

/-- **An armv8 acquire load** of `l` whose forwarding item is at or below
`vrNew` or `vRel`: it reads some `tr` with no write to `l` in `(tr, coh l]`,
and `tr` is at or below the new `vrNew` (an acquire load's pre-view includes
`vRel`, `readPre`). -/
theorem load_acq_vrNew {tid : Nat} {pl : Plan} {σ σ' : State isa} {xcl : Bool} {addr : BitVec 64} {n : Nat}
    {v : Val} (h : (EnvGC isa Arch.armv8 tid pl).step (.load .acq xcl addr n) σ v σ')
    (hfw : ∀ f, σ.vs.getFwd ⟨addr, n⟩ = some f → f.time ≤ σ.vs.vrNew ∨ f.time ≤ σ.vs.vRel) :
    ∃ tr, σ'.snap.mem.read? ⟨addr, n⟩ tr = some v ∧
      (∀ p wm, tr < p → p ≤ σ.vs.getCoh ⟨addr, n⟩ → σ'.snap.mem.get? p = some wm → wm.loc ≠ ⟨addr, n⟩) ∧
      tr ≤ σ'.vs.vrNew := by
  obtain ⟨-, -, -, tr, cx', hx, hvs, -⟩ := (h : LoadOut Arch.armv8 tid σ σ' .acq xcl ⟨addr, n⟩ v)
  obtain ⟨t, v', he, -, hrd, hwin, -⟩ := (mem_readSuccs Arch.armv8).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  subst h1 h2 h3
  refine ⟨_, hrd, fun p wm h1 h2 hg hl => ?_, ?_⟩
  · have := (Memory.writeIn_iff (envCtx tid σ.vs σ'.snap).mem _ _
      (max (readPre Arch.armv8 iv0 (envCtx tid σ.vs σ'.snap) LoadKind.acq)
        ((envCtx tid σ.vs σ'.snap).views.getCoh ⟨addr, n⟩))).mpr
      ⟨p, wm, h1, Nat.le_trans h2 (Nat.le_max_right _ _), hg, hl⟩
    rw [hwin] at this; cases this
  rw [hvs]
  simp only [readNext, readView]
  have hk : (Arch.armv8.loadKind LoadKind.acq).isAcquire = true := rfl
  simp only [hk, ↓reduceIte, envCtx_views]
  rcases hf : σ.vs.getFwd ⟨addr, n⟩ with _ | f
  · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  · simp only
    by_cases ht : f.time = tr
    · rcases hfw f hf with hle | hx
      · rw [← ht]; exact Nat.le_trans hle (Nat.le_max_left _ _)
      · have : σ.vs.vRel ≤ readPre Arch.armv8 iv0 (envCtx tid σ.vs σ'.snap) LoadKind.acq := by
          simp only [readPre, envCtx_views]; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        rw [← ht]
        exact Nat.le_trans hx (Nat.le_trans this (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
    · simp only [ht, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- `0 < 1/2` in `Rat`. -/
theorem half_posA : (0 : Rat) < 1 / 2 := by grind

/-! ## The table predicates -/

/-- `top`'s forwarding item is at or below `vrNew` or `vRel`. -/
def FwdOKX (P : Params) (σ : State isa) : Prop :=
  ∀ f, σ.vs.getFwd P.top = some f → f.time ≤ σ.vs.vrNew ∨ f.time ≤ σ.vs.vRel

theorem FwdOKX.of_fwdOK {P : Params} {σ : State isa} (h : Treiber2.FwdOK P σ) : FwdOKX P σ :=
  fun f hf => .inl (h f hf)

/-- **The common facts** of thread `w`. -/
def ComA (P : Params) (w : Nat) (σ : State isa) : Prop :=
  GWA P σ.g ∧ (σ.r.wr P.top).q = 1 / 2 ∧ 1 ≤ σ.r.acq P.top w ∧ σ.snap.mem.initVal P.top = 0 ∧ FwdOKX P σ

/-- The common facts after a successful pop (`ComA` without `FwdOKX`: the
pop's `cas` leaves an exclusive forwarding item that is not below `vRel`,
and no acquire load of `top` follows). -/
def ComDA (P : Params) (w : Nat) (σ : State isa) : Prop :=
  GWA P σ.g ∧ (σ.r.wr P.top).q = 1 / 2 ∧ 1 ≤ σ.r.acq P.top w ∧ σ.snap.mem.initVal P.top = 0

theorem ComA.toD {P : Params} {w : Nat} {σ : State isa} (h : ComA P w σ) : ComDA P w σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- `top`'s write set is initial. -/
def NoWA (P : Params) (r : Res) : Prop := ∀ p, (r.wr P.top).X p → p.2 = 0

/-- `top`'s write set is the initial message and the push `Pw`. -/
def WS1 (P : Params) (r : Res) (Pw : Time) : Prop := ∀ p, (r.wr P.top).X p → p.2 = 0 ∨ p.2 = Pw

/-- **`worker`**: no push yet, the link and the data word whole. -/
def Pu0A (P : Params) (w : Nat) (σ : State isa) : Prop :=
  ComA P w σ ∧ NoWA P σ.r ∧ (σ.r.wr (P.nd w)).q = 1 ∧
    (∀ p, (σ.r.wr (P.nd w)).X p → p.2 ≤ σ.vs.getCoh (P.nd w)) ∧ (σ.r.wr (P.dd w)).q = 1 ∧
    (∀ p, (σ.r.wr (P.dd w)).X p → p.2 ≤ σ.vs.getCoh (P.dd w))

/-- **`push`**. -/
def PuA (P : Params) (w : Nat) (σ : State isa) : Prop :=
  ComA P w σ ∧ NoWA P σ.r ∧ (σ.r.wr (P.nd w)).q = 1 ∧
    (∀ p, (σ.r.wr (P.nd w)).X p → p.2 ≤ σ.vs.getCoh (P.nd w)) ∧ DataOK P w σ

/-- **After the link store** of `y`. -/
def Pu2A (P : Params) (w : Nat) (y : Val) (σ : State isa) : Prop :=
  ComA P w σ ∧ NoWA P σ.r ∧ (σ.r.wr (P.nd w)).q = 1 ∧
    (∃ t, (σ.r.wr (P.nd w)).X (y, t) ∧ (∀ p, (σ.r.wr (P.nd w)).X p → p.2 ≤ t) ∧ t ≤ σ.vs.vwOld ∧
      t ≤ σ.vs.getCoh (P.nd w)) ∧ DataOK P w σ

/-- **`pop`**. -/
def PoA (P : Params) (w : Nat) (σ : State isa) : Prop :=
  ComA P w σ ∧ ∃ Pw y, KeptA P w σ.snap.mem σ.r Pw y ∧ Pw ≤ σ.vs.getCoh P.top ∧ WS1 P σ.r Pw

/-- **After `ldar x2, [x0]`** of `y0`. -/
def PlA (P : Params) (w : Nat) (y0 : Val) (σ : State isa) : Prop :=
  ComA P w σ ∧ ∃ Pw y tr0, KeptA P w σ.snap.mem σ.r Pw y ∧ Pw ≤ σ.vs.getCoh P.top ∧ WS1 P σ.r Pw ∧
    Pw ≤ tr0 ∧ σ.snap.mem.read? P.top tr0 = some y0 ∧ tr0 ≤ σ.vs.vrNew

/-- **After `ldr x4, [x2, #8]`** of `u`. -/
def PrA (P : Params) (w : Nat) (y0 u : Val) (σ : State isa) : Prop :=
  ComA P w σ ∧ ∃ Pw y tr0 tl, KeptA P w σ.snap.mem σ.r Pw y ∧ Pw ≤ σ.vs.getCoh P.top ∧ WS1 P σ.r Pw ∧
    Pw ≤ tr0 ∧ σ.snap.mem.read? P.top tr0 = some y0 ∧ tr0 ≤ σ.vs.vrNew ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y0 + 8, 8⟩ tl = some u ∧
    ∀ p wm, tl < p → p ≤ tr0 → σ.snap.mem.get? p = some wm → wm.loc ≠ ⟨BitVec.setWidth 64 y0 + 8, 8⟩

/-- **After a successful pop `cas`**: a popped side with `v = x`, its `ldar`
read at or below `vrNew`. -/
def DnBA (P : Params) (w : Nat) (x : BitVec 64) (σ : State isa) : Prop :=
  ComDA P w σ ∧ ∃ X : Side, X.popped ∧ X.v = x ∧ SideA P w σ.snap.mem σ.r X ∧ X.tr0 ≤ σ.vs.vrNew

/-- **`done`** with `X10 = x10`, `X11 = x11`. -/
def DnDA (P : Params) (w : Nat) (x10 x11 : BitVec 64) (σ : State isa) : Prop :=
  ComDA P w σ ∧ DoneRA P w σ.snap.mem σ.r x10 x11

/-! ## Fences -/

section Fence

variable {P : Params} {w : Nat} {σ σ' : State isa}

theorem ComA.fence (h : ComA P w σ) (hf : FenceLe σ σ') : ComA P w σ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨hf.g ▸ h1, hf.r ▸ h2, hf.r ▸ h3, hf.snap ▸ h4, fun f hfw => ?_⟩
  rw [hf.getFwd] at hfw
  exact (h5 f hfw).imp (fun h => Nat.le_trans h hf.vrNew) (fun h => hf.vRel ▸ h)

theorem ComDA.fence (h : ComDA P w σ) (hf : FenceLe σ σ') : ComDA P w σ' :=
  ⟨hf.g ▸ h.1, hf.r ▸ h.2.1, hf.r ▸ h.2.2.1, hf.snap ▸ h.2.2.2⟩

theorem Pu0A.fence (h : Pu0A P w σ) (hf : FenceLe σ σ') : Pu0A P w σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.fence hf, hf.r ▸ h2, hf.r ▸ h3, ?_, hf.r ▸ h5, ?_⟩ <;> rw [hf.r, hf.getCoh] <;> assumption

theorem PuA.fence (h : PuA P w σ) (hf : FenceLe σ σ') : PuA P w σ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1.fence hf, hf.r ▸ h2, hf.r ▸ h3, ?_, h5.fence hf⟩
  rw [hf.r, hf.getCoh]; exact h4

theorem Pu2A.fence {y : Val} (h : Pu2A P w y σ) (hf : FenceLe σ σ') : Pu2A P w y σ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1.fence hf, hf.r ▸ h2, hf.r ▸ h3, ?_, h5.fence hf⟩
  rw [hf.r, hf.getCoh, hf.vwOld]; exact h4

theorem PoA.fence (h : PoA P w σ) (hf : FenceLe σ σ') : PoA P w σ' := by
  obtain ⟨h1, Pw, y, h2, h3, h4⟩ := h
  exact ⟨h1.fence hf, Pw, y, by rw [hf.snap, hf.r]; exact h2, by rw [hf.getCoh]; exact h3, by rw [hf.r]; exact h4⟩

theorem PlA.fence {y0 : Val} (h : PlA P w y0 σ) (hf : FenceLe σ σ') : PlA P w y0 σ' := by
  obtain ⟨h1, Pw, y, tr0, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1.fence hf, Pw, y, tr0, by rw [hf.snap, hf.r]; exact h2, by rw [hf.getCoh]; exact h3,
    by rw [hf.r]; exact h4, h5, hf.snap ▸ h6, Nat.le_trans h7 hf.vrNew⟩

theorem PrA.fence {y0 u : Val} (h : PrA P w y0 u σ) (hf : FenceLe σ σ') : PrA P w y0 u σ' := by
  obtain ⟨h1, Pw, y, tr0, tl, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1.fence hf, Pw, y, tr0, tl, by rw [hf.snap, hf.r]; exact h2, by rw [hf.getCoh]; exact h3,
    by rw [hf.r]; exact h4, h5, hf.snap ▸ h6, Nat.le_trans h7 hf.vrNew, hf.snap ▸ h8, hf.snap ▸ h9⟩

theorem DnBA.fence {x : BitVec 64} (h : DnBA P w x σ) (hf : FenceLe σ σ') : DnBA P w x σ' := by
  obtain ⟨h1, X, h2, h3, h4, h5⟩ := h
  exact ⟨h1.fence hf, X, h2, h3, by rw [hf.snap, hf.r]; exact h4, Nat.le_trans h5 hf.vrNew⟩

theorem DnDA.fence {x y : BitVec 64} (h : DnDA P w x y σ) (hf : FenceLe σ σ') : DnDA P w x y σ' := by
  unfold DnDA; rw [hf.snap, hf.r]; exact ⟨h.1.fence hf, h.2⟩

end Fence

/-! ## Steps that keep the resource -/

section Keep

variable {P : Params} {w : Nat} {σ σ' : State isa}

theorem ComA.load {k : LoadKind} {l : Loc} {v : Val} (h : ComA P w σ)
    (hf : LoadFacts Arch.armv8 w σ σ' k l v) : ComA P w σ' := by
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, by rw [initVal_eq hanc.snap.init]; exact h4, fun f hfw => ?_⟩
  rw [hlv.getFwd] at hfw
  exact (h5 f hfw).imp (fun h => Nat.le_trans h hlv.mono.vrNew) (fun h => Nat.le_trans h hlv.mono.vRel)

theorem ComA.rmwFail {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}
    (h : ComA P w σ) (hs : (EnvGC isa Arch.armv8 w planA).step (.rmw k addr n op) σ old σ')
    (hop : op old = none) : ComA P w σ' := by
  obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs
  rcases hbr with ⟨-, hsnap, hr⟩ | ⟨new, -, hon, -⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, by rw [hsnap, initVal_eq hanc.snap.init]; exact h4,
      fun f hfw => ?_⟩
    rw [envGC_rmw_fail_getFwd hs hop] at hfw
    exact (h5 f hfw).imp (fun h => Nat.le_trans h hvle.vrNew) (fun h => Nat.le_trans h hvle.vRel)
  · rw [hop] at hon; cases hon

/-- `ComA` after a store to a location other than `top`. -/
theorem ComA.store {k : StoreKind} {l : Loc} {v : Val} (h : ComA P w σ) (hne : l ≠ P.top)
    (hf : StoreFacts Arch.armv8 w planA σ σ' k l v) : ComA P w σ' := by
  obtain ⟨c, tw, hanc, hws, -, hwv, -, ⟨_, -, hr⟩, -, -⟩ := hf
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [planA_after] at hr
  refine ⟨h1.mono hanc.ghost, by rw [hr, Res.addW_wr_ne _ _ (Ne.symm hne)]; exact h2, by rw [hr, Res.addW_acq]; exact h3,
    by rw [initVal_eq (Treiber.WriteSnap.init hws), initVal_eq hanc.snap.init]; exact h4, fun f hfw => ?_⟩
  rw [hwv.fwdOther _ (Ne.symm hne)] at hfw
  exact (h5 f hfw).imp (fun h => Nat.le_trans h hwv.mono.vrNew) (fun h => Nat.le_trans h hwv.mono.vRel)

/-- The resource after a successful non-claiming RMW on `top`. -/
theorem rmw_res_top {k : RmwKind} (hcl : ∀ vs l tr, ¬ ClaimOk Arch.armv8 k vs l tr) {new : Val} {tw : Time}
    {Pc : Prop} {tr : Time}
    (hr : σ'.r = (planA.after P.top new tw Pc σ.r).op
      (Res.prod ((claimSlotsC Arch.armv8 k σ.vs σ'.g P.top tr).map (·.res)))) :
    σ'.r = σ.r.addW P.top (new, tw) := by
  rw [hr, claimSlotsC_of_not (hcl _ _ _), planA_after]
  simp [Res.prod, Res.op_unit]

end Keep

/-! ## The data word and the push -/

section Push

variable {P : Params} {w : Nat}

/-- **VC `str w9, [x1]`** (the data word, a value `v` with `D w v`):
permitted (pure), and `PuA` after it. -/
theorem vc_data_strA (σ : State isa) (h : Pu0A P w σ) (v : Val) (hD : P.D w v) :
    (EWA w).ok (.store .plain false (P.dd w).addr (P.dd w).bytes v) σ ∧
      ∀ b (σ' : State isa), (EWA w).step (.store .plain false (P.dd w).addr (P.dd w).bytes v) σ b σ' →
        PuA P w σ' := by
  obtain ⟨hcom, hnw, hq, hX, hqd, hXd⟩ := h
  have e : ({ addr := (P.dd w).addr, bytes := (P.dd w).bytes } : Loc) = P.dd w := rfl
  have hne : P.dd w ≠ P.top := Ne.symm (top_dd P w)
  refine ⟨⟨rfl, by rw [e, hqd]; decide, fun _ => hcom.1.pure _ _, fun hr => by simp [planA, Plan.find?] at hr⟩, ?_⟩
  intro b σ' hs
  have hsf := step_storeFacts (pl := planA) hs
  have hcom' := hcom.store (by rw [e]; exact hne) hsf
  obtain ⟨c, tw, hanc, hws, hwb, hwv, -, ⟨_, -, hr⟩, -, -⟩ := hsf
  rw [e, planA_after] at hr
  have hwr : ∀ x, x ≠ P.dd w → σ'.r.wr x = σ.r.wr x := fun x hx => by rw [hr, Res.addW_wr_ne _ _ hx]
  refine ⟨hcom', by unfold NoWA; rw [hwr _ (Ne.symm hne)]; exact hnw, by rw [hwr _ (nd_dd P w w)]; exact hq,
    fun p hp => ?_, ⟨by rw [hr, Res.addW_q]; exact hqd, v, tw, ?_, ?_, hwv.vwOld (by decide), hD⟩⟩
  · rw [hwr _ (nd_dd P w w)] at hp
    exact Nat.le_trans (hX p hp) (hwv.mono.coh _)
  · rw [hr, Res.addW_X_self]; exact .inr ⟨by rw [hqd]; decide, rfl⟩
  · intro p hp
    rw [hr, Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hXd p hp) hwb.coh)
    · exact Nat.le_refl _

/-- **VC of a push load** (`ldr x2, [x0]`, any kind): `PuA` is kept. -/
theorem vc_push_loadA (σ : State isa) (h : PuA P w σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64} {n : Nat} :
    ∀ v (σ' : State isa), (EWA w).step (.load k xcl a n) σ v σ' → PuA P w σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planA) hs
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := id hf
  obtain ⟨h1, h2, h3, h4, ⟨h5, d, td, h6, h7, h8, h9⟩⟩ := h
  refine ⟨h1.load hf, hr ▸ h2, hr ▸ h3, fun p hp => ?_, ⟨hr ▸ h5, d, td, hr ▸ h6, hr ▸ h7,
    Nat.le_trans h8 hlv.mono.vwOld, h9⟩⟩
  rw [hr] at hp
  exact Nat.le_trans (h4 p hp) (hlv.mono.coh _)

/-- **VC `str x2, [x1, #8]`** (the link, any value `v`): permitted, and
`(v, tw)` is the link's maximal write. -/
theorem vc_push_strA (hL : TLocs P) (hw : w < 2) (σ : State isa) (h : PuA P w σ) (v : Val) :
    (EWA w).ok (.store .plain false (P.nd w).addr (P.nd w).bytes v) σ ∧
      ∀ b (σ' : State isa), (EWA w).step (.store .plain false (P.nd w).addr (P.nd w).bytes v) σ b σ' →
        Pu2A P w v σ' := by
  obtain ⟨hcom, hnw, hq, hX, ⟨hqd, d, td, hXd, hmd, htd, hD⟩⟩ := h
  have e : ({ addr := (P.nd w).addr, bytes := (P.nd w).bytes } : Loc) = P.nd w := rfl
  have hne : P.nd w ≠ P.top := Ne.symm (hL.top_nd' hw)
  refine ⟨⟨rfl, by rw [e, hq]; decide, fun _ => hcom.1.pure _ _, fun hr => by simp [planA, Plan.find?] at hr⟩, ?_⟩
  intro b σ' hs
  have hsf := step_storeFacts (pl := planA) hs
  have hcom' := hcom.store (by rw [e]; exact hne) hsf
  obtain ⟨c, tw, hanc, hws, hwb, hwv, -, ⟨_, -, hr⟩, -, -⟩ := hsf
  rw [e, planA_after] at hr
  have hwr : ∀ x, x ≠ P.nd w → σ'.r.wr x = σ.r.wr x := fun x hx => by rw [hr, Res.addW_wr_ne _ _ hx]
  refine ⟨hcom', by unfold NoWA; rw [hwr _ (Ne.symm hne)]; exact hnw, by rw [hr, Res.addW_q]; exact hq,
    ⟨tw, ?_, ?_, hwv.vwOld (by decide), hwv.coh⟩,
    ⟨by rw [hwr _ (Ne.symm (nd_dd P w w))]; exact hqd, d, td, by rw [hwr _ (Ne.symm (nd_dd P w w))]; exact hXd,
      by rw [hwr _ (Ne.symm (nd_dd P w w))]; exact hmd, Nat.le_trans htd hwv.mono.vwOld, hD⟩⟩
  · rw [hr, Res.addW_X_self]; exact .inr ⟨by rw [hq]; decide, rfl⟩
  · intro p hp
    rw [hr, Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hX p hp) hwb.coh)
    · exact Nat.le_refl _

/-- **VC of the push RMW** `casl x3, x1, [x0]` (any kind `k` that does not
claim and stores as a release; `x3 = x2`, the link's maximal write `y` with
`x2` its 64 bits, `x1` the node): permitted (pure: `top` carries nothing),
and every outcome fails (`Pu2A` kept) or succeeds (`PoA`: the push message
`tw`, the read `tr` with only own messages of `top` in between, the node kept
with its writes below `tw`). -/
theorem vc_push_casA {k : RmwKind} (hcl : ∀ vs l tr, ¬ ClaimOk Arch.armv8 k vs l tr)
    (hrel : Arch.armv8.storeKind (Arch.armv8.rmwKind k).storeKind = .rel) (hL : TLocs P) (hw : w < 2)
    (σ : State isa) {y : Val} (h : Pu2A P w y σ) (x2 : BitVec 64) (hy : BitVec.setWidth 64 y = x2) :
    (EWA w).ok (.rmw k P.top.addr P.top.bytes (casOp64 x2 (P.n w))) σ ∧
      ∀ old (σ' : State isa), (EWA w).step (.rmw k P.top.addr P.top.bytes (casOp64 x2 (P.n w))) σ old σ' →
        (BitVec.setWidth 64 old ≠ x2 ∧ Pu2A P w y σ') ∨ (BitVec.setWidth 64 old = x2 ∧ PoA P w σ') := by
  obtain ⟨hcom, hnw, hq, ⟨t, hXt, hmt, htv, htc⟩, ⟨hqd, d, td, hXd, hmd, htd, hD⟩⟩ := h
  have e : ({ addr := P.top.addr, bytes := P.top.bytes } : Loc) = P.top := rfl
  refine ⟨⟨by rw [e, hcom.2.1]; exact half_posA, fun c g tr old new hanc hrd hon =>
    ⟨fun _ => hcom.1.pure _ _, fun hr => by simp [planA, Plan.find?] at hr⟩⟩, ?_⟩
  intro old σ' hs
  have hs' := envGCAdj_step_iff.mp hs
  rcases Classical.em (casOp64 x2 (P.n w) old = none) with hon | hon
  · refine .inl ⟨casOp64_none hon, hcom.rmwFail hs' hon, ?_⟩
    obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
    rcases hbr with ⟨-, -, hr⟩ | ⟨new, -, hon', -⟩
    · refine ⟨by unfold NoWA; rw [hr]; exact hnw, hr ▸ hq, ⟨t, hr ▸ hXt, hr ▸ hmt, Nat.le_trans htv hvle.vwOld,
        Nat.le_trans htc (hvle.coh _)⟩, ⟨hr ▸ hqd, d, td, hr ▸ hXd, hr ▸ hmd, Nat.le_trans htd hvle.vwOld, hD⟩⟩
    · rw [hon] at hon'; cases hon'
  obtain ⟨new, hon⟩ := Option.ne_none_iff_exists'.mp hon
  obtain ⟨hx, rfl⟩ := casOp64_some hon
  refine .inr ⟨hx, ?_⟩
  obtain ⟨c, tr, hanc, hrd, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon', -⟩ | ⟨new', tw, hon', htrw, hat, hws, hwb, htwc, -, -, ⟨Pc, -, hr⟩, -⟩
  · rw [hon] at hon'; cases hon'
  rw [hon] at hon'; cases hon'
  rw [e] at hr hws htwc hat hrd hwb
  have hr' := rmw_res_top hcl hr
  have hwr : ∀ x, x ≠ P.top → σ'.r.wr x = σ.r.wr x := fun x hx => by rw [hr', Res.addW_wr_ne _ _ hx]
  have hV : max (max σ.vs.vrOld σ.vs.vrOldNR) σ.vs.vwOld < tw := hwb.rel hrel
  have hvw : σ.vs.vwOld < tw := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hV
  have hpre : c.mem.Prefix σ'.snap.mem := Treiber2.WriteSnap.prefix hws
  have hnd := hL.top_nd' hw
  have hdd := top_dd P w
  refine ⟨⟨hcom.1.mono hanc.ghost, by rw [hr', Res.addW_q]; exact hcom.2.1, by rw [hr', Res.addW_acq]; exact hcom.2.2.1,
    by rw [initVal_eq (Treiber.WriteSnap.init hws), initVal_eq hanc.snap.init]; exact hcom.2.2.2.1,
    fun f hf => .inr (rmw_success_fwd_rel hs' hrel hon f hf)⟩, tw, x2,
    ⟨Treiber.WriteSnap.get?_new hws, by rw [hwr _ (Ne.symm hnd)]; exact hq,
      ⟨y, t, by rw [hwr _ (Ne.symm hnd)]; exact hXt, by rw [hwr _ (Ne.symm hnd)]; exact hmt,
        Nat.lt_of_le_of_lt htv hvw, hy⟩,
      ⟨tr, old, htrw, read?_mono hpre hrd.val, hx, fun p wm a b hg hl => ?_⟩,
      by rw [hwr _ (Ne.symm hdd)]; exact hqd,
      ⟨d, td, by rw [hwr _ (Ne.symm hdd)]; exact hXd, by rw [hwr _ (Ne.symm hdd)]; exact hmd,
        Nat.lt_of_le_of_lt htd hvw, hD⟩⟩, htwc, fun p hp => ?_⟩
  · have hle_tw : tw ≤ c.mem.last + 1 := Treiber2.WriteSnap.tw_le hws
    have hp : p ≤ c.mem.last := by omega_t
    exact atomic_between hat hrd.val a b (Memory.get?_of_prefix_le hpre.2 hp hg) hl
  · rw [hr', Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact .inl (hnw p hp)
    · exact .inr rfl

end Push

/-! ## The pop -/

section Pop

variable {P : Params} {w : Nat}

/-- **VC `ldar x2, [x0]`** of the pop: `PlA` of the value read (at
`tr0 ≥ Pw`, `tr0 ≤ vrNew` by `load_acq_vrNew`). -/
theorem vc_pop_ldarA (σ : State isa) (h : PoA P w σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (EWA w).step (.load .acq xcl P.top.addr P.top.bytes) σ v σ' → PlA P w v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planA) hs
  obtain ⟨hcom, Pw, y, hk, hc, hws⟩ := h
  obtain ⟨tr0, hrd, hwin, hle⟩ := load_acq_vrNew (envGCAdj_step_iff.mp hs) hcom.2.2.2.2
  obtain ⟨hanc, hr, -, _tr, -, hlv, -⟩ := id hf
  have hpre := Treiber2.AnchorOk.prefix hanc
  refine ⟨hcom.load hf, Pw, y, tr0, hr ▸ hk.mono hpre, Nat.le_trans hc (hlv.mono.coh _), hr ▸ hws, ?_, hrd, hle⟩
  refine Nat.le_of_not_lt fun hlt => ?_
  exact hwin Pw _ hlt hc (get?_of_anchor hanc hk.1) rfl

/-- **`cbz x2, done` taken**: `DnDA` (the stack read empty). -/
theorem vc_pop_cbzA (σ : State isa) {y0 : Val} (h : PlA P w y0 σ) (hz : BitVec.setWidth 64 y0 = 0)
    (x y : BitVec 64) : DnDA P w x y σ := by
  obtain ⟨hcom, Pw, y', tr0, hk, -, hws, h1, h2, -⟩ := h
  refine ⟨hcom.toD, hcom.2.2.1, hcom.2.2.2.1, ⟨Pw, P.n w, y', False, 0, 0, 0, 0, 0⟩,
    ⟨rfl, hcom.2.1, fun p hp => ?_, hk, fun h => h.elim, fun _ => ⟨tr0, y0, h1, h2, hz⟩⟩, fun h => h.elim⟩
  rcases hws p hp with h | h
  · exact .inl h
  · exact .inr (.inl h)

/-- **VC `ldr x4, [x2, #8]`** of the pop (`x2` the 64 bits of `y0`): `PrA`
of the value read, its window covering `tr0`. -/
theorem vc_pop_ldrA (σ : State isa) {y0 : Val} (h : PlA P w y0 σ) {xcl : Bool} :
    ∀ u (σ' : State isa), (EWA w).step (.load .plain xcl (BitVec.setWidth 64 y0 + 8) 8) σ u σ' →
      PrA P w y0 u σ' := by
  intro u σ' hs
  have hf := step_loadFacts (pl := planA) hs
  obtain ⟨hcom, Pw, y, tr0, hk, hc, hws, h1, h2, h3⟩ := h
  refine ⟨hcom.load hf, Pw, y, tr0, ?_⟩
  obtain ⟨hanc, hr, -, tl, hrd, hlv, -⟩ := hf
  have hpre := Treiber2.AnchorOk.prefix hanc
  refine ⟨tl, hr ▸ hk.mono hpre, Nat.le_trans hc (hlv.mono.coh _), hr ▸ hws, h1, hanc.read? h2,
    Nat.le_trans h3 hlv.mono.vrNew, hrd.val, fun p wm a b hg hl => ?_⟩
  have := (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, a, Nat.le_trans b (Nat.le_trans h3
    (le_readBound_vrNew Arch.armv8 σ.vs .plain ⟨BitVec.setWidth 64 y0 + 8, 8⟩)), hg, hl⟩
  rw [hrd.window] at this; cases this

/-- **VC of the pop RMW** `cas x3, x4, [x0]` (any kind `k` that does not
claim; `x3 = x2` the 64 bits of `y0`, `x2 ≠ 0`, `x4` the 64 bits of `u`):
permitted (pure), and every outcome fails (`PoA`) or succeeds (`DnBA x2`). -/
theorem vc_pop_casA {k : RmwKind} (hcl : ∀ vs l tr, ¬ ClaimOk Arch.armv8 k vs l tr) (hL : TLocs P) (hw : w < 2)
    (σ : State isa) {y0 u : Val} (h : PrA P w y0 u σ) (hx2 : BitVec.setWidth 64 y0 ≠ 0) :
    (EWA w).ok (.rmw k P.top.addr P.top.bytes (casOp64 (BitVec.setWidth 64 y0) (BitVec.setWidth 64 u))) σ ∧
      ∀ old (σ' : State isa), (EWA w).step (.rmw k P.top.addr P.top.bytes
          (casOp64 (BitVec.setWidth 64 y0) (BitVec.setWidth 64 u))) σ old σ' →
        (BitVec.setWidth 64 old ≠ BitVec.setWidth 64 y0 ∧ PoA P w σ') ∨
          (BitVec.setWidth 64 old = BitVec.setWidth 64 y0 ∧ DnBA P w (BitVec.setWidth 64 y0) σ') := by
  obtain ⟨hcom, Pw, y, tr0, tl, hk, hc, hws, h5_le, h5, h6, h7, h8⟩ := h
  have e : ({ addr := P.top.addr, bytes := P.top.bytes } : Loc) = P.top := rfl
  refine ⟨⟨by rw [e, hcom.2.1]; exact half_posA, fun c g tr old new hanc hrd hon =>
    ⟨fun _ => hcom.1.pure _ _, fun hr => by simp [planA, Plan.find?] at hr⟩⟩, ?_⟩
  intro old σ' hs
  have hs' := envGCAdj_step_iff.mp hs
  obtain ⟨c, tr, hanc, hrd, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, hsnap, hr⟩ | ⟨new, tw, hon, htrw, hat, hws', -, -, -, -, ⟨Pc, -, hr⟩, -⟩
  · -- failure: back to `pop`
    refine .inl ⟨casOp64_none hon, hcom.rmwFail hs' hon, Pw, y, ?_, Nat.le_trans hc (hvle.coh _), hr ▸ hws⟩
    rw [hsnap, hr]; exact hk.mono (Treiber2.AnchorOk.prefix hanc)
  -- success
  obtain ⟨hx, rfl⟩ := casOp64_some hon
  refine .inr ⟨hx, ?_⟩
  rw [e] at hrd hat hws' hr
  have hr' := rmw_res_top hcl hr
  have hpre : σ.snap.mem.Prefix σ'.snap.mem := (Treiber2.AnchorOk.prefix hanc).trans (Treiber2.WriteSnap.prefix hws')
  have hcom' : ComDA P w σ' := ⟨hcom.1.mono hanc.ghost, by rw [hr', Res.addW_q]; exact hcom.2.1,
    by rw [hr', Res.addW_acq]; exact hcom.2.2.1,
    by rw [initVal_eq (Treiber.WriteSnap.init hws'), initVal_eq hanc.snap.init]; exact hcom.2.2.2.1⟩
  -- the `cas` read is at or after the `ldar`'s
  have htr0 : tr0 ≤ tr := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have h0 : tr0 ≠ 0 := by omega_t
    obtain ⟨wm, hg, hl, -⟩ := TreiberCommon.get?_of_read? h0 (hanc.read? h5)
    have hB : tr0 ≤ readBound Arch.armv8 (rmwReadViews Arch.armv8 σ.vs) (Arch.armv8.rmwKind k).loadKind P.top :=
      Nat.le_trans h6 (le_readBound_vrNew _ _ _ _)
    have := (Memory.writeIn_iff _ _ _ _).mpr ⟨tr0, wm, hlt, hB, hg, hl⟩
    rw [hrd.window] at this; cases this
  have hle_tw : tw ≤ c.mem.last + 1 := Treiber2.WriteSnap.tw_le hws'
  have hnd := hL.top_nd' hw
  have hdd := top_dd P w
  refine ⟨hcom', ⟨Pw, P.n w, y, True, tw, tr0, tr, BitVec.setWidth 64 y0, BitVec.setWidth 64 u⟩, trivial, rfl,
    ⟨rfl, hcom'.2.1, fun p hp => ?_, (hk.mono hpre).congr (by rw [hr', Res.addW_wr_ne _ _ (Ne.symm hnd)])
      (by rw [hr', Res.addW_wr_ne _ _ (Ne.symm hdd)]), fun _ => ⟨h5_le, htr0, htrw, ⟨y0, read?_mono hpre h5, rfl⟩,
      ⟨old, read?_mono (Treiber2.WriteSnap.prefix hws') hrd.val, hx⟩, hx2, ?_, Treiber.WriteSnap.get?_new hws', tl, u,
      read?_mono hpre h7, rfl, ?_⟩, fun h => absurd trivial h⟩, Nat.le_trans h6 hvle.vrNew⟩
  · rw [hr', Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · rcases hws p hp with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · exact .inr (.inr ⟨trivial, rfl⟩)
  · intro p wm a b hg hl
    have hp : p ≤ c.mem.last := by omega_t
    exact atomic_between hat hrd.val a b (Memory.get?_of_prefix_le (Treiber2.WriteSnap.prefix hws').2 hp hg) hl
  · intro p wm a b hg
    have hp : p ≤ σ.snap.mem.last := Nat.le_trans b (TreiberCommon.read?_le_last h5)
    exact h8 p wm a b (Memory.get?_of_prefix_le hpre.2 hp hg)

/-- **VC `ldr w11, [x2]`** after a successful pop (`x2 = x` the node): its
window covers the pop's `ldar` read (`DnDA`). -/
theorem vc_ldr_dataA (σ : State isa) {x : BitVec 64} (h : DnBA P w x σ) {xcl : Bool} :
    ∀ u (σ' : State isa), (EWA w).step (.load .plain xcl x 4) σ u σ' → DnDA P w x (x32A u) σ' := by
  intro u σ' hs
  have hf := step_loadFacts (pl := planA) hs
  obtain ⟨hcom, X, hp, hv, hX, hle⟩ := h
  obtain ⟨hanc, hr, -, tl, hrd, hlv, -⟩ := hf
  refine ⟨⟨hcom.1.mono hanc.ghost, hr ▸ hcom.2.1, hr ▸ hcom.2.2.1,
    by rw [initVal_eq hanc.snap.init]; exact hcom.2.2.2⟩, ?_⟩
  have hpre := Treiber2.AnchorOk.prefix hanc
  refine ⟨by rw [hr]; exact hcom.2.2.1, by rw [initVal_eq hanc.snap.init]; exact hcom.2.2.2, X,
    hr ▸ hX.mono hpre, fun _ => ⟨hv, tl, u, hrd.val, rfl, fun p wm a b hg hl => ?_⟩⟩
  have := (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, a, Nat.le_trans b (Nat.le_trans hle
    (le_readBound_vrNew Arch.armv8 σ.vs .plain ⟨x, 4⟩)), hg, hl⟩
  rw [hrd.window] at this; cases this

end Pop

end Kraken.Promising.SLR.EnvG.Treiber2Arm
