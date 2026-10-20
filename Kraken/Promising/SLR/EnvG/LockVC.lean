/-
**The swap-acquire spinlock on `EnvG`, the ISA-neutral table predicates and
counter VCs**: the part of `EnvG/X64SpinVC.lean` (the
x64 `xchg` lock) that `EnvG/SwplLockVC.lean` (the AArch64 `swpa`/`swpl`
lock) copied, because `X64SpinVC` imports the x64 syntax and cannot be
co-imported with AArch64's. Moved here verbatim (the state-typed predicates
generalised from `EStateX`/`State isa` to `State I`); both files keep their
names as aliases (`EnvG/Alias.lean`) or instances.

The specification is the SWP lock's (`SpinCommon`: `Sys`, `World`, `Fresh`;
`Spinlock`: `Pool`, `Good`, `Bad`, `lockPred`); the plan is `xlockPlan`
(`EnvG/X64SpinRelease.lean`).

- `LkLe` (the write set of the lock), `GoodC`, `Acq` (+ `mono`, `q`,
  `counter`), `fresh_join`, `LkLe.mono/join/addW_ne`, `threadRes_lkLe`;
- the table predicates `H1`, `H2 x5`, `H3 x5`, `QEnd` and their `fence`
  lemmas;
- the counter VCs from the Out/Facts interface, for any `Arch`:
  `vc_ld_cG` (from `LoadFacts`) and `vc_st_cG` (`StoreOk` and `StoreFacts`).

Phase-1 limits apply (single-access trees, read-side acquire only).

This file imports no ISA syntax.
-/
import Kraken.Promising.SLR.EnvG.X64SpinRelease
import Kraken.Promising.SLR.EnvG.VCGenCommon
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.Promising.SLR.SpinAcquire
import Kraken.Promising.SLR.SpinClaim

namespace Kraken.Promising.SLR.EnvG.LockVC

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

variable {I : ISA} {P : Sys} {tid : Nat}

/-! ## The table predicates -/

/-- **The write set of the lock**: without a surplus of the lock, every
non-zero write of `Lk` in `r`'s write set is at or below `vs`'s coherence
view of `Lk`. -/
def LkLe (P : Sys) (r : Res) (vs : Views) : Prop :=
  ¬ 1 / (P.N : Rat) < (r.wr P.Lk).q → ∀ p, (r.wr P.Lk).X p → p.1 ≠ 0 → p.2 ≤ vs.getCoh P.Lk

/-- The counter relation of an acquired `Good` part `R` for `S` (`CasVC.GoodC`). -/
def GoodC (P : Sys) (S : Nat → Bool) (k : Nat) (vs : Views) (R : Res) : Prop :=
  ∃ ts, (R.wr P.C).X (BitVec.ofNat 128 k, ts) ∧ (∀ p, (R.wr P.C).X p → p.2 ≤ ts) ∧
    k = ((List.range P.N).filter S).length ∧ ts ≤ vs.vrNew ∧ ts ≤ vs.vwNew

/-- **The resource after a successful lock swap**: a `Fresh` resource `r0`,
the claimed slots `R ⋅ R'` and the swap's write `(1, tw)` of the lock; `R`
holds the pool for `S`, and the counter relation (`GoodC`) or `Bad`. -/
def Acq (P : Sys) (tid : Nat) (S : Nat → Bool) (k : Nat) (vs : Views) (rr R : Res) : Prop :=
  ∃ r0 R' : Res, ∃ tw : Time, rr = (r0.op (R.op R')).addW P.Lk (1#128, tw) ∧ Fresh P tid r0 ∧
    Pool P.N P.C P.K P.F S R ∧ (GoodC P S k vs R ∨ Bad P.N P.Lk P.C P.K P.F R)

theorem Acq.mono {S : Nat → Bool} {k : Nat} {vs vs' : Views} {rr R : Res}
    (h : Acq P tid S k vs rr R) (h1 : vs.vrNew ≤ vs'.vrNew) (h2 : vs.vwNew ≤ vs'.vwNew) :
    Acq P tid S k vs' rr R := by
  obtain ⟨r0, R', tw, e, hf, hp, hgb⟩ := h
  exact ⟨r0, R', tw, e, hf, hp,
    hgb.imp (fun ⟨ts, hX, hm, hk, a, b⟩ => ⟨ts, hX, hm, hk, Nat.le_trans a h1, Nat.le_trans b h2⟩) id⟩

theorem Acq.q {r0 R R' : Res} {tw : Time} (y : Loc) :
    ((((r0.op (R.op R')).addW P.Lk (1#128, tw))).wr y).q = (r0.wr y).q + ((R.wr y).q + (R'.wr y).q) := by
  rw [Res.addW_q]; rfl

/-- **The counter in `Acq`**: at least a full share; with a valid resource
exactly one, and in the `Good` case the maximal write `(k, ts)`. -/
theorem Acq.counter {S : Nat → Bool} {k : Nat} {vs : Views} {rr R : Res}
    (hLC : P.Lk ≠ P.C) (h : Acq P tid S k vs rr R) :
    1 ≤ (rr.wr P.C).q ∧ (rr.valid → (rr.wr P.C).q = 1 ∧ (GoodC P S k vs R → ∃ ts,
      (rr.wr P.C).X (BitVec.ofNat 128 k, ts) ∧ (∀ p, (rr.wr P.C).X p → p.2 ≤ ts) ∧ ts ≤ vs.vrNew ∧
        ts ≤ vs.vwNew)) := by
  obtain ⟨r0, R', tw, rfl, -, hpool, -⟩ := h
  have hq := Acq.q (P := P) (r0 := r0) (R := R) (R' := R') (tw := tw) P.C
  have n1 := (r0.wr P.C).nonneg
  have n3 := (R'.wr P.C).nonneg
  rw [hpool.1] at hq
  refine ⟨by rw [hq]; grind, fun hv => ?_⟩
  have h1 := hv.1 P.C
  rw [hq] at h1
  have h0 : (r0.wr P.C).q = 0 := by grind
  have h0' : (R'.wr P.C).q = 0 := by grind
  have hwr : ((r0.op (R.op R')).addW P.Lk (1#128, tw)).wr P.C = (r0.wr P.C).op ((R.wr P.C).op (R'.wr P.C)) :=
    Res.addW_wr_ne _ _ (Ne.symm hLC)
  refine ⟨by rw [hq]; grind, fun hgood => ?_⟩
  rw [hwr]
  obtain ⟨ts, hX, hmax, -, h1, h2⟩ := hgood
  refine ⟨ts, .inr (.inl hX), fun p hp => ?_, h1, h2⟩
  rcases hp with hp | hp | hp
  · exact absurd hp ((r0.wr P.C).zero h0 p)
  · exact hmax p hp
  · exact absurd hp ((R'.wr P.C).zero h0' p)

/-- **Holding the lock** (after a successful acquiring swap). -/
def H1 (P : Sys) (tid : Nat) (σ : State I) : Prop :=
  World P σ.g ∧ LkLe P σ.r σ.vs ∧ ∃ S k R, Acq P tid S k σ.vs σ.r R

/-- **After the counter load** of `x5`: under the clean flag, the resource is
valid and the counter value is `|S|` (or the acquired part was `Bad`). -/
def H2 (P : Sys) (tid : Nat) (x5 : BitVec 32) (σ : State I) : Prop :=
  World P σ.g ∧ LkLe P σ.r σ.vs ∧ ∃ S k R, Acq P tid S k σ.vs σ.r R ∧
    (σ.cl → σ.r.valid ∧ (Bad P.N P.Lk P.C P.K P.F R ∨ x5 = BitVec.ofNat 32 k))

/-- **After the counter store** of `x5` at `tw ≤ vwOld`; under the clean flag
the store is above every earlier counter write. -/
def H3 (P : Sys) (tid : Nat) (x5 : BitVec 32) (σ : State I) : Prop :=
  World P σ.g ∧ LkLe P σ.r σ.vs ∧ ∃ S k R rr, ∃ tw : Time, Acq P tid S k σ.vs rr R ∧
    σ.r = rr.addW P.C (BitVec.setWidth 128 x5, tw) ∧ tw ≤ σ.vs.vwOld ∧
    (σ.cl → rr.valid ∧ (Bad P.N P.Lk P.C P.K P.F R ∨
      (x5 = BitVec.ofNat 32 (k + 1) ∧ ∀ p, (rr.wr P.C).X p → p.2 < tw)))

/-- **The end**: the world, and under the clean flag the worker's `Post`. -/
def QEnd (P : Sys) (σ : State I) : Prop := World P σ.g ∧ (σ.cl → Post P.N P.Lk P.K σ.r)

/-! ## Monotonicity of the lock facts -/

theorem fresh_join {r X : Res} {p : Val × Time} (h : Fresh P tid r) :
    Fresh P tid ((r.op X).addW P.Lk p) := by
  have hge : ∀ y, (r.wr y).q ≤ (((r.op X).addW P.Lk p).wr y).q :=
    fun y => by rw [Res.addW_q]; exact Perm.le_op_left _ _
  exact ⟨Rat.le_trans h.1 (hge _), Rat.le_trans h.2.1 (hge _), Rat.le_trans h.2.2 (hge _)⟩

theorem LkLe.mono {r : Res} {vs vs' : Views} (h : LkLe P r vs) (hc : vs.getCoh P.Lk ≤ vs'.getCoh P.Lk) :
    LkLe P r vs' := fun hs p hp hp0 => Nat.le_trans (h hs p hp hp0) hc

/-- **`LkLe` across a lock RMW**: a `Fresh` thread joins a part `X` and
writes `(v, tw)`, `tw` at or below the new coherence view. -/
theorem LkLe.join {r X : Res} {vs vs' : Views} {v : Val} {tw : Time} (hf : Fresh P tid r) (h : LkLe P r vs)
    (hc : vs.getCoh P.Lk ≤ vs'.getCoh P.Lk) (htw : tw ≤ vs'.getCoh P.Lk) :
    LkLe P ((r.op X).addW P.Lk (v, tw)) vs' := by
  intro hs p hp hp0
  rw [Res.addW_q] at hs
  change ¬ 1 / (P.N : Rat) < (r.wr P.Lk).q + (X.wr P.Lk).q at hs
  have hX0 : (X.wr P.Lk).q = 0 := by have := hf.2.2; have := (X.wr P.Lk).nonneg; grind
  have hs' : ¬ 1 / (P.N : Rat) < (r.wr P.Lk).q := by grind
  rcases (Res.addW_X_self _ _ _ _).mp hp with (hp | hp) | ⟨-, rfl⟩
  · exact Nat.le_trans (h hs' p hp hp0) hc
  · exact absurd hp ((X.wr P.Lk).zero hX0 p)
  · exact htw

/-- `LkLe` across a write of another location. -/
theorem LkLe.addW_ne {r : Res} {vs vs' : Views} {y : Loc} {p : Val × Time} (h : LkLe P r vs) (hy : y ≠ P.Lk)
    (hc : vs.getCoh P.Lk ≤ vs'.getCoh P.Lk) : LkLe P (r.addW y p) vs' := by
  unfold LkLe
  rw [Res.addW_wr_ne _ _ (Ne.symm hy)]
  exact (h.mono hc)

/-- The initial thread resource writes only the lock's initial message `0`,
so `LkLe` holds at any views. -/
theorem threadRes_lkLe {m : Memory} (h0 : m.initVal P.Lk = 0) (vs : Views) :
    LkLe P (threadRes m P.N P.Lk P.K P.F tid) vs := by
  rintro - p ⟨-, rfl⟩ hne
  exact absurd h0 hne

/-! ## The table predicates are monotone under fences -/

theorem H1.fence {σ σ' : State I} (h : H1 P tid σ) (hf : FenceLe σ σ') : H1 P tid σ' := by
  obtain ⟨hW, hz, S, k, R, hA⟩ := h
  exact ⟨by rw [hf.g]; exact hW, by unfold LkLe; rw [hf.r, hf.getCoh]; exact hz, S, k, R,
    by rw [hf.r]; exact hA.mono hf.vrNew hf.vwNew⟩

theorem H2.fence {x5 : BitVec 32} {σ σ' : State I} (h : H2 P tid x5 σ) (hf : FenceLe σ σ') : H2 P tid x5 σ' := by
  obtain ⟨hW, hz, S, k, R, hA, hc⟩ := h
  exact ⟨by rw [hf.g]; exact hW, by unfold LkLe; rw [hf.r, hf.getCoh]; exact hz, S, k, R,
    by rw [hf.r]; exact hA.mono hf.vrNew hf.vwNew, by rw [hf.cl, hf.r]; exact hc⟩

theorem H3.fence {x5 : BitVec 32} {σ σ' : State I} (h : H3 P tid x5 σ) (hf : FenceLe σ σ') : H3 P tid x5 σ' := by
  obtain ⟨hW, hz, S, k, R, rr, tw, hA, hr, hvw, hc⟩ := h
  exact ⟨by rw [hf.g]; exact hW, by unfold LkLe; rw [hf.r, hf.getCoh]; exact hz, S, k, R, rr, tw,
    hA.mono hf.vrNew hf.vwNew, by rw [hf.r]; exact hr, by rw [hf.vwOld]; exact hvw, by rw [hf.cl]; exact hc⟩

theorem QEnd.fence {σ σ' : State I} (h : QEnd P σ) (hf : FenceLe σ σ') : QEnd P σ' := by
  unfold QEnd; rw [hf.g, hf.r, hf.cl]; exact h

/-! ## The counter VCs -/

/-- **VC, the counter load** (from `LoadFacts`, any `Arch`): `H1` is kept,
and under the clean flag of the load's anchor the resource is valid and a
`Good` acquisition reads the counter's maximal write `|S|` (`read_max`). -/
theorem vc_ld_cG {A : Arch} {k : LoadKind} (hLC : P.Lk ≠ P.C) {σ σ' : State I} {v : Val} (h : H1 P tid σ)
    (hs : LoadFacts A tid σ σ' k P.C v) : H2 P tid (BitVec.setWidth 32 v) σ' := by
  obtain ⟨hanc, hr, hcl, tr, hrd, hlv, -⟩ := hs
  obtain ⟨hW, hz, S, k, R, hA⟩ := h
  refine ⟨hW.mono hanc.ghost, by rw [hr]; exact hz.mono (hlv.mono.coh _), S, k, R,
    by rw [hr]; exact hA.mono hlv.mono.vrNew hlv.mono.vwNew, fun hc => ?_⟩
  rw [hcl] at hc
  obtain ⟨-, rF, E'⟩ := hc
  have hv : σ.r.valid := Res.valid_op_left (Erase.valid_claim E' hanc.lt P.C 0)
  refine ⟨by rw [hr]; exact hv, ?_⟩
  have hA' := hA
  obtain ⟨-, -, -, -, -, -, hgb⟩ := hA'
  rcases hgb with hgood | hbad
  · refine .inr ?_
    obtain ⟨hq1, ts, hX, hmax, h1, -⟩ := (Acq.counter hLC hA).2 hv |>.imp id (fun f => f hgood)
    obtain ⟨t, ht⟩ : ∃ t, σ'.snap.threads[tid]? = some t :=
      ⟨σ'.snap.threads[tid]'hanc.lt, Array.getElem?_eq_getElem hanc.lt⟩
    have hp : t.prom.contains tr = false := by
      have := hrd.notOwn
      simp only [ownProm, ht, Option.map_some, Option.getD_some] at this
      exact this
    obtain ⟨-, rfl⟩ := read_max E' ht hq1 hX hmax hrd.val hp hrd.window
      (Nat.le_trans h1 (le_readBound_vrNew _ _ _ _))
    apply BitVec.eq_of_toNat_eq; simp
  · exact .inl hbad

/-- **VC, the counter store** (`StoreOk` and `StoreFacts`, any `Arch` whose
store kind `k` is not non-temporal; plain, pure value): permitted (at least a
full counter share, the counter's predicate pure), and every outcome adds
`(x5, tw)`; under the clean flag above every earlier counter write. -/
theorem vc_st_cG {A : Arch} {k : StoreKind} (hnt : A.storeKind k ≠ .nt) (hLC : P.Lk ≠ P.C) (x5 : BitVec 32)
    {σ : State I} (h : H2 P tid x5 σ) :
    StoreOk A tid (xlockPlan P tid) σ k false P.C (BitVec.setWidth 128 (x5 + 1)) ∧
      ∀ σ' : State I, StoreFacts A tid (xlockPlan P tid) σ σ' k P.C (BitVec.setWidth 128 (x5 + 1)) →
        H3 P tid (x5 + 1) σ' := by
  obtain ⟨hW, hz, S, k, R, hA, hcl⟩ := h
  have hq := (Acq.counter hLC hA).1
  have hne : P.C ≠ P.Lk := Ne.symm hLC
  refine ⟨⟨rfl, show 0 < (σ.r.wr P.C).q by grind, fun _ => hW.2.1 _,
    fun hr => by rw [xlockPlan_rel_ne hne] at hr; cases hr⟩, ?_⟩
  intro σ' hs
  obtain ⟨c, tw, hanc, -, hwb, hwv, -, hr, hcl', -⟩ := hs
  obtain ⟨_, -, hr⟩ := hr
  have hr' : σ'.r = σ.r.addW P.C (BitVec.setWidth 128 (x5 + 1), tw) := by
    rw [hr, Plan.after, xlockPlan_rel_ne hne]; rfl
  refine ⟨hW.mono hanc.ghost, by rw [hr']; exact hz.addW_ne hne (hwv.mono.coh _), S, k, R, σ.r, tw,
    hA.mono hwv.mono.vrNew hwv.mono.vwNew, hr', hwv.vwOld hnt, fun hc => ?_⟩
  rw [hcl'] at hc
  obtain ⟨hv, hb⟩ := hcl hc
  refine ⟨hv, ?_⟩
  rcases hb with hb | hx
  · exact .inl hb
  · have hA' := hA
    obtain ⟨-, -, -, -, -, -, hgb⟩ := hA'
    rcases hgb with hgood | hbad
    · refine .inr ⟨by rw [hx]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add], fun p hp => ?_⟩
      obtain ⟨-, ts, -, hmax, -, h2⟩ := (Acq.counter hLC hA).2 hv |>.imp id (fun f => f hgood)
      exact Nat.lt_of_le_of_lt (Nat.le_trans (hmax p hp) h2) hwb.vwNew
    · exact .inl hbad

/-! ## RMW facts (from `EnvG/TicketLockVC.lean`) -/

/-- **A successful or failed RMW leaves the other locations' forwarding
items alone.** -/
theorem _root_.Kraken.Promising.SLR.EnvG.rmwOut_getFwd_ne {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {old : Val} (h : RmwOut A tid pl σ σ' k l op old) {l' : Loc} (hne : l' ≠ l) :
    σ'.vs.getFwd l' = σ.vs.getFwd l' := by
  obtain ⟨c, x, -, hx, -, -, -, -, -, hbr⟩ := h
  have h5 := readSuccs_fwdb A _ hx
  have e : x.2.2.views.getFwd l' = (fenceOptCtx A (envCtx tid σ.vs c)).views.getFwd l' := by
    simp only [Views.getFwd, h5]
  rcases hbr with ⟨-, -, hvs, -⟩ | ⟨new, cx', tw, -, hcx, -, -, -, -, hvs, -⟩
  · rw [hvs, fenceOptCtx_getFwd, e, fenceOptCtx_getFwd]; rfl
  · rw [hvs, rmwAfter_getFwd]
    rcases (mem_writeSuccs A tid).mp hcx with ⟨-, -, -, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩
    · rw [afterWrite_getFwd, ite_eq_right hne, e, fenceOptCtx_getFwd]; rfl
    · rw [afterWrite_getFwd, ite_eq_right hne]; exact e.trans (fenceOptCtx_getFwd _ _)

/-! ## The lock release

The release proof of the x64 `xchg` lock (`X64Spin.vc_rel`, a plain store
under `Arch.tso`) was copied twice: the AArch64 `swpl` lock's
`SwplLock.vc_swpl` (a release-only swap) and the SWP lock's `SwpEnvG.vc_stlr`
(a store release). `vc_relG` is the shared part, for any ISA, architecture
and store kind with the effective kind of a `tso` plain store: the
permission (`storeOk_xlockRelease` through `storeOk_of_storeKind`), and
`QEnd` after any release whose outcome is `xlockPlan`'s split above the
coherence view of `Lk` (`xlockRelease_post`). The three VCs are its
instances. -/

/-- **A store's permission depends on the architecture and the store kind
only through the effective kind.** -/
theorem _root_.Kraken.Promising.SLR.EnvG.SwpEnvG.storeOk_of_storeKind {I : ISA} {A A' : Arch} {k k' : StoreKind} (hk : A.storeKind k = A'.storeKind k')
    {tid : Nat} {pl : Plan} {σ : State I} {xcl : Bool} {l : Loc} {v : Val}
    (h : StoreOk A tid pl σ k xcl l v) : StoreOk A' tid pl σ k' xcl l v := by
  obtain ⟨hx, hq, hp, hrel⟩ := h
  refine ⟨hx, hq, hp, fun hr => ?_⟩
  obtain ⟨he, hi, hg, hob⟩ := hrel hr
  refine ⟨?_, hi, hg, fun c g hanc hwb => hob c g hanc ⟨hwb.vwNew, hwb.vCAP, hwb.coh, fun h => hwb.rel (hk ▸ h)⟩⟩
  rcases he with h | h
  · exact .inl (hk ▸ h)
  · exact .inr h

/-- **The lock release, generic** (a write of `0` to `Lk`, `xlockPlan`'s
split): permitted from `H3` for any store kind whose effective kind is that
of a `tso` plain store, and `QEnd` after any outcome that keeps the ghost
growing and the clean flag, and gives `xlockPlan`'s split at a time `tw`
above the coherence view of `Lk` (without a surplus, `LkLe` bounds the own
non-zero writes of `Lk` by the coherence view). -/
theorem vc_relG {A : Arch} {sk : StoreKind} (hsk : Arch.tso.storeKind .plain = A.storeKind sk)
    (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32)
    {x5 : BitVec 32} {σ : State I} (h : H3 P tid x5 σ) :
    StoreOk A tid (xlockPlan P tid) σ sk false P.Lk 0 ∧
      ∀ {σ' : State I} {tw : Time} {Pc : Prop}, σ.g.Le σ'.g → σ'.cl = σ.cl → σ.vs.getCoh P.Lk < tw →
        (σ.cl → Pc) → σ'.r = (xlockPlan P tid).after P.Lk 0 tw Pc σ.r → QEnd P σ' := by
  obtain ⟨hW, hz, S, k, R, rr, tw3, hA, hr, hvw, hcl⟩ := h
  obtain ⟨r0, R', twc, hrr, hf0, hpool, hgb⟩ := hA
  have hN := one_div_pos hN0
  have hq : ∀ y, (σ.r.wr y).q = (r0.wr y).q + ((R.wr y).q + (R'.wr y).q) := fun y => by
    rw [hr, Res.addW_q, hrr, Acq.q]
  have nn := fun (x : Res) (y : Loc) => (x.wr y).nonneg
  have hown : 1 / (P.N : Rat) ≤ (σ.r.wr P.Lk).q := by
    rw [hq]; have := hf0.2.2; have := nn R P.Lk; have := nn R' P.Lk; grind
  have hHW : HoldingWX P tid S σ.r := by
    refine ⟨by rw [hq, hpool.1]; have := nn r0 P.C; have := nn R' P.C; grind, htid, ?_, by grind,
      fun j hj hne => ⟨fun hS => ?_, fun hS => ?_⟩⟩
    · rw [hq]; have := hf0.2.1; have := nn R (P.F tid); have := nn R' (P.F tid); grind
    · rw [hq]; have := (hpool.2 j hj).1 hS; have := nn r0 (P.K j); have := nn R' (P.K j); grind
    · rw [hq]; have := (hpool.2 j hj).2 hS; have := nn r0 (P.F j); have := nn R' (P.F j); grind
  -- clean: the thread holds the lock with the pool for `S` (`S tid = false`, `K tid` whole)
  have hHc : σ.cl → Holding P tid S rr := fun hc => by
    have hv := (hcl hc).1
    rw [hrr, Res.valid_addW] at hv
    rw [hrr]; exact holding_of_pool htid hN0 hf0 hv hpool
  refine ⟨SwpEnvG.storeOk_of_storeKind hsk (storeOk_xlockRelease hL hN0 hW hHW fun hc => ⟨hown, ?_⟩), ?_⟩
  · -- the clean mode facts
    have hsur : Bad P.N P.Lk P.C P.K P.F R → 1 / (P.N : Rat) < (σ.r.wr P.Lk).q := fun hbad => by
      rw [hq]; have := hf0.2.2; have := hbad.1; have := nn R' P.Lk; grind
    rcases (hcl hc).2 with hbad | ⟨hx, hlt⟩
    · exact .inr (hsur hbad)
    rcases hgb with ⟨ts, hX, hmax, hk, -, -⟩ | hbad
    · left
      have hH := hHc hc
      have hlen := filter_setTrue_length hH.2.1 P.N htid
      have hle : ((List.range P.N).filter (setTrue S tid)).length ≤ P.N :=
        Nat.le_trans (List.length_filter_le _ _) (by simp)
      have hrrC : 0 < (rr.wr P.C).q := by rw [hH.1]; decide
      refine ⟨k + 1, tw3, ⟨⟨?_, fun p hp => ?_⟩, by rw [hlen, hk]⟩, hvw⟩
      · rw [hr, Res.addW_X_self]
        refine .inr ⟨hrrC, ?_⟩
        rw [hx]
        refine Prod.ext ?_ rfl
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        have : k + 1 < 2 ^ 32 := by omega
        rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
      · rw [hr, Res.addW_X_self] at hp
        rcases hp with hp | ⟨-, rfl⟩
        · exact Nat.le_of_lt (hlt p hp)
        · exact Nat.le_refl _
    · exact .inr (hsur hbad)
  · -- after the release
    intro σ' tw Pc hg hcl' hcoh hPc hr''
    refine ⟨hW.mono hg, fun hc => ?_⟩
    rw [hcl'] at hc
    rw [hr'']
    have hH := hHc hc
    refine xlockRelease_post hL hN0 htid tw (hPc hc) ?_ hown fun hns p hp hp0 => ?_
    · rw [hr, Res.addW_wr_ne _ _ (hL.k_c tid htid)]; exact hH.2.2.2.1
    · exact Nat.lt_of_le_of_lt (hz hns p hp hp0) hcoh

end Kraken.Promising.SLR.EnvG.LockVC
