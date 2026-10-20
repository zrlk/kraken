/-
**The CAS spinlock on `EnvG`: the plan, the table predicates and the
per-access verification conditions**, for the worker
`casTtasWorker` (`EnvG/CasSmoke.lean`) against `EnvG`'s Out/Facts interface.

The specification is the SWP lock's, reused unchanged from the ISA-neutral
`SpinCommon` (`SLR/SpinCommon.lean`, `SLR/SpinAcquire.lean`: `Sys`, `World`,
`Fresh`, `World.lock_claim'`) and `Spinlock` (`SLR/SwpSpec.lean`: `Pool`,
`Good`, `Bad`, `lockPred`).

**The plan**: `casPlan P tid = lockPlan P tid` (`EnvG/CasRelease.lean`):
the release `Lk := 0` gives the pool and a share of the lock chosen by the
thread's clean knowledge (F1's `Plan.Split`).

**Table predicates** (positions of `casTtasWorker`):
- `Fr` (at `worker`, `try`, `spin`): the world, `Fresh`, no counter share, no
  forwarding item for the lock (the thread has not written it), and only
  writes of `0` in the write set of the lock (`LkZero`);
- `H1` (at `cs`): the world and `Acq`: the resource is the fresh one, the
  claimed slots of the `casa`'s read (the pool for `S`, and the counter
  relation `GoodC` or `Bad`), and the `casa`'s write `(1, tw)` to the lock,
  `tw` at or below the coherence view of the lock; in the `Good` case the
  counter's maximal write is at or below `vrNew` and `vwNew`;
- `H2 x5` (after `ldr w5, [x1]`): `H1`, and under the clean flag the
  resource is valid (so the thread is `Holding`) and the value read is `|S|`
  (or the acquired slot was `Bad`);
- `H3 x5` (after `str w5, [x1]`): the counter's write set has gained
  `(x5, tw)` above all its earlier writes, `tw ≤ vwOld`;
- `QEnd` (at the end): the world and, clean, `Post`.

**VCs**:
- `vc_casa`: `Fr → ok ∧ (step → Fr ∨ H1)` (failure / success), with the
  unclaimed read `StepRmwU` (a theorem since the claim fix:
  `EnvG/CasStepRmwU.lean`);
- `vc_ldr_spin`: `Fr → step → Fr`;
- `vc_ldr_c`: `H1 → step → H2`, through `read_max` under the clean flag;
- `vc_str_c`: `H2 → ok ∧ (step → H3)`;
- `vc_stlr`: `H3 → ok ∧ (step → QEnd)` (`storeOk_lockRelease`,
  `lockRelease_post`).

Phase-1 limits apply (single-access trees, read-side acquire only, releases
are stores).
-/
import Kraken.Promising.SLR.EnvG.CasSmoke
import Kraken.Promising.SLR.EnvG.CasRelease
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.Promising.SLR.SpinAcquire
import Kraken.Promising.SLR.SpinClaim
import Kraken.Promising.SLR.EnvG.RmwFailFwd

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon

/-! ## The plan -/

/-- The CAS lock's plan for thread `tid`: the release `Lk := 0` gives the
pool and a share of the lock, split by `lockSplit` (`EnvG/CasRelease.lean`). -/
noncomputable abbrev casPlan (P : Sys) (tid : Nat) : Plan := lockPlan P tid

/-- The environment of thread `tid`. -/
noncomputable abbrev E (P : Sys) (tid : Nat) : SharedEnv := EnvG isa Arch.armv8 tid (casPlan P tid)

theorem casPlan_rel_ne {P : Sys} {tid : Nat} {l : Loc} (h : l ≠ P.Lk) (v : Val) : (casPlan P tid).rel l v = false :=
  lockPlan_rel_ne h v

theorem casPlan_rel_one {P : Sys} {tid : Nat} : (casPlan P tid).rel P.Lk 1#128 = false := lockPlan_rel_one

/-! ## The `casa` -/

/-- The `casa w2, w3, [x0]` operation with `w2 = 0`, `w3 = 1`. -/
abbrev casOp : Val → Option Val := rmwOpBits 32 fun old => if old = 0#32 then some 1#32 else none

theorem casOp_some {old new : Val} (h : casOp old = some new) : BitVec.setWidth 32 old = 0 ∧ new = 1#128 := by
  simp only [rmwOpBits, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  split at ha
  · next h0 => exact ⟨h0, by cases ha; rfl⟩
  · cases ha

/-- **`RmwFacts` with the unclaimed read** (the proposed `Facts.lean` edit):
in the success branch, the message read is not claimed at the anchor ghost. -/
def RmwFactsU (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State isa) (k : RmwKind) (l : Loc)
    (op : Val → Option Val) (old : Val) : Prop :=
  ∃ (c : Config isa) (tr : Time), AnchorOk tid σ c σ'.g ∧
    ReadAt A tid (rmwReadViews A σ.vs) c (A.rmwKind k).loadKind l tr old ∧
    VLe σ.vs σ'.vs ∧ σ'.cl = σ.cl ∧
    ((A.loadKind (A.rmwKind k).loadKind).isAcquire = true → ¬ Fwded σ.vs l tr →
      tr ≤ σ'.vs.vrNew ∧ tr ≤ σ'.vs.vwNew) ∧
    ((op old = none ∧ σ'.r = σ.r) ∨
     (∃ (new : Val) (tw : Time), op old = some new ∧ tr < tw ∧ ¬ σ'.g.Claimed (l, tr) ∧
       WriteBound A σ.vs (A.rmwKind k).storeKind l tw ∧ tw ≤ σ'.vs.getCoh l ∧
       ∃ Pc : Prop, (σ.cl → Pc) ∧ σ'.r = pl.afterRmw l new tr tw σ'.g Pc σ.r))

/-- **The strengthened RMW step facts** (open: `step_rmwFacts` plus the
unclaimed read; becomes a theorem with the proposed `RmwOut` edit). -/
def StepRmwU (A : Arch) (tid : Nat) (pl : Plan) : Prop :=
  ∀ (σ σ' : State isa) (k : RmwKind) (addr : BitVec 64) (n : Nat) (op : Val → Option Val) (old : Val),
    (EnvG isa A tid pl).step (.rmw k addr n op) σ old σ' → RmwFactsU A tid pl σ σ' k ⟨addr, n⟩ op old

/-- A failed RMW leaves the forwarding items alone (from the outcome: the
read and the optional fence do not touch them). The AArch64 instance of
`envG_rmw_fail_getFwd` (`EnvG/RmwFailFwd.lean`). -/
theorem rmw_fail_getFwd {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val} (h : (EnvG isa A tid pl).step (.rmw k addr n op) σ old σ')
    (hop : op old = none) (l : Loc) : σ'.vs.getFwd l = σ.vs.getFwd l :=
  envG_rmw_fail_getFwd h hop l

/-! ## The table predicates -/

/-- Every write of `Lk` in `r`'s write set is of `0` (before the thread's
own `casa`: the initial message). -/
def LkZero (P : Sys) (r : Res) : Prop := ∀ p, (r.wr P.Lk).X p → p.1 = 0

/-- **Before taking the lock** (`worker`, `try`, `spin`). -/
def Fr (P : Sys) (tid : Nat) (σ : State isa) : Prop :=
  World P σ.g ∧ Fresh P tid σ.r ∧ (σ.r.wr P.C).q = 0 ∧ σ.vs.getFwd P.Lk = none ∧ LkZero P σ.r

/-- The counter relation of an acquired `Good` part `R` for `S`: the
counter's maximal write `(k, ts)` with `k = |S|`, `ts` at or below the views
`vs`. -/
def GoodC (P : Sys) (S : Nat → Bool) (k : Nat) (vs : Views) (R : Res) : Prop :=
  ∃ ts, (R.wr P.C).X (BitVec.ofNat 128 k, ts) ∧ (∀ p, (R.wr P.C).X p → p.2 ≤ ts) ∧
    k = ((List.range P.N).filter S).length ∧ ts ≤ vs.vrNew ∧ ts ≤ vs.vwNew

/-- **The resource after a successful `casa`**: the fresh resource `r0` (no
counter share, only writes of `0` to the lock), the claimed slots `R ⋅ R'`
(`R'` without counter share), and the `casa`'s write `(1, tw)` to the lock,
at or below the coherence view of the lock; `R` holds the pool for `S`, and
the counter relation (`GoodC`) or `Bad`. -/
def Acq (P : Sys) (tid : Nat) (S : Nat → Bool) (k : Nat) (vs : Views) (rr R : Res) : Prop :=
  ∃ r0 R' : Res, ∃ tw : Time, rr = (r0.op (R.op R')).addW P.Lk (1#128, tw) ∧ Fresh P tid r0 ∧
    (r0.wr P.C).q = 0 ∧ (R'.wr P.C).q = 0 ∧ LkZero P r0 ∧ tw ≤ vs.getCoh P.Lk ∧ Pool P.N P.C P.K P.F S R ∧
    (GoodC P S k vs R ∨ Bad P.N P.Lk P.C P.K P.F R)

theorem Acq.mono {P : Sys} {tid : Nat} {S : Nat → Bool} {k : Nat} {vs vs' : Views} {rr R : Res}
    (h : Acq P tid S k vs rr R) (h1 : vs.vrNew ≤ vs'.vrNew) (h2 : vs.vwNew ≤ vs'.vwNew)
    (h3 : vs.getCoh P.Lk ≤ vs'.getCoh P.Lk) : Acq P tid S k vs' rr R := by
  obtain ⟨r0, R', tw, e, hf, h0, h0', hz, hc, hp, hgb⟩ := h
  refine ⟨r0, R', tw, e, hf, h0, h0', hz, Nat.le_trans hc h3, hp,
    hgb.imp (fun ⟨ts, hX, hm, hk, a, b⟩ => ⟨ts, hX, hm, hk, ?_, ?_⟩) id⟩
  · exact Nat.le_trans a h1
  · exact Nat.le_trans b h2

/-- The fractions in `Acq`: the sum of the three parts. -/
theorem Acq.q {P : Sys} {r0 R R' : Res} {tw : Time} (y : Loc) :
    ((((r0.op (R.op R')).addW P.Lk (1#128, tw))).wr y).q = (r0.wr y).q + ((R.wr y).q + (R'.wr y).q) := by
  rw [Res.addW_q]; rfl

/-- **The counter in `Acq`** (`Lk ≠ C`): exactly a full share, and in the
`Good` case the maximal write `(k, ts)`. -/
theorem Acq.counter {P : Sys} {tid : Nat} {S : Nat → Bool} {k : Nat} {vs : Views} {rr R : Res}
    (hLC : P.Lk ≠ P.C) (h : Acq P tid S k vs rr R) :
    (rr.wr P.C).q = 1 ∧ (GoodC P S k vs R → ∃ ts, (rr.wr P.C).X (BitVec.ofNat 128 k, ts) ∧
          (∀ p, (rr.wr P.C).X p → p.2 ≤ ts) ∧ ts ≤ vs.vrNew ∧ ts ≤ vs.vwNew) := by
  obtain ⟨r0, R', tw, rfl, -, h0, h0', -, -, hpool, -⟩ := h
  have hwr : ((r0.op (R.op R')).addW P.Lk (1#128, tw)).wr P.C = (r0.wr P.C).op ((R.wr P.C).op (R'.wr P.C)) :=
    Res.addW_wr_ne _ _ (Ne.symm hLC)
  rw [hwr]
  refine ⟨?_, fun hgood => ?_⟩
  · change (r0.wr P.C).q + ((R.wr P.C).q + (R'.wr P.C).q) = 1
    rw [h0, h0', hpool.1]; grind
  obtain ⟨ts, hX, hmax, -, h1, h2⟩ := hgood
  refine ⟨ts, .inr (.inl hX), fun p hp => ?_, h1, h2⟩
  rcases hp with hp | hp | hp
  · exact absurd hp ((r0.wr P.C).zero h0 p)
  · exact hmax p hp
  · exact absurd hp ((R'.wr P.C).zero h0' p)

/-- **Holding the lock** (`cs`). -/
def H1 (P : Sys) (tid : Nat) (σ : State isa) : Prop :=
  World P σ.g ∧ ∃ S k R, Acq P tid S k σ.vs σ.r R

/-- **After the counter load** of `x5` (low word): under the clean flag, the
resource is valid (with the acquired slots: `Holding`) and the counter value
is `|S|` (or the slot was `Bad`). -/
def H2 (P : Sys) (tid : Nat) (x5 : BitVec 32) (σ : State isa) : Prop :=
  World P σ.g ∧ ∃ S k R, Acq P tid S k σ.vs σ.r R ∧
    (σ.cl → σ.r.valid ∧ (Bad P.N P.Lk P.C P.K P.F R ∨ x5 = BitVec.ofNat 32 k))

/-- **After the counter store** of `v` at `tw`: the counter's write set has
gained `(v, tw)` above all its earlier writes, `tw` at or below `vwOld`. -/
def H3 (P : Sys) (tid : Nat) (x5 : BitVec 32) (σ : State isa) : Prop :=
  World P σ.g ∧ ∃ S k R rr, ∃ tw : Time, Acq P tid S k σ.vs rr R ∧
    σ.r = rr.addW P.C (BitVec.setWidth 128 x5, tw) ∧ tw ≤ σ.vs.vwOld ∧
    (Bad P.N P.Lk P.C P.K P.F R ∨ ∀ p, (rr.wr P.C).X p → p.2 < tw) ∧
    (σ.cl → rr.valid ∧ (Bad P.N P.Lk P.C P.K P.F R ∨ x5 = BitVec.ofNat 32 (k + 1)))

/-- **The end**: the world, and under the clean flag the worker's `Post`
(`hB` of `ofSafelyEnvG`). -/
def QEnd (P : Sys) (σ : State isa) : Prop := World P σ.g ∧ (σ.cl → Post P.N P.Lk P.K σ.r)

/-! ## The VCs -/

variable {P : Sys} {tid : Nat}

/-- **VC `ldr w2, [x0]`** (the spin): `Fr` is kept. -/
theorem vc_ldr_spin (σ : State isa) (h : Fr P tid σ) :
    ∀ v (σ' : State isa), (E P tid).step (.load .plain false P.Lk.addr P.Lk.bytes) σ v σ' → Fr P tid σ' := by
  intro v σ' hs
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := step_loadFacts hs
  obtain ⟨hW, hf, hC, hfw, hz⟩ := h
  exact ⟨hW.mono hanc.ghost, hr ▸ hf, hr ▸ hC, by rw [hlv.getFwd]; exact hfw, hr ▸ hz⟩

/-- The claimed slots are valid together (`Erase.valid` at the anchor). -/
theorem valid_claimed {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config isa} (E' : Erase rF g T c)
    (hn : tid < c.threads.size) (x : Loc) (tr : Time) : (Res.prod ((claimedSlots g x tr).map (·.res))).valid := by
  have e : setRes rF tid (rF tid) = rF := by
    funext i; unfold setRes; split <;> simp_all
  exact Res.valid_op_right (Erase.valid_claim (e ▸ E') hn x tr)

/-- **VC `casa w2, w3, [x0]`** (`w2 = 0`, `w3 = 1`, acquire): permitted
(the lock share, a pure written value `1`, the claim condition: an acquire
not forwarded), and every outcome either fails (`Fr` kept) or takes the lock
(`H1`), given the unclaimed read (`StepRmwU`, a theorem:
`EnvG/CasStepRmwU.lean`). -/
theorem vc_casa (hU : StepRmwU Arch.armv8 tid (casPlan P tid)) (hN0 : 0 < P.N) (σ : State isa) (h : Fr P tid σ) :
    (E P tid).ok (.rmw .acq P.Lk.addr P.Lk.bytes casOp) σ ∧
      ∀ old (σ' : State isa), (E P tid).step (.rmw .acq P.Lk.addr P.Lk.bytes casOp) σ old σ' →
        (BitVec.setWidth 32 old ≠ 0 ∧ Fr P tid σ') ∨ (BitVec.setWidth 32 old = 0 ∧ H1 P tid σ') := by
  obtain ⟨hW, hf, hC, hfw, hz⟩ := h
  have hnf : ∀ tr, ¬ Fwded σ.vs P.Lk tr := fun tr ⟨f, hf', _⟩ => by rw [hfw] at hf'; cases hf'
  refine ⟨⟨?_, fun c g tr old new _ _ hop => ⟨fun _ => .inr ⟨rfl, hnf tr⟩, fun _ => ?_, fun hr => ?_⟩⟩, ?_⟩
  · show 0 < (σ.r.wr P.Lk).q
    have := one_div_pos hN0; have := hf.2.2; grind
  · obtain ⟨-, rfl⟩ := casOp_some hop
    rw [hW.1]; exact lockPred_pure (by decide)
  · obtain ⟨-, rfl⟩ := casOp_some hop
    rw [casPlan_rel_one] at hr; cases hr
  intro old σ' hs
  obtain ⟨c, tr, hanc, hrd, hvle, -, hacq, hbr⟩ := hU _ _ _ _ _ _ _ hs
  rcases hbr with ⟨hop, hr⟩ | ⟨new, tw, hop, -, hun, -, hcoh, hr⟩
  · refine .inl ⟨fun h0 => ?_, hW.mono hanc.ghost, hr ▸ hf, hr ▸ hC, by rw [rmw_fail_getFwd hs hop]; exact hfw,
      hr ▸ hz⟩
    simp [rmwOpBits, h0] at hop
  obtain ⟨hz0, rfl⟩ := casOp_some hop
  refine .inr ⟨hz0, hW.mono hanc.ghost, ?_⟩
  obtain ⟨rF, E'⟩ := hanc.erase
  obtain ⟨R, R', hprod, hgb⟩ := World.lock_claim' (hW.mono hanc.ghost) E' hrd.val hz0 hun
  have hval := valid_claimed (tid := tid) E' hanc.lt P.Lk tr
  rw [hprod] at hval
  obtain ⟨_, -, hr⟩ := hr
  have hr' : σ'.r = (σ.r.op (R.op R')).addW P.Lk (1#128, tw) := by
    rw [hr, Plan.afterRmw, Plan.after, casPlan_rel_one, hprod]; rfl
  have hacq' := hacq rfl (hnf tr)
  have hR'C : ∀ S, Pool P.N P.C P.K P.F S R → (R'.wr P.C).q = 0 := fun S hpool => by
    have h1 := hval.1 P.C
    change (R.wr P.C).q + (R'.wr P.C).q ≤ 1 at h1
    have := (R'.wr P.C).nonneg; rw [hpool.1] at h1; grind
  rcases hgb with ⟨k, S, ts, hpool, hX, hmax, hk, hts⟩ | hbad
  · exact ⟨S, k, R, σ.r, R', tw, hr', hf, hC, hR'C S hpool, hz, hcoh, hpool,
      .inl ⟨ts, hX, hmax, hk, Nat.le_trans hts hacq'.1, Nat.le_trans hts hacq'.2⟩⟩
  · obtain ⟨S, hpool⟩ := hbad.2
    exact ⟨S, 0, R, σ.r, R', tw, hr', hf, hC, hR'C S hpool, hz, hcoh, hpool, .inr hbad⟩

/-- **VC `ldr w5, [x1]`** (the counter): `H1` is kept, and under the clean
flag of the load's anchor the resource is valid and a `Good` acquisition
reads the counter's maximal write `|S|` (`read_max`: the thread holds all of
the counter). -/
theorem vc_ldr_c (hLC : P.Lk ≠ P.C) (σ : State isa) (h : H1 P tid σ) :
    ∀ v (σ' : State isa), (E P tid).step (.load .plain false P.C.addr P.C.bytes) σ v σ' →
      H2 P tid (BitVec.setWidth 32 v) σ' := by
  intro v σ' hs
  obtain ⟨hanc, hr, hcl, tr, hrd, hlv, -⟩ := step_loadFacts hs
  obtain ⟨hW, S, k, R, hA⟩ := h
  refine ⟨hW.mono hanc.ghost, S, k, R, by rw [hr]; exact hA.mono hlv.mono.vrNew hlv.mono.vwNew (hlv.mono.coh _),
    fun hc => ?_⟩
  rw [hcl] at hc
  obtain ⟨-, rF, E'⟩ := hc
  refine ⟨by rw [hr]; exact Res.valid_op_left (Erase.valid_claim E' hanc.lt P.C 0), ?_⟩
  have hA' := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgb⟩ := hA'
  rcases hgb with hgood | hbad
  · refine .inr ?_
    obtain ⟨ts, hX, hmax, h1, -⟩ := (Acq.counter hLC hA).2 hgood
    obtain ⟨t, ht⟩ : ∃ t, σ'.snap.threads[tid]? = some t :=
      ⟨σ'.snap.threads[tid]'hanc.lt, Array.getElem?_eq_getElem hanc.lt⟩
    have hp : t.prom.contains tr = false := by
      have := hrd.notOwn
      simp only [ownProm, ht, Option.map_some, Option.getD_some] at this
      exact this
    obtain ⟨-, rfl⟩ := read_max E' ht (Acq.counter hLC hA).1 hX hmax hrd.val hp hrd.window
      (Nat.le_trans h1 (le_readBound_vrNew _ _ _ _))
    apply BitVec.eq_of_toNat_eq; simp
  · exact .inl hbad

/-- **VC `str w5, [x1]`** (the counter, plain, pure value): permitted (a
full counter share, the counter's predicate pure), and every outcome adds
`(x5, tw)` above every earlier counter write (`tw > vwNew ≥ ts`), with
`tw ≤ vwOld` after the store. -/
theorem vc_str_c (hLC : P.Lk ≠ P.C) (x5 : BitVec 32) (σ : State isa) (h : H2 P tid x5 σ) :
    (E P tid).ok (.store .plain false P.C.addr P.C.bytes (BitVec.setWidth 128 (x5 + 1))) σ ∧
      ∀ b (σ' : State isa), (E P tid).step (.store .plain false P.C.addr P.C.bytes (BitVec.setWidth 128 (x5 + 1))) σ b σ' →
        H3 P tid (x5 + 1) σ' := by
  obtain ⟨hW, S, k, R, hA, hcl⟩ := h
  have hq := (Acq.counter hLC hA).1
  have hne : P.C ≠ P.Lk := Ne.symm hLC
  refine ⟨⟨rfl, show 0 < (σ.r.wr P.C).q by rw [hq]; decide, fun _ => hW.2.1 _,
    fun hr => by rw [casPlan_rel_ne hne] at hr; cases hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, -, hwb, hwv, -, hr, hcl', -⟩ := step_storeFacts hs
  obtain ⟨_, -, hr⟩ := hr
  have hr' : σ'.r = σ.r.addW P.C (BitVec.setWidth 128 (x5 + 1), tw) := by
    rw [hr, Plan.after, casPlan_rel_ne hne]; rfl
  refine ⟨hW.mono hanc.ghost, S, k, R, σ.r, tw, hA.mono hwv.mono.vrNew hwv.mono.vwNew (hwv.mono.coh _), hr',
    hwv.vwOld (by decide), ?_, fun hc => ?_⟩
  · have hA' := hA
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hgb⟩ := hA'
    rcases hgb with hgood | hbad
    · obtain ⟨ts, -, hmax, -, h2⟩ := (Acq.counter hLC hA).2 hgood
      exact .inr fun p hp => Nat.lt_of_le_of_lt (Nat.le_trans (hmax p hp) h2) hwb.vwNew
    · exact .inl hbad
  · rw [hcl'] at hc
    obtain ⟨hv, hb⟩ := hcl hc
    refine ⟨hv, ?_⟩
    rcases hb with hb | hx
    · exact .inl hb
    · exact .inr (by rw [hx]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add])


/-- **VC `stlr wzr, [x0]`** (the lock release, a release store of `0`,
`lockPlan`'s split): permitted from `H3` (`storeOk_lockRelease`; clean: the
counter relation for `S[tid := true]` at the store `(k + 1, tw)`, or a
surplus of the lock from a `Bad` slot), and every outcome ends in `QEnd`
(`lockRelease_post`: without a surplus the acquired slots held no lock share,
so the write set of `Lk` is the fresh `0`s and the own `casa`'s `(1, tw')`,
`tw' ≤ coh < tw`). -/
theorem vc_stlr (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32)
    (x5 : BitVec 32) (σ : State isa) (h : H3 P tid x5 σ) :
    (E P tid).ok (.store .rel false P.Lk.addr P.Lk.bytes 0) σ ∧
      ∀ b (σ' : State isa), (E P tid).step (.store .rel false P.Lk.addr P.Lk.bytes 0) σ b σ' → QEnd P σ' := by
  obtain ⟨hW, S, k, R, rr, tw3, hA, hr, hvw, hb, hcl⟩ := h
  obtain ⟨r0, R', twc, hrr, hf0, h0, h0', hz0, hcoh, hpool, hgb⟩ := hA
  have hN := one_div_pos hN0
  have hq : ∀ y, (σ.r.wr y).q = (r0.wr y).q + ((R.wr y).q + (R'.wr y).q) := fun y => by
    rw [hr, Res.addW_q, hrr, Acq.q]
  have nn := fun (x : Res) (y : Loc) => (x.wr y).nonneg
  have hown : 1 / (P.N : Rat) ≤ (σ.r.wr P.Lk).q := by
    rw [hq]; have := hf0.2.2; have := nn R P.Lk; have := nn R' P.Lk; grind
  have hHW : HoldingW P tid S σ.r := by
    refine ⟨by rw [hq, h0, h0', hpool.1]; grind, htid, ?_, by grind, fun j hj hne => ⟨fun hS => ?_, fun hS => ?_⟩⟩
    · rw [hq]; have := hf0.2.1; have := nn R (P.F tid); have := nn R' (P.F tid); grind
    · rw [hq]; have := (hpool.2 j hj).1 hS; have := nn r0 (P.K j); have := nn R' (P.K j); grind
    · rw [hq]; have := (hpool.2 j hj).2 hS; have := nn r0 (P.F j); have := nn R' (P.F j); grind
  -- clean: the thread holds the lock with the pool for `S` (`S tid = false`, `K tid` whole)
  have hHc : σ.cl → Holding P tid S rr := fun hc => by
    have hv := (hcl hc).1
    rw [hrr, Res.valid_addW] at hv
    rw [hrr]; exact holding_of_pool htid hN0 hf0 hv hpool
  refine ⟨storeOk_lockRelease hL hN0 hW hHW fun hc => ⟨hown, ?_⟩, ?_⟩
  · -- the clean mode facts
    have hsur : Bad P.N P.Lk P.C P.K P.F R → 1 / (P.N : Rat) < (σ.r.wr P.Lk).q := fun hbad => by
      rw [hq]; have := hf0.2.2; have := hbad.1; have := nn R' P.Lk; grind
    rcases (hcl hc).2 with hbad | hx
    · exact .inr (hsur hbad)
    rcases hgb with ⟨ts, hX, hmax, hk, -, -⟩ | hbad
    · rcases hb with hbad | hlt
      · exact .inr (hsur hbad)
      left
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
    intro b σ' hs
    obtain ⟨c, tw, hanc, -, hwb, -, -, hr', hcl', -⟩ := step_storeFacts hs
    refine ⟨hW.mono hanc.ghost, fun hc => ?_⟩
    rw [hcl'] at hc
    obtain ⟨Pc, hPc, hr''⟩ := hr'
    rw [hr'']
    have hH := hHc hc
    refine lockRelease_post hL hN0 htid tw (hPc hc) ?_ hown fun hns p hp hp0 => ?_
    · rw [hr, Res.addW_wr_ne _ _ (hL.k_c tid htid)]; exact hH.2.2.2.1
    · -- no surplus: the acquired slots hold no lock share
      have hRq : (R.wr P.Lk).q = 0 := by
        have := hf0.2.2; have := nn R P.Lk; have := nn R' P.Lk; rw [hq] at hns; grind
      have hR'q : (R'.wr P.Lk).q = 0 := by
        have := hf0.2.2; have := nn R P.Lk; have := nn R' P.Lk; rw [hq] at hns; grind
      rw [hr, Res.addW_wr_ne _ _ hL.lk_c, hrr, Res.addW_X_self] at hp
      rcases hp with (hp | hp | hp) | ⟨-, rfl⟩
      · exact absurd (hz0 p hp) hp0
      · exact absurd hp ((R.wr P.Lk).zero hRq p)
      · exact absurd hp ((R'.wr P.Lk).zero hR'q p)
      · exact Nat.lt_of_le_of_lt hcoh hwb.coh

end Kraken.Promising.SLR.EnvG.CasSmoke
