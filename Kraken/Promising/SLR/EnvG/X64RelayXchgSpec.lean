/-
**Part 3: the x64 three-thread relay through
`xchg` — programs, predicates and VCs** (`mp_relay3_xchg.kl`; the x64 copy
of the relay proof's `EnvG/RelaySpec.lean` and the `swpl` relay's `EnvG/RelaySwplSpec.lean`,
which import AArch64 files).

Three threads hand the data word `Dt = ⟨d, 4⟩` along, under `Arch.tso`:
- **writer** (thread `0`): x64 MP's `mpWriterX` (`movl` data `:= 42`, then
  `movl` `f1 := 1`, a planned release store giving all of `Dt` to the slot of
  the relay's acquire id);
- **relay** (thread `1`, `relayX` below): spins on `movl (%rdi), %eax` (an
  acquire under `Arch.tso`, which **takes** `Dt`, as the x64 take route's
  `takeReaderX`), stores `43` to it, and releases it with **`xchgl %ecx,
  (%rdx)`** (`f2 := 1`; an `.acqRel` RMW, plan `mpPlan rp.Q`: `F2 := 1` gives
  `[Dt]`), on `EnvGTCX` (`EnvG/X64RmwGhostLink.lean`);
- **reader** (thread `2`): x64 MP's `mpReaderX` text on `f2`, run on
  `EnvGTX`: it takes `Dt` at its flag load, then reads `43` from its own
  resource (its data load is an acquire too and may take; it holds all of
  `Dt`, so a take adds nothing, `takeEff_wr_full`).

**The `xchg` claims** (every x64 RMW is `.acqRel`, `claimSlotsC_acqRel`) and
**gives from the relay's own resource** (`RmwOkC`): the permission is the relay proof's
`vc_r3` argument (`flag43` of all of `Dt` at every anchor and fresh `tw`),
and the outcome keeps the token `W2` (the claim only adds,
`Res.op_wr_q_ge`). On the old `EnvG` (`ofSafelyEnvGRX`) this needed
`RelRmwGiveOk` with a non-empty give list, which is not provable
(`KNOWN_GAPS.md`).

**Parameters**: `RP` (`f1`, `f2`, `d`, tokens `W`, `W2`), seen as two x64 MP
parameter sets sharing `d`: `rp.P = ⟨f1, d, W⟩` (MP's `flagPred`, releasing
`Good` at `1`) and `rp.Q = ⟨f2, d, W2⟩` (`flag43`, releasing `Good43`).

**The VCs**:
- relay, `movl (%rdi), %eax`: `vc_r1` (the x64 take route's `vc_k1`, plus the relay's
  world `RW`);
- relay, `movl $43, (%rsi)` (a release store to the unplanned `Dt`):
  `vc_r2`, all of `Dt` with maximal write `(43, tw)`, `tw ≤ vwOld`;
- relay, `xchgl %ecx, (%rdx)` (any operation writing `1`): `vc_r3`;
- reader, `movl (%rdi), %eax`: `vc_d1`; reader, `movl (%rsi), %ebx`: `vc_d2`.

Phase-1 limits (single-access trees, read-side acquire only, takes only at
non-forwarded acquire loads, no take at an RMW node) apply; none is binding.
-/
import Kraken.Promising.SLR.EnvG.X64TakeMp
import Kraken.Promising.SLR.EnvG.X64RmwGhostVCGen

namespace Kraken.Promising.X64.EnvG.RelayX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.TakeMp
open Kraken.X64.Parser

/-! ## The relay program -/

/-- **The x64 relay**: spin on the flag at `(%rdi)` until non-zero, store `43`
to the data at `(%rsi)`, release the flag at `(%rdx)` with `xchgl` (the old
value goes to `ecx`). -/
def relayX : Program := parse("
spin:
  movl (%rdi), %eax
  cmpl $0, %eax
  je spin
  movl $43, (%rsi)
  movl $1, %ecx
  xchgl %ecx, (%rdx)
done_y:
")

/-- info: 8 -/
#guard_msgs in
#eval relayX.length

/-! ## Parameters -/

/-- The relay's parameters: the two flags, the data, and the tokens of the
writer and the relay. -/
structure RP where
  f1 : BitVec 64
  f2 : BitVec 64
  d : BitVec 64
  W : Loc
  W2 : Loc

/-- The writer's MP parameters (flag `f1`). -/
abbrev RP.P (rp : RP) : Params := ⟨rp.f1, rp.d, rp.W⟩

/-- The relay's MP parameters (flag `f2`). -/
abbrev RP.Q (rp : RP) : Params := ⟨rp.f2, rp.d, rp.W2⟩

/-- The relay's shared layout: `f1`, `d`, `f2`. -/
abbrev relayS (rp : RP) : SharedEnv.Layout := [(rp.f1, 4), (rp.d, 4), (rp.f2, 4)]

theorem relayS_le16 (rp : RP) : Le16 (relayS rp) := fun x hx => by
  simp only [relayS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact (by decide : 4 ≤ 16)

/-! ## The relay's flag predicate (copy of the relay proof's `flag43`) -/

/-- The relayed state: all of `Dt`, whose maximal write is `(43, ts)` with
`ts ≤ V`. -/
def Good43 (Dt : Loc) (V : View) (r : Res) : Prop :=
  (r.wr Dt).q = 1 ∧ ∃ ts, (r.wr Dt).X (43#128, ts) ∧ (∀ p, (r.wr Dt).X p → p.2 ≤ ts) ∧ ts ≤ V

/-- **`f2`'s release and acquire predicate**: `Good43` at a non-zero low
word. -/
def flag43 (Dt : Loc) : Pred where
  P v _ V r := BitVec.setWidth 32 v ≠ 0 → Good43 Dt V r
  mono _ _ _ _ _ _ h := h

theorem flag43_pure {Dt : Loc} {v : Val} (hv : BitVec.setWidth 32 v = 0) : Pred.Pure (flag43 Dt) v :=
  fun _ _ h => absurd hv h

theorem flag43_impure {Dt : Loc} {v : Val} (hv : BitVec.setWidth 32 v ≠ 0) : ¬ Pred.Pure (flag43 Dt) v :=
  fun h => by
    have := (h default 0 hv).1
    simp [Res.unit, Perm.unit] at this

/-! ## Takes only add (copy of the relay proof's `takeEff_wr_q_ge`) -/

/-- A load's take never lowers a write fraction. -/
theorem takeEff_wr_q_ge {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (ha : TakeEff A k vs l tr r ga a) (x : Loc) : (r.wr x).q ≤ (a.r.wr x).q := by
  by_cases hc : TakeCond A k vs l tr
  · rw [ha.1 hc]
    obtain ⟨e, he, -⟩ := takeFold_wr l tr x (ga.acqIds r.acq l) ⟨r, ga, []⟩
    show _ ≤ ((takeAll l tr r ga).r.wr x).q
    unfold takeAll; rw [he]
    have := e.nonneg
    show (r.wr x).q ≤ (r.wr x).q + e.q
    grind
  · rw [ha.2 hc]; exact Rat.le_refl

/-! ## The relay's predicates -/

/-- The relay's world: `f2`'s release predicate is `flag43`, a share of
`f2`, and the token `W2`. -/
def RW (Q : Params) (σ : EStateX) : Prop :=
  σ.g.rel Q.Fl = flag43 Q.Dt ∧ 0 < (σ.r.wr Q.Fl).q ∧ 1 ≤ (σ.r.wr Q.W).q

/-- Before the flag load (the loop invariant): the x64 take route's `K1` on `f1`, and
the relay's world. -/
def RK1 (rp : RP) (σ : EStateX) : Prop := K1 rp.P σ ∧ RW rp.Q σ

/-- After the take: the x64 take route's `K2`, and the relay's world. -/
def RK2 (rp : RP) (σ : EStateX) : Prop := K2 rp.P σ ∧ RW rp.Q σ

/-- After `movl $43, (%rsi)`: the world, all of `Dt` with maximal write
`(43, tw)`, `tw ≤ vwOld`. -/
def RK3 (rp : RP) (σ : EStateX) : Prop :=
  RW rp.Q σ ∧ (σ.r.wr rp.Q.Dt).q = 1 ∧
    ∃ tw, (σ.r.wr rp.Q.Dt).X (43#128, tw) ∧ (∀ p, (σ.r.wr rp.Q.Dt).X p → p.2 ≤ tw) ∧ tw ≤ σ.vs.vwOld

/-- At the end: the token `W2`. -/
def RK4 (rp : RP) (σ : EStateX) : Prop := 1 ≤ (σ.r.wr rp.Q.W).q

theorem RK1.fence {rp : RP} {σ σ' : EStateX} (h : RK1 rp σ) (hf : FenceLe σ σ') : RK1 rp σ' :=
  ⟨h.1.fence hf, by unfold RW; rw [hf.g, hf.r]; exact h.2⟩

theorem RK2.fence {rp : RP} {σ σ' : EStateX} (h : RK2 rp σ) (hf : FenceLe σ σ') : RK2 rp σ' :=
  ⟨h.1.fence hf, by unfold RW; rw [hf.g, hf.r]; exact h.2⟩

theorem RK3.fence {rp : RP} {σ σ' : EStateX} (h : RK3 rp σ) (hf : FenceLe σ σ') : RK3 rp σ' := by
  unfold RK3 RW; rw [hf.g, hf.r, hf.vs]; exact h

theorem RK4.fence {rp : RP} {σ σ' : EStateX} (h : RK4 rp σ) (hf : FenceLe σ σ') : RK4 rp σ' := by
  unfold RK4; rw [hf.r]; exact h

/-- The relay's environment: `EnvGTCX` (taking loads, claim-conditional
RMWs) under `Arch.tso`, the plan `F2 := 1` gives `[Dt]`, the layout
`relayS`. -/
abbrev ERX (rp : RP) (tid : Nat) : SharedEnv := EnvGTCX Arch.tso tid (mpPlan rp.Q) (relayS rp)

/-! ## The relay's VCs -/

/-- **VC R1** (`movl (%rdi), %eax`, an acquire under `Arch.tso`): a zero
flag keeps `RK1`, a non-zero flag takes all of `Dt` (`RK2`). The load step of
`EnvGTCX` is `EnvGTX`'s, so the x64 take route's `vc_k1` applies. -/
theorem vc_r1 {rp : RP} (tid : Nat) (σ : EStateX) (h : RK1 rp σ) :
    ∀ v (σ' : EStateX), (ERX rp tid).step (.load .plain false rp.f1 4) σ v σ' →
      (BitVec.setWidth 32 v = 0 → RK1 rp σ') ∧ (BitVec.setWidth 32 v ≠ 0 → RK2 rp σ') := by
  intro v σ' hs
  have hk := vc_k1 (P := rp.P) tid σ h.1 v σ' hs
  obtain ⟨ga, hanc, -, -, tr, -, -, a, ha, hr, hg, -⟩ := step_loadFactsTCX (I := isa) (A := Arch.tso)
    (pl := mpPlan rp.Q) hs
  obtain ⟨hrel, hF, hW⟩ := h.2
  have hrel' : σ'.g.rel = σ.g.rel := by rw [hg, (ha.ghost_le).rel, hanc.rel]
  have hw : RW rp.Q σ' := ⟨by rw [hrel']; exact hrel, by rw [hr]; have := takeEff_wr_q_ge ha rp.Q.Fl; grind,
    by rw [hr]; have := takeEff_wr_q_ge ha rp.Q.W; grind⟩
  exact ⟨fun h0 => ⟨hk.1 h0, hw⟩, fun h0 => ⟨hk.2 h0, hw⟩⟩

/-- **VC R2** (`movl $43, (%rsi)`, a release store under `Arch.tso` to the
unplanned `Dt`): permitted, and gives `RK3`. -/
theorem vc_r2 {rp : RP} (hL : MpLocs rp.Q) (tid : Nat) (σ : EStateX) (h : RK2 rp σ) :
    (ERX rp tid).ok (.store .plain false rp.d 4 43#128) σ ∧
      ∀ b (σ' : EStateX), (ERX rp tid).step (.store .plain false rp.d 4 43#128) σ b σ' → RK3 rp σ' := by
  obtain ⟨⟨hpure, hq, hmax⟩, hrel, hF, hW⟩ := h
  have hne : rp.Q.Fl ≠ rp.Q.Dt := hL.fl_dt
  refine ⟨⟨⟨rfl, by rw [hq]; decide, fun _ => hpure _, fun hr => by simp [mpPlan, hne] at hr⟩,
    by simp [SharedEnv.AccessIn]⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, -, hwb, hwv, -, ⟨Q, -, hr⟩, -⟩ := step_storeFactsTCX (I := isa) (A := Arch.tso)
    (pl := mpPlan rp.Q) hs
  have hr' : σ'.r = σ.r.addW rp.Q.Dt (43#128, tw) := by simpa [mpPlan, hne] using hr
  refine ⟨⟨by rw [hanc.rel]; exact hrel, by rw [hr', Res.addW_q]; exact hF, by rw [hr', Res.addW_q]; exact hW⟩,
    by rw [hr', Res.addW_q]; exact hq, tw, ?_, fun p hp => ?_, hwv.vwOld (by decide)⟩
  · rw [hr', Res.addW_X_self, hq]; exact .inr ⟨by decide, rfl⟩
  · rw [hr', Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hmax p hp) hwb.vwNew)
    · exact Nat.le_refl _

/-- **VC R3 by `xchg`** (`xchgl %ecx, (%rdx)`, an `.acqRel` RMW writing `1`
to `f2`): the planned release is permitted on `EnvGTCX` (`F2` held; at every
anchor, read and fresh `tw`, `flag43` of all of `Dt`, given from the relay's
own resource), and every outcome keeps the token `W2` (the `xchg` claims the
read message's update slots, which only adds). -/
theorem vc_r3 {rp : RP} (hL : MpLocs rp.Q) (tid : Nat) (σ : EStateX) (h : RK3 rp σ)
    (op : Val → Option Val) (hop : ∀ x y, op x = some y → y = 1#128) :
    (ERX rp tid).ok (.rmw .acqRel rp.f2 4 op) σ ∧
      ∀ old (σ' : EStateX), (ERX rp tid).step (.rmw .acqRel rp.f2 4 op) σ old σ' → RK4 rp σ' := by
  obtain ⟨⟨hrel, hF, hW⟩, hq, ts, hX, hmax, hts⟩ := h
  have hne : rp.Q.Fl ≠ rp.Q.Dt := hL.fl_dt
  have hWd : rp.Q.W ≠ rp.Q.Dt := hL.wd
  refine ⟨⟨⟨hF, fun c g tr old new _ _ hon => ?_⟩, by simp [SharedEnv.AccessIn]⟩, ?_⟩
  · obtain rfl := hop _ _ hon
    refine ⟨fun hr => by simp [mpPlan] at hr, fun _ => ⟨by decide, ?_, ?_, fun _ hwb => ?_⟩⟩
    · rw [hrel]; exact flag43_impure (by decide)
    · simp [mpPlan, hne]
    · have hlt := hwb.rel rfl
      rw [hrel]
      refine fun _ => ⟨by simp [mpPlan, hq], ts, by simpa [mpPlan] using hX,
        fun p hp => hmax p (by simpa [mpPlan] using hp), ?_⟩
      simp only [Time, View] at *; omega
  · intro old σ' hs
    obtain ⟨c, tr, -, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsTCX (I := isa) (A := Arch.tso)
      (pl := mpPlan rp.Q) hs
    unfold RK4
    rcases hbr with ⟨-, -, hr⟩ | ⟨new, tw, hon, -, -, -, -, -, -, -, ⟨_, -, hr⟩, -⟩
    · rw [hr]; exact hW
    · obtain rfl := hop _ _ hon
      rw [hr]
      refine Rat.le_trans ?_ (Res.op_wr_q_ge _ _ _ ((Res.prod _).wr _).nonneg)
      simp [mpPlan, hWd, hW]

/-! ## The reader's predicates -/

/-- **A usable acquire predicate for `f2`** (`OkPred` at `flag43`). -/
def OkPred43 (Q : Params) (c : Config isa) (ψ : Pred) : Prop :=
  ∀ v m V R, ψ.P v m V R → BitVec.setWidth 32 v ≠ 0 →
    Good43 Q.Dt V R ∨ ∃ v0, c.mem.read? Q.Fl V = some v0 ∧ BitVec.setWidth 32 v0 = 0

theorem OkPred43.snap {Q : Params} {tid : Nat} {c c' : Config isa} {ψ : Pred} (h : OkPred43 Q c ψ)
    (hs : SnapLe tid c c') : OkPred43 Q c' ψ := fun v m V R hP hv =>
  (h v m V R hP hv).imp id fun ⟨v0, hr, h0⟩ => ⟨v0, hs.read? hr, h0⟩

theorem OkPred43.flag {Q : Params} {c : Config isa} : OkPred43 Q c (flag43 Q.Dt) := fun _ _ _ _ hP hv => .inl (hP hv)

/-- Before the flag load (the reader's loop invariant): `f2`'s release
predicate `flag43`, no forwarding item for `f2`, and an acquire id of `f2`
with a usable predicate. -/
def DK1 (Q : Params) (σ : EStateX) : Prop :=
  σ.g.rel Q.Fl = flag43 Q.Dt ∧ σ.vs.getFwd Q.Fl = none ∧
    ∃ ι, ι < σ.g.acqTab.length ∧ 1 ≤ σ.r.acq Q.Fl ι ∧ OkPred43 Q σ.snap (σ.g.acqPred ι)

/-- After the take: all of `Dt`, maximal write `(43, ts)`, `ts ≤ vrNew`. -/
def DK2 (Q : Params) (σ : EStateX) : Prop :=
  (σ.r.wr Q.Dt).q = 1 ∧ ∃ ts, (σ.r.wr Q.Dt).X (43#128, ts) ∧ (∀ p, (σ.r.wr Q.Dt).X p → p.2 ≤ ts) ∧
    ts ≤ σ.vs.vrNew

theorem DK1.fence {Q : Params} {σ σ' : EStateX} (h : DK1 Q σ) (hf : FenceLe σ σ') : DK1 Q σ' := by
  unfold DK1; rw [hf.g, hf.r, hf.getFwd, hf.snap]; exact h

theorem DK2.fence {Q : Params} {σ σ' : EStateX} (h : DK2 Q σ) (hf : FenceLe σ σ') : DK2 Q σ' := by
  obtain ⟨hq, ts, hX, hmax, hts⟩ := h
  exact ⟨by rw [hf.r]; exact hq, ts, by rw [hf.r]; exact hX, fun p hp => hmax p (by rw [← hf.r]; exact hp),
    Nat.le_trans hts hf.vrNew⟩

/-- The reader's environment: the x64 take route's `ETX` (`EnvGTX`, empty plan) on
`f2`'s MP layout. -/
abbrev EDX (Q : Params) (tid : Nat) : SharedEnv := ETX Q tid

/-! ## The reader's VCs -/

/-- **VC D1** (`movl (%rdi), %eax` on `EnvGTX`): a zero flag keeps the loop
invariant, a non-zero flag takes all of `Dt` with maximal write `43`. -/
theorem vc_d1 {Q : Params} (tid : Nat) (σ : EStateX) (h : DK1 Q σ) :
    ∀ v (σ' : EStateX), (EDX Q tid).step (.load .plain false Q.f 4) σ v σ' →
      (BitVec.setWidth 32 v = 0 → DK1 Q σ') ∧ (BitVec.setWidth 32 v ≠ 0 → DK2 Q σ') := by
  intro v σ' hs
  obtain ⟨ga, hanc, ⟨rF, E⟩, -, tr, hrd, hlv, a, ha, hr, hg, -⟩ := step_loadFactsT (pl := rdPlanX) hs
  obtain ⟨hrel, hfw, ι, hlt, hacq1, hok⟩ := h
  have hn := hanc.lt
  have hacq : σ.r.acq Q.Fl ι = 1 := Nat.le_antisymm (E.thread_acq_le hn _ _) hacq1
  have hc : TakeCond Arch.tso .plain σ.vs Q.Fl tr := ⟨by decide, not_fwded_of_none hfw⟩
  have ha' : a = takeAll Q.Fl tr σ.r ga := ha.1 hc
  have hrel' : σ'.g.rel = σ.g.rel := by rw [hg, (ha.ghost_le).rel, hanc.rel]
  have hok' : OkPred43 Q σ'.snap (ga.acqPred ι) := by rw [hanc.acqPred hlt]; exact hok.snap hanc.snap
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨ι', h1, h2, hp⟩ := takeAll_held (l := Q.Fl) (tr := tr) (r := σ.r) (g := ga) hacq1 (hanc.acqLen hlt)
    refine ⟨by rw [hrel']; exact hrel, by rw [hlv.getFwd]; exact hfw, ι',
      by rw [hg, ha']; exact h2, by rw [hr, ha']; exact h1, ?_⟩
    rw [hg, ha']
    rcases hp with hp | hp
    · rw [hp]; exact hok'
    · rw [hp]
      intro v' m V R hP hv'
      rcases hP with ⟨rfl, -⟩ | hP
      · exact .inr ⟨v, hrd.val, hv⟩
      · exact hok' v' m V R hP hv'
  · obtain ⟨s, hs, hkey, hid, hP⟩ := SLR.EnvG.slot_of_seen (k := (Q.Fl, tr)) E hn hacq hrd.val
      (by rw [hanc.rel, hrel]; exact flag43_impure hv)
    obtain ⟨hq, ts, hX, hmax, hts⟩ : Good43 Q.Dt tr s.res := by
      rcases hok' v _ tr s.res hP hv with hG | ⟨v0, hr0, h0⟩
      · exact hG
      · rw [hrd.val] at hr0; cases hr0; exact absurd h0 hv
    obtain ⟨hq', hX'⟩ := takeAll_wr_full hn E hs hkey (by rw [hid]; exact hacq) hq
    have hvr : tr ≤ σ'.vs.vrNew := (hlv.acq (by decide) (not_fwded_of_none hfw)).1
    refine ⟨by rw [hr, ha']; exact hq', ts, by rw [hr, ha']; exact (hX' _).mpr hX, fun p hp => ?_,
      Nat.le_trans hts hvr⟩
    rw [hr, ha'] at hp
    exact hmax p ((hX' p).mp hp)

/-- **VC D2** (`movl (%rsi), %ebx`, an acquire under `Arch.tso` that may
take): the reader keeps `Own43` (`takeEff_wr_full`), and under the clean flag
the load returns `43`. -/
theorem vc_d2 {Q : Params} (tid : Nat) (σ : EStateX) (h : DK2 Q σ) :
    ∀ v (σ' : EStateX), (EDX Q tid).step (.load .plain false Q.d 4) σ v σ' →
      Own43 Q σ'.r ∧ (σ'.cl → v = 43#128) := by
  intro v σ' hs
  obtain ⟨ga, hanc, ⟨rF₀, E₀⟩, hcl, tr, hrd, -, a, ha, hr, -⟩ := step_loadFactsT (pl := rdPlanX) hs
  obtain ⟨hq, ts, hX, hmax, hts⟩ := h
  obtain ⟨hq', hX'⟩ := takeEff_wr_full hanc.lt E₀ ha hq
  refine ⟨⟨by rw [hr]; exact hq', ts, by rw [hr, hX']; exact hX, fun p hp => hmax p (by rw [hr, hX'] at hp; exact hp)⟩,
    fun hc => ?_⟩
  rw [hcl] at hc
  obtain ⟨-, rF, E'⟩ := hc
  obtain ⟨t, ht⟩ : ∃ t, σ'.snap.threads[tid]? = some t :=
    ⟨σ'.snap.threads[tid]'hanc.lt, Array.getElem?_eq_getElem hanc.lt⟩
  have hp : t.prom.contains tr = false := by
    have := hrd.notOwn
    simp only [ownProm, ht, Option.map_some, Option.getD_some] at this
    exact this
  exact (read_max E' ht hq hX hmax hrd.val hp hrd.window (Nat.le_trans hts (le_readBound_vrNew _ _ _ _))).2

end Kraken.Promising.X64.EnvG.RelayX

#print axioms Kraken.Promising.X64.EnvG.RelayX.vc_r1
#print axioms Kraken.Promising.X64.EnvG.RelayX.vc_r2
#print axioms Kraken.Promising.X64.EnvG.RelayX.vc_r3
#print axioms Kraken.Promising.X64.EnvG.RelayX.vc_d1
#print axioms Kraken.Promising.X64.EnvG.RelayX.vc_d2
