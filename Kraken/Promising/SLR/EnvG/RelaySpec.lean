/-
**Part 1: a three-thread ownership relay — the
programs, predicates and VCs** (on `EnvGT`, `EnvG/TakeEnv.lean`).

Three threads hand the data word `Dt = ⟨d, 4⟩` along:
- **writer** (thread `0`): MP's `mpWriter` (`str` data `:= 1`, then `stlr`
  `f1 := 1`, releasing all of `Dt` to the slot of the relay's acquire id);
- **relay** (thread `1`, `relay` below): spins on `ldar f1`, **takes** `Dt`
  (as `takeReader`), stores `43` to it, and releases it with
  `stlr f2 := 1` (plan `mpPlan Q`: `F2 := 1` gives `[Dt]`, a store release);
- **reader** (thread `2`): MP's `mpReader` text (`spin: ldar; cbz; ldr`) on
  `f2`, run on `EnvGT`: it **takes** `Dt` at its acquire load, then reads
  `43` from its own resource.

The release of the relay is a *store* (`stlr`). The briefed `swpl` (a
release-only RMW) is not provable on phase-1 EnvG: `RmwOk`'s claim condition
and `RelRmwGiveOk` quantify over arbitrary anchor/erasure ghosts, where an
`f2` message may carry update slots (`KNOWN_GAPS.md`). The explorer
checks the `swpl` program too (`mp_relay3_swpl.kl`).

**Parameters**: `RP` (`f1`, `f2`, `d` and the tokens `W`, `W2`), seen as two
MP parameter sets sharing `d`: `rp.P = ⟨f1, d, W⟩` (the writer's flag, with
MP's `flagPred` releasing `Good` at value `1`) and `rp.Q = ⟨f2, d, W2⟩` (the
relay's flag, with `flag43`, releasing `Good43` at value `43`).

**The VCs**:
- relay, `ldar w3, [x0]`: `vc_r1` (TakeMp's `vc_k1`, plus the relay's world
  `RW`: `f2`'s release predicate, a share of `f2`, the token `W2`);
- relay, `str w5, [x1]` (`43`): `vc_r2`, all of `Dt` with maximal write
  `(43, tw)`, `tw ≤ vwOld`;
- relay, `stlr w6, [x2]` (`1`): `vc_r3`, the planned release (`RelOb`:
  `flag43` of all of `Dt`), keeping `W2`;
- reader, `ldar w3, [x0]`: `vc_d1` (spurious takes as `vc_k1`; a non-zero
  flag takes all of `Dt` with maximal write `(43, ts)`, `ts ≤ vrNew`);
- reader, `ldr w4, [x1]`: `vc_d2` (`read_max` on its own resource).

Phase-1 limits (single-access trees, read-side acquire only, releases are
stores, takes only at non-forwarded acquire loads) apply; none is binding.
-/
import Kraken.Promising.SLR.EnvG.TakeMp

namespace Kraken.Promising.SLR.EnvG.Relay

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp Kraken.Promising.SLR.EnvG.MpSmoke

/-! ## The relay program -/

/-- **The relay**: spin on an acquire load of `f1` (`X0`) until non-zero,
store `43` to the data (`X1`), release `f2` (`X2`) with `stlr`. -/
def relay : Program := parseAArch64("
spin:
    ldar w3, [x0]
    cbz w3, spin
    mov w5, #43
    str w5, [x1]
    mov w6, #1
    stlr w6, [x2]
done_y:
")

/-- info: 8 -/
#guard_msgs in
#eval relay.length

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

/-! ## The relay's flag predicate -/

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

/-! ## Takes only add -/

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
def RW (Q : Params) (σ : State isa) : Prop :=
  σ.g.rel Q.Fl = flag43 Q.Dt ∧ 0 < (σ.r.wr Q.Fl).q ∧ 1 ≤ (σ.r.wr Q.W).q

/-- Before `ldar w3, [x0]` (the loop invariant): TakeMp's `K1` on `f1`, and
the relay's world. -/
def RK1 (rp : RP) (σ : State isa) : Prop := K1 rp.P σ ∧ RW rp.Q σ

/-- After the take: TakeMp's `K2`, and the relay's world. -/
def RK2 (rp : RP) (σ : State isa) : Prop := K2 rp.P σ ∧ RW rp.Q σ

/-- After `str w5, [x1]`: the world, all of `Dt` with maximal write
`(43, tw)`, `tw ≤ vwOld`. -/
def RK3 (rp : RP) (σ : State isa) : Prop :=
  RW rp.Q σ ∧ (σ.r.wr rp.Q.Dt).q = 1 ∧
    ∃ tw, (σ.r.wr rp.Q.Dt).X (43#128, tw) ∧ (∀ p, (σ.r.wr rp.Q.Dt).X p → p.2 ≤ tw) ∧ tw ≤ σ.vs.vwOld

/-- At the end: the token `W2`. -/
def RK4 (rp : RP) (σ : State isa) : Prop := 1 ≤ (σ.r.wr rp.Q.W).q

theorem RK1.fence {rp : RP} {σ σ' : State isa} (h : RK1 rp σ) (hf : FenceLe σ σ') : RK1 rp σ' :=
  ⟨h.1.fence hf, by unfold RW; rw [hf.g, hf.r]; exact h.2⟩

theorem RK2.fence {rp : RP} {σ σ' : State isa} (h : RK2 rp σ) (hf : FenceLe σ σ') : RK2 rp σ' :=
  ⟨h.1.fence hf, by unfold RW; rw [hf.g, hf.r]; exact h.2⟩

theorem RK3.fence {rp : RP} {σ σ' : State isa} (h : RK3 rp σ) (hf : FenceLe σ σ') : RK3 rp σ' := by
  unfold RK3 RW; rw [hf.g, hf.r, hf.vs]; exact h

theorem RK4.fence {rp : RP} {σ σ' : State isa} (h : RK4 rp σ) (hf : FenceLe σ σ') : RK4 rp σ' := by
  unfold RK4; rw [hf.r]; exact h

/-- The relay's environment: taking loads, the plan `F2 := 1` gives `[Dt]`. -/
abbrev ER (rp : RP) (tid : Nat) : SharedEnv := EnvGT isa Arch.armv8 tid (mpPlan rp.Q)

/-! ## The relay's VCs -/

/-- **VC R1** (`ldar w3, [x0]`): a zero flag keeps `RK1`, a non-zero flag
takes all of `Dt` (`RK2`). -/
theorem vc_r1 {rp : RP} (tid : Nat) (σ : State isa) (h : RK1 rp σ) :
    ∀ v (σ' : State isa), (ER rp tid).step (.load .acq false rp.f1 4) σ v σ' →
      (BitVec.setWidth 32 v = 0 → RK1 rp σ') ∧ (BitVec.setWidth 32 v ≠ 0 → RK2 rp σ') := by
  intro v σ' hs
  have hk := vc_k1 (P := rp.P) tid σ h.1 v σ' hs
  obtain ⟨ga, hanc, -, -, tr, -, -, a, ha, hr, hg, -⟩ := step_loadFactsT hs
  obtain ⟨hrel, hF, hW⟩ := h.2
  have hrel' : σ'.g.rel = σ.g.rel := by rw [hg, (ha.ghost_le).rel, hanc.rel]
  have hw : RW rp.Q σ' := ⟨by rw [hrel']; exact hrel, by rw [hr]; have := takeEff_wr_q_ge ha rp.Q.Fl; grind,
    by rw [hr]; have := takeEff_wr_q_ge ha rp.Q.W; grind⟩
  exact ⟨fun h0 => ⟨hk.1 h0, hw⟩, fun h0 => ⟨hk.2 h0, hw⟩⟩

/-- **VC R2** (`str w5, [x1]`, `w5 = 43`): the plain store is permitted and
gives `RK3`. -/
theorem vc_r2 {rp : RP} (hL : MpLocs rp.Q) (tid : Nat) (σ : State isa) (h : RK2 rp σ) :
    (ER rp tid).ok (.store .plain false rp.d 4 43#128) σ ∧
      ∀ b (σ' : State isa), (ER rp tid).step (.store .plain false rp.d 4 43#128) σ b σ' → RK3 rp σ' := by
  obtain ⟨⟨hpure, hq, hmax⟩, hrel, hF, hW⟩ := h
  have hne : rp.Q.Fl ≠ rp.Q.Dt := hL.fl_dt
  refine ⟨⟨rfl, by rw [hq]; decide, fun _ => hpure _, fun hr => by simp [mpPlan, hne] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, -, hwb, hwv, -, ⟨Q, -, hr⟩, -⟩ := step_storeFactsT hs
  have hr' : σ'.r = σ.r.addW rp.Q.Dt (43#128, tw) := by simpa [mpPlan, hne] using hr
  refine ⟨⟨by rw [hanc.rel]; exact hrel, by rw [hr', Res.addW_q]; exact hF, by rw [hr', Res.addW_q]; exact hW⟩,
    by rw [hr', Res.addW_q]; exact hq, tw, ?_, fun p hp => ?_, hwv.vwOld (by simp)⟩
  · rw [hr', Res.addW_X_self, hq]; exact .inr ⟨by decide, rfl⟩
  · rw [hr', Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hmax p hp) hwb.vwNew)
    · exact Nat.le_refl _

/-- **VC R3** (`stlr w6, [x2]`, `w6 = 1`): the planned release is permitted
(`effRel`, impure value, `F2` kept, and the obligation: `flag43` of all of
`Dt` at every anchor and fresh `tw`), and every outcome keeps `W2`. -/
theorem vc_r3 {rp : RP} (hL : MpLocs rp.Q) (tid : Nat) (σ : State isa) (h : RK3 rp σ) :
    (ER rp tid).ok (.store .rel false rp.f2 4 1#128) σ ∧
      ∀ b (σ' : State isa), (ER rp tid).step (.store .rel false rp.f2 4 1#128) σ b σ' → RK4 rp σ' := by
  obtain ⟨⟨hrel, hF, hW⟩, hq, ts, hX, hmax, hts⟩ := h
  have hne : rp.Q.Fl ≠ rp.Q.Dt := hL.fl_dt
  have hWd : rp.Q.W ≠ rp.Q.Dt := hL.wd
  refine ⟨⟨rfl, hF, fun hr => by simp [mpPlan] at hr, fun _ => ⟨effRel_rel _ _, ?_, ?_, ?_⟩⟩, ?_⟩
  · rw [hrel]; exact flag43_impure (by decide)
  · simp [mpPlan, hne]
  · intro c g _ hwb
    have hlt := hwb.rel rfl
    rw [hrel]
    refine fun _ => ⟨by simp [mpPlan, hq], ts, by simpa [mpPlan] using hX, fun p hp => hmax p (by simpa [mpPlan] using hp), ?_⟩
    simp only [Time, View] at *; omega
  · intro b σ' hs
    obtain ⟨c, tw, -, -, -, -, -, hr, -⟩ := step_storeFactsT hs
    obtain ⟨_, -, hr⟩ := hr
    unfold RK4
    rw [hr]
    simp [mpPlan, hWd, hW]

/-! ## The reader's predicates -/

/-- **A usable acquire predicate for `f2`** (`OkPred` at `flag43`): at a
non-zero value it gives `Good43`, unless its timestamp is that of a zero
`f2` message (a spurious take relaxed it). -/
def OkPred43 (Q : Params) (c : Config isa) (ψ : Pred) : Prop :=
  ∀ v m V R, ψ.P v m V R → BitVec.setWidth 32 v ≠ 0 →
    Good43 Q.Dt V R ∨ ∃ v0, c.mem.read? Q.Fl V = some v0 ∧ BitVec.setWidth 32 v0 = 0

theorem OkPred43.snap {Q : Params} {tid : Nat} {c c' : Config isa} {ψ : Pred} (h : OkPred43 Q c ψ)
    (hs : SnapLe tid c c') : OkPred43 Q c' ψ := fun v m V R hP hv =>
  (h v m V R hP hv).imp id fun ⟨v0, hr, h0⟩ => ⟨v0, hs.read? hr, h0⟩

theorem OkPred43.flag {Q : Params} {c : Config isa} : OkPred43 Q c (flag43 Q.Dt) := fun _ _ _ _ hP hv => .inl (hP hv)

/-- Before `ldar w3, [x0]` (the reader's loop invariant): `f2`'s release
predicate `flag43`, no forwarding item for `f2`, and an acquire id of `f2`
with a usable predicate. -/
def DK1 (Q : Params) (σ : State isa) : Prop :=
  σ.g.rel Q.Fl = flag43 Q.Dt ∧ σ.vs.getFwd Q.Fl = none ∧
    ∃ ι, ι < σ.g.acqTab.length ∧ 1 ≤ σ.r.acq Q.Fl ι ∧ OkPred43 Q σ.snap (σ.g.acqPred ι)

/-- After the take: all of `Dt`, maximal write `(43, ts)`, `ts ≤ vrNew`. -/
def DK2 (Q : Params) (σ : State isa) : Prop :=
  (σ.r.wr Q.Dt).q = 1 ∧ ∃ ts, (σ.r.wr Q.Dt).X (43#128, ts) ∧ (∀ p, (σ.r.wr Q.Dt).X p → p.2 ≤ ts) ∧
    ts ≤ σ.vs.vrNew

theorem DK2.own43 {Q : Params} {σ : State isa} (h : DK2 Q σ) : Own43 Q σ.r :=
  ⟨h.1, h.2.elim fun ts h => ⟨ts, h.1, h.2.1⟩⟩

theorem DK1.fence {Q : Params} {σ σ' : State isa} (h : DK1 Q σ) (hf : FenceLe σ σ') : DK1 Q σ' := by
  unfold DK1; rw [hf.g, hf.r, hf.getFwd, hf.snap]; exact h

theorem DK2.fence {Q : Params} {σ σ' : State isa} (h : DK2 Q σ) (hf : FenceLe σ σ') : DK2 Q σ' := by
  obtain ⟨hq, ts, hX, hmax, hts⟩ := h
  exact ⟨by rw [hf.r]; exact hq, ts, by rw [hf.r]; exact hX, fun p hp => hmax p (by rw [← hf.r]; exact hp),
    Nat.le_trans hts hf.vrNew⟩

/-! ## The reader's VCs -/

/-- **VC D1** (`ldar w3, [x0]` on `EnvGT`): a zero flag keeps the loop
invariant, a non-zero flag takes all of `Dt` with maximal write `43`. -/
theorem vc_d1 {Q : Params} (tid : Nat) (σ : State isa) (h : DK1 Q σ) :
    ∀ v (σ' : State isa), (ET tid).step (.load .acq false Q.f 4) σ v σ' →
      (BitVec.setWidth 32 v = 0 → DK1 Q σ') ∧ (BitVec.setWidth 32 v ≠ 0 → DK2 Q σ') := by
  intro v σ' hs
  obtain ⟨ga, hanc, ⟨rF, E⟩, -, tr, hrd, hlv, a, ha, hr, hg, -⟩ := step_loadFactsT hs
  obtain ⟨hrel, hfw, ι, hlt, hacq1, hok⟩ := h
  have hn := hanc.lt
  have hacq : σ.r.acq Q.Fl ι = 1 := Nat.le_antisymm (E.thread_acq_le hn _ _) hacq1
  have hc : TakeCond Arch.armv8 .acq σ.vs Q.Fl tr := ⟨by decide, not_fwded_of_none hfw⟩
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
  · obtain ⟨s, hs, hkey, hid, hP⟩ := slot_of_seen (k := (Q.Fl, tr)) E hn hacq hrd.val
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

/-- **VC D2** (`ldr w4, [x1]`): the reader keeps `Own43`, and under the
clean flag the load returns `43`. -/
theorem vc_d2 {Q : Params} (tid : Nat) (σ : State isa) (h : DK2 Q σ) :
    ∀ v (σ' : State isa), (ET tid).step (.load .plain false Q.d 4) σ v σ' →
      Own43 Q σ'.r ∧ (σ'.cl → v = 43#128) := by
  intro v σ' hs
  obtain ⟨ga, hanc, -, hcl, tr, hrd, -, a, ha, hr, -⟩ := step_loadFactsT hs
  obtain rfl := takeEff_of_not_acq ha (by decide)
  simp only at hr
  refine ⟨by rw [hr]; exact h.own43, fun hc => ?_⟩
  rw [hcl] at hc
  obtain ⟨-, rF, E'⟩ := hc
  obtain ⟨hq, ts, hX, hmax, hts⟩ := h
  obtain ⟨t, ht⟩ : ∃ t, σ'.snap.threads[tid]? = some t :=
    ⟨σ'.snap.threads[tid]'hanc.lt, Array.getElem?_eq_getElem hanc.lt⟩
  have hp : t.prom.contains tr = false := by
    have := hrd.notOwn
    simp only [ownProm, ht, Option.map_some, Option.getD_some] at this
    exact this
  exact (read_max E' ht hq hX hmax hrd.val hp hrd.window (Nat.le_trans hts (le_readBound_vrNew _ _ _ _))).2

#print axioms vc_r1
#print axioms vc_r2
#print axioms vc_r3
#print axioms vc_d1
#print axioms vc_d2

end Kraken.Promising.SLR.EnvG.Relay
