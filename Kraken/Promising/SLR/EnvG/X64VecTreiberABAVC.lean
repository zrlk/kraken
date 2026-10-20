/-
**`treiber_aba_tagged.kl`, part 2: the per-access
verification conditions** on `EnvGCAdj isa Arch.tso w plan0`
(`X64VecTreiberABAGhost.lean`).

The program's shared accesses are the 16-byte `movdqa (head)` load
(`.load .plain false h 16`), the node loads `movq (%rax),%rbx`
(`.load .plain false p 8`), thread `1`'s node store `movq %rax,(%r12)`
(`.store .plain false p 8 v`) and `lock cmpxchg16b (head)`
(`.rmw .acqRel h 16 (cas16 acc new)`). With no release predicate and the
empty plan their permissions are positive fractions and `Pred.emp` purity
(`st_ok`, `cas_ok`); the step lemmas (`ld_step`, `st_step`, `cas_step`)
expose what the table predicates of `X64VecTreiberABARun.lean` need:

- `Tr σ σ'`: the snapshot memory grows, `coh`, `vrNew` and `vwOld` grow, the
  release predicates stay `Pred.emp` (every step, `Tr.*`);
- `Com P w σ`: the ghost facts, thread `w`'s fractions (`head ≥ ½`, its token,
  for thread `1` every 8-byte location), the initial values of `head`, `A.next`
  and `B.next`, and `FwdC`: every forwarding item is at or below `coh` of
  its location, and `head`'s at or below `vrNew` (TSO's `lock` RMW is a
  fence);
- a read of `head` or of a node is at or below `coh` afterwards (forwarded
  or not, by `FwdC`); a read of `head` also at or below `vrNew`;
- the `cmpxchg16b` read is at or above every own earlier write of `head`
  (its window covers `coh`), its write is fresh-above `coh`, and atomic.

Write-set exactness (`ExH`, `ExN`): while a thread's fraction of `head` is
exactly `½` (of an 8-byte location exactly `1`), its write set there is the
initial message and the writes the thread made (`ExH.cas`, `ExN.cas`,
`ExN.store`); a claimed slot can only add to the fraction.
-/
import Kraken.Promising.SLR.EnvG.X64VecTreiberABAGhost
import Kraken.Promising.SLR.EnvG.X64Treiber2VC
import Kraken.Promising.SLR.EnvG.LockVC

namespace Kraken.Promising.X64.EnvG.VecABA

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read? initVal_eq read?_mono read?_le_last
  prefix_append get?_of_anchor envGC_rmw_fail_getFwd)
open Kraken.Promising.SLR.SpinCommon (readSuccs_fwdb fenceOptCtx_getFwd rmwAfter_getFwd)

/-- `omega` on `Time`/`View` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- Thread `w`'s environment. -/
noncomputable abbrev EW (w : Nat) : SharedEnv := EnvGCAdj isa Arch.tso w plan0

/-! ## Values -/

/-- The low 64 bits of a 16-byte value (`head`'s pointer). -/
abbrev lo (v : Val) : BitVec 64 := v.extractLsb' 0 64

/-- The high 64 bits of a 16-byte value (`head`'s tag). -/
abbrev hi (v : Val) : BitVec 64 := v.extractLsb' 64 64

/-- `lock cmpxchg16b`'s operation with accumulator `acc` (`rdx:rax`) and
replacement `new` (`rcx:rbx`). -/
def cas16 (acc new : BitVec 128) : Val → Option Val := fun old => if old == acc then some new else none

theorem cas16_some {acc new old new' : BitVec 128} (h : cas16 acc new old = some new') : old = acc ∧ new' = new := by
  unfold cas16 at h
  split at h
  · rename_i hb; exact ⟨by simpa using hb, (Option.some.inj h).symm⟩
  · cases h

theorem cas16_none {acc new old : BitVec 128} (h : cas16 acc new old = none) : old ≠ acc := by
  unfold cas16 at h
  split at h
  · cases h
  · rename_i hb; simpa using hb

theorem hi_lo (v : Val) : hi v ++ lo v = v := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split
  · simp [BitVec.getLsbD_eq_getElem hi]
  · rw [BitVec.getLsbD_eq_getElem (by omega)]; congr 1; omega

/-! ## What every step keeps -/

/-- **What every step keeps**: the snapshot memory grows, `coh`, `vrNew` and
`vwOld` grow, the release predicates are unchanged. -/
structure Tr (σ σ' : EStateX) : Prop where
  pre : σ.snap.mem.Prefix σ'.snap.mem
  coh : ∀ x, σ.vs.getCoh x ≤ σ'.vs.getCoh x
  vr : σ.vs.vrNew ≤ σ'.vs.vrNew
  rel : σ'.g.rel = σ.g.rel
  vw : σ.vs.vwOld ≤ σ'.vs.vwOld

theorem Tr.refl (σ : EStateX) : Tr σ σ :=
  ⟨Memory.Prefix.refl _, fun _ => Nat.le_refl _, Nat.le_refl _, rfl, Nat.le_refl _⟩

theorem Tr.trans {σ₁ σ₂ σ₃ : EStateX} (h₁ : Tr σ₁ σ₂) (h₂ : Tr σ₂ σ₃) : Tr σ₁ σ₃ :=
  ⟨h₁.pre.trans h₂.pre, fun x => Nat.le_trans (h₁.coh x) (h₂.coh x), Nat.le_trans h₁.vr h₂.vr, h₂.rel.trans h₁.rel,
    Nat.le_trans h₁.vw h₂.vw⟩

theorem Tr.ofFence {σ σ' : EStateX} (h : FenceLe σ σ') : Tr σ σ' :=
  ⟨by rw [h.snap]; exact Memory.Prefix.refl _, fun x => Nat.le_of_eq (h.getCoh x).symm, h.vrNew, by rw [h.g],
    by rw [h.vs]; exact Nat.le_refl _⟩

theorem Tr.initVal {σ σ' : EStateX} (h : Tr σ σ') (l : Loc) : σ'.snap.mem.initVal l = σ.snap.mem.initVal l :=
  initVal_eq h.pre.1 l

/-! ## The common facts -/

/-- The initial values: `head = {A, 0}`, `A.next = B`, `B.next = 0`. -/
def IV (P : Params) (m : Memory) : Prop :=
  m.initVal P.hd = BitVec.setWidth 128 P.a ∧ m.initVal (nd P.a) = BitVec.setWidth 128 P.b ∧
    m.initVal (nd P.b) = 0

/-- Forwarding items are at or below `coh` of their location; `head`'s at or
below `vrNew`. -/
def FwdC (P : Params) (vs : Views) : Prop :=
  (∀ x f, vs.getFwd x = some f → f.time ≤ vs.getCoh x) ∧ ∀ f, vs.getFwd P.hd = some f → f.time ≤ vs.vrNew

/-- Thread `w`'s fractions. -/
def Fr (P : Params) (w : Nat) (r : Res) : Prop :=
  1 / 2 ≤ (r.wr P.hd).q ∧
    if w = 0 then 1 ≤ (r.wr P.tok0).q else 1 ≤ (r.wr P.tok1).q ∧ ∀ x : Loc, x.bytes = 8 → 1 ≤ (r.wr x).q

/-- **The common facts** of thread `w`. -/
def Com (P : Params) (w : Nat) (σ : EStateX) : Prop :=
  σ.g.rel = ghost₀.rel ∧ Fr P w σ.r ∧ IV P σ.snap.mem ∧ FwdC P σ.vs

/-- Fractions only grow. -/
def QGe (r r' : Res) : Prop := ∀ x, (r.wr x).q ≤ (r'.wr x).q

theorem Fr.mono {P : Params} {w : Nat} {r r' : Res} (h : Fr P w r) (hq : QGe r r') : Fr P w r' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨Rat.le_trans h1 (hq _), ?_⟩
  split
  · rename_i hw; simp only [hw, ↓reduceIte] at h2; exact Rat.le_trans h2 (hq _)
  · rename_i hw; simp only [hw, ↓reduceIte] at h2
    exact ⟨Rat.le_trans h2.1 (hq _), fun x hx => Rat.le_trans (h2.2 x hx) (hq _)⟩

theorem QGe.addW (r : Res) (l : Loc) (p : Val × Time) : QGe r (r.addW l p) := fun x => by
  rw [Res.addW_q]; exact Rat.le_refl

theorem QGe.op (r C : Res) : QGe r (r.op C) := fun _ => Perm.le_op_left _ _

theorem QGe.cas (r : Res) (l : Loc) (p : Val × Time) (C : Res) : QGe r ((r.addW l p).op C) := fun x =>
  Rat.le_trans ((QGe.addW r l p) x) ((QGe.op _ C) x)

theorem Fr.hd_pos {P : Params} {w : Nat} {r : Res} (h : Fr P w r) : 0 < (r.wr P.hd).q := by
  have := h.1; grind

theorem Fr.nd_pos {P : Params} {r : Res} (h : Fr P 1 r) (p : BitVec 64) : 0 < (r.wr (nd p)).q := by
  have := h.2; simp only [Nat.one_ne_zero, ↓reduceIte] at this
  have := this.2 (nd p) rfl; grind

theorem Fr.nd_ge {P : Params} {r : Res} (h : Fr P 1 r) {x : Loc} (hx : x.bytes = 8) : 1 ≤ (r.wr x).q := by
  have := h.2; simp only [Nat.one_ne_zero, ↓reduceIte] at this
  exact this.2 _ hx

theorem Com.pure {P : Params} {w : Nat} {σ : EStateX} (h : Com P w σ) (l : Loc) (v : Val) :
    Pred.Pure (σ.g.rel l) v := by
  rw [h.1]; exact Pred.emp_pure _

/-! ## Permissions -/

/-- **The node store's permission** (thread `1`, any 8-byte location). -/
theorem st_ok {P : Params} {σ : EStateX} (h : Com P 1 σ) (p : BitVec 64) (v : Val) :
    (EW 1).ok (.store .plain false p 8 v) σ :=
  ⟨rfl, h.2.1.nd_pos p, fun _ => h.pure _ _, fun hr => by simp [plan0, Plan.rel, Plan.find?] at hr⟩

/-- **`lock cmpxchg16b (head)`'s permission.** -/
theorem cas_ok {P : Params} {w : Nat} {σ : EStateX} (h : Com P w σ) (op : Val → Option Val) :
    (EW w).ok (.rmw .acqRel P.h 16 op) σ :=
  ⟨h.2.1.hd_pos, fun _ _ _ _ _ _ _ _ => ⟨fun _ => h.pure _ _, fun hr => by simp [plan0, Plan.rel, Plan.find?] at hr⟩⟩

/-! ## Loads -/

/-- **A plain load** (an acquire under `Arch.tso`): the common facts are
kept, the resource unchanged; the read is at or below `coh` afterwards, and
for `head` at or below `vrNew`. -/
theorem ld_step {P : Params} {w : Nat} {σ σ' : EStateX} (hc : Com P w σ) {xcl : Bool} {a : BitVec 64} {n : Nat}
    {v : Val} (hs : (EW w).step (.load .plain xcl a n) σ v σ') :
    Com P w σ' ∧ Tr σ σ' ∧ σ'.r = σ.r ∧ ∃ tr, ReadAt Arch.tso w σ.vs σ'.snap .plain ⟨a, n⟩ tr v ∧
      tr ≤ σ'.vs.getCoh ⟨a, n⟩ ∧ (⟨a, n⟩ = P.hd → tr ≤ σ'.vs.vrNew) := by
  have hf := step_loadFacts (pl := plan0) hs
  obtain ⟨hanc, hr, -, tr, hrd, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, ⟨h4, h5⟩⟩ := hc
  have htr : Tr σ σ' := ⟨TreiberCommon.AnchorOk.prefix hanc, hlv.mono.coh, hlv.mono.vrNew, hanc.ghost.rel,
    hlv.mono.vwOld⟩
  refine ⟨⟨htr.rel.trans h1, hr ▸ h2, ?_, fun x f hf => ?_, fun f hf => ?_⟩, htr, hr, tr, hrd, ?_, fun he => ?_⟩
  · unfold IV; rw [htr.initVal, htr.initVal, htr.initVal]; exact h3
  · rw [hlv.getFwd] at hf; exact Nat.le_trans (h4 x f hf) (hlv.mono.coh x)
  · rw [hlv.getFwd] at hf; exact Nat.le_trans (h5 f hf) hlv.mono.vrNew
  · by_cases hfw : Fwded σ.vs ⟨a, n⟩ tr
    · obtain ⟨f, hf, rfl⟩ := hfw
      exact Nat.le_trans (h4 _ f hf) (hlv.mono.coh _)
    · exact hlv.coh hfw
  · by_cases hfw : Fwded σ.vs ⟨a, n⟩ tr
    · obtain ⟨f, hf, rfl⟩ := hfw
      rw [he] at hf
      exact Nat.le_trans (h5 f hf) hlv.mono.vrNew
    · exact (hlv.acq (by decide) hfw).1

/-! ## The node store -/

/-- **The node store** of thread `1` to `⟨p, 8⟩`: the common facts are kept;
the write `tw` is the location's new maximum, above the old `coh`, and joins
the write set. -/
theorem st_step {P : Params} {σ σ' : EStateX} (hc : Com P 1 σ) {p : BitVec 64} {v : Val} {b : Bool}
    (hs : (EW 1).step (.store .plain false p 8 v) σ b σ') :
    Com P 1 σ' ∧ Tr σ σ' ∧ ∃ tw, σ'.r = σ.r.addW (nd p) (v, tw) ∧ σ'.snap.mem.get? tw = some ⟨nd p, v, 1⟩ ∧
      σ.vs.getCoh (nd p) < tw ∧ tw ≤ σ'.vs.getCoh (nd p) ∧ tw ≤ σ'.vs.vwOld := by
  obtain ⟨c, tw, hanc, hws, hwb, hwv, -, ⟨_, -, hr⟩, -, -⟩ := step_storeFacts (pl := plan0) hs
  rw [plan0_after] at hr
  obtain ⟨h1, h2, h3, ⟨h4, h5⟩⟩ := hc
  have htr : Tr σ σ' := ⟨(TreiberCommon.AnchorOk.prefix hanc).trans (TreiberCommon.WriteSnap.prefix hws), hwv.mono.coh,
    hwv.mono.vrNew, hanc.ghost.rel, hwv.mono.vwOld⟩
  have hne : P.hd ≠ nd p := Ne.symm (nd_ne_hd P p)
  refine ⟨⟨htr.rel.trans h1, hr ▸ h2.mono (QGe.addW _ _ _), ?_, fun x f hf => ?_, fun f hf => ?_⟩, htr, tw, hr,
    TreiberCommon.WriteSnap.get?_new hws, hwb.coh, hwv.coh, hwv.vwOld (by decide)⟩
  · unfold IV; rw [htr.initVal, htr.initVal, htr.initVal]; exact h3
  · by_cases hx : x = nd p
    · subst hx
      obtain ⟨f0, hf0, ht0⟩ := hwv.fwd
      have e : (⟨p, 8⟩ : Loc) = nd p := rfl
      rw [e] at hf0
      rw [hf0] at hf; cases hf
      rw [ht0]; exact hwv.coh
    · rw [hwv.fwdOther _ hx] at hf
      exact Nat.le_trans (h4 x f hf) (hwv.mono.coh x)
  · rw [hwv.fwdOther _ hne] at hf
    exact Nat.le_trans (h5 f hf) hwv.mono.vrNew

/-! ## `lock cmpxchg16b` -/

/-- **A successful TSO RMW's forwarding items**: the written location's is
at or below its `coh`; the others are unchanged. -/
theorem rmw_getFwd {tid : Nat} {pl : Plan} {σ σ' : EStateX} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old new : Val} (h : (EnvGC isa Arch.tso tid pl).step (.rmw .acqRel addr n op) σ old σ')
    (hop : op old = some new) (l' : Loc) (f : FwdItem) (hf : σ'.vs.getFwd l' = some f) :
    (l' = ⟨addr, n⟩ ∧ f.time ≤ σ'.vs.getCoh l') ∨ (l' ≠ ⟨addr, n⟩ ∧ σ.vs.getFwd l' = some f) := by
  obtain ⟨c, x, -, hx, -, -, -, -, -, hbr⟩ := (h : RmwOutC Arch.tso tid pl σ σ' .acqRel ⟨addr, n⟩ op old)
  rcases hbr with ⟨hon, -⟩ | ⟨new', cx', tw, -, hcx, -, -, -, -, hvs, -⟩
  · rw [hop] at hon; cases hon
  have hle3 := vle_rmwAfter Arch.tso .acqRel false ⟨addr, n⟩ cx'
  have hcoh : ∀ l, cx'.views.getCoh l ≤ σ'.vs.getCoh l := fun l => by rw [hvs]; exact hle3.coh l
  rw [hvs, rmwAfter_getFwd] at hf
  have h5 := readSuccs_fwdb Arch.tso _ hx
  have e : x.2.2.views.getFwd l' = (fenceOptCtx Arch.tso (envCtx tid σ.vs c)).views.getFwd l' := by
    simp only [Views.getFwd, h5]
  rcases (mem_writeSuccs Arch.tso tid).mp hcx with ⟨t, -, -, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · rw [afterWrite_getFwd] at hf
    by_cases hl : l' = ⟨addr, n⟩
    · subst hl
      simp only [↓reduceIte, Option.some.injEq] at hf
      subst hf
      refine .inl ⟨rfl, Nat.le_trans ?_ (hcoh _)⟩
      rw [afterWrite_getCoh]; simp only [↓reduceIte]; exact Nat.le_max_right _ _
    · rw [ite_eq_right hl, e, fenceOptCtx_getFwd] at hf
      exact .inr ⟨hl, hf⟩
  · rw [afterWrite_getFwd] at hf
    by_cases hl : l' = ⟨addr, n⟩
    · subst hl
      simp only [↓reduceIte, Option.some.injEq] at hf
      subst hf
      refine .inl ⟨rfl, Nat.le_trans ?_ (hcoh _)⟩
      rw [afterWrite_getCoh]; simp only [↓reduceIte]; exact Nat.le_max_right _ _
    · rw [ite_eq_right hl] at hf
      refine .inr ⟨hl, ?_⟩
      have hf' : x.2.2.views.getFwd l' = some f := hf
      rw [e, fenceOptCtx_getFwd] at hf'
      exact hf'

/-- Every message of `l` strictly between `tr` and `tw` is by `w`. -/
def AtomicT (m : Memory) (l : Loc) (tr tw : Time) (w : Nat) : Prop :=
  ∀ p wm, tr < p → p < tw → m.get? p = some wm → wm.loc = l → wm.tid = w

theorem AtomicT.mono {m m' : Memory} (h : m.Prefix m') {l : Loc} {tr tw : Time} {w : Nat} (htw : tw ≤ m.last + 1)
    (ha : AtomicT m l tr tw w) : AtomicT m' l tr tw w := fun p wm h1 h2 hg hl =>
  ha p wm h1 h2 (Memory.get?_of_prefix_le h.2 (by omega_t) hg) hl

/-- **`lock cmpxchg16b (head)`** of thread `w`: the read `tr` is at or above
every own write of `head` at or below `coh`; on failure the resource is
unchanged; on success the write `tw` is atomic after `tr`, above the old
`coh`, and joins the write set (with claimed slots `C`). The common facts
are kept. -/
theorem cas_step {P : Params} {w : Nat} {σ σ' : EStateX} (hc : Com P w σ) {op : Val → Option Val} {old : Val}
    (hs : (EW w).step (.rmw .acqRel P.h 16 op) σ old σ') :
    Com P w σ' ∧ Tr σ σ' ∧ ∃ tr, σ'.snap.mem.read? P.hd tr = some old ∧
      (∀ W wm, σ.snap.mem.get? W = some wm → wm.loc = P.hd → W ≤ σ.vs.getCoh P.hd → W ≤ tr) ∧
      ((op old = none ∧ σ'.r = σ.r) ∨
        (∃ new tw C, op old = some new ∧ tr < tw ∧ σ'.snap.mem.get? tw = some ⟨P.hd, new, w⟩ ∧
          AtomicT σ'.snap.mem P.hd tr tw w ∧ σ.vs.getCoh P.hd < tw ∧ tw ≤ σ'.vs.getCoh P.hd ∧
          σ'.r = (σ.r.addW P.hd (new, tw)).op C ∧ σ.vs.vwOld < tw)) := by
  have hs' := envGCAdj_step_iff.mp hs
  obtain ⟨c, tr, hanc, hrd, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  obtain ⟨h1, h2, h3, ⟨h4, h5⟩⟩ := hc
  have e : ({ addr := P.h, bytes := 16 } : Loc) = P.hd := rfl
  rw [e] at hrd
  -- the read is at or above the own writes at or below `coh`
  have hown : ∀ W wm, σ.snap.mem.get? W = some wm → wm.loc = P.hd → W ≤ σ.vs.getCoh P.hd → W ≤ tr := by
    intro W wm hg hl hW
    refine Nat.le_of_not_lt fun hlt => ?_
    have hv : VLe σ.vs (rmwReadViews Arch.tso σ.vs) := by
      unfold rmwReadViews; split
      · exact vle_fenceViews _ _
      · exact VLe.refl _
    have hB : W ≤ readBound Arch.tso (rmwReadViews Arch.tso σ.vs) (Arch.tso.rmwKind .acqRel).loadKind P.hd :=
      Nat.le_trans hW (Nat.le_trans (hv.coh _) (Nat.le_max_right _ _))
    have := (Memory.writeIn_iff _ _ _ _).mpr ⟨W, wm, hlt, hB, get?_of_anchor hanc hg, hl⟩
    rw [hrd.window] at this; cases this
  rcases hbr with ⟨hon, hsnap, hr⟩ | ⟨new, tw, hon, htrw, hat, hws, hwb, htwc, -, -, ⟨Pc, -, hr⟩, -⟩
  · have htr : Tr σ σ' := ⟨hsnap ▸ TreiberCommon.AnchorOk.prefix hanc, hvle.coh, hvle.vrNew, hanc.ghost.rel,
      hvle.vwOld⟩
    refine ⟨⟨htr.rel.trans h1, hr ▸ h2, ?_, fun x f hf => ?_, fun f hf => ?_⟩, htr, tr, by rw [hsnap]; exact hrd.val,
      hown, .inl ⟨hon, hr⟩⟩
    · unfold IV; rw [htr.initVal, htr.initVal, htr.initVal]; exact h3
    · rw [envGC_rmw_fail_getFwd hs' hon] at hf; exact Nat.le_trans (h4 x f hf) (hvle.coh x)
    · rw [envGC_rmw_fail_getFwd hs' hon] at hf; exact Nat.le_trans (h5 f hf) hvle.vrNew
  · rw [e] at hat hws hwb htwc
    rw [plan0_after] at hr
    have hpre2 := TreiberCommon.WriteSnap.prefix hws
    have htr : Tr σ σ' := ⟨(TreiberCommon.AnchorOk.prefix hanc).trans hpre2, hvle.coh, hvle.vrNew, hanc.ghost.rel,
      hvle.vwOld⟩
    refine ⟨⟨htr.rel.trans h1, hr ▸ h2.mono (QGe.cas _ _ _ _), ?_, fun x f hf => ?_, fun f hf => ?_⟩, htr, tr,
      read?_mono hpre2 hrd.val, hown, .inr ⟨new, tw, _, hon, htrw, TreiberCommon.WriteSnap.get?_new hws, ?_,
      hwb.coh, htwc, hr, by have := hwb.rel (by decide); omega_t⟩⟩
    · unfold IV; rw [htr.initVal, htr.initVal, htr.initVal]; exact h3
    · rcases rmw_getFwd hs' hon x f hf with ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · exact Nat.le_trans (h4 x f h) (hvle.coh x)
    · exact Treiber2X.rmw_success_fwd_tso hs' hon f hf
    · have hle_tw : tw ≤ c.mem.last + 1 := TreiberCommon.WriteSnap.tw_le hws
      intro p wm a b hg hl
      have hp : p ≤ c.mem.last := by omega_t
      exact atomic_between hat hrd.val a b (Memory.get?_of_prefix_le hpre2.2 hp hg) hl

/-! ## Write-set exactness -/

/-- **`head`'s write set while the fraction is `½`**: the initial message
and `S`. -/
def ExH (P : Params) (r : Res) (S : Val × Time → Prop) : Prop :=
  (r.wr P.hd).q = 1 / 2 → ∀ p, (r.wr P.hd).X p → p.2 = 0 ∨ S p

/-- **The 8-byte write sets while the fraction is `1`**: the initial message
and `N`. -/
def ExN (r : Res) (N : Loc → Time → Prop) : Prop :=
  ∀ x : Loc, x.bytes = 8 → (r.wr x).q = 1 → ∀ p, (r.wr x).X p → p.2 = 0 ∨ N x p.2

theorem ExH.mono {P : Params} {r : Res} {S S' : Val × Time → Prop} (h : ExH P r S) (hS : ∀ p, S p → S' p) :
    ExH P r S' := fun hq p hp => (h hq p hp).imp_right (hS p)

theorem ExN.mono {r : Res} {N N' : Loc → Time → Prop} (h : ExN r N) (hN : ∀ x t, N x t → N' x t) : ExN r N' :=
  fun x hx hq p hp => (h x hx hq p hp).imp_right (hN x p.2)

theorem ExH.addW_ne {P : Params} {r : Res} {S : Val × Time → Prop} (h : ExH P r S) {l : Loc} (hl : l ≠ P.hd)
    (p : Val × Time) : ExH P (r.addW l p) S := by
  intro hq p' hp
  rw [Res.addW_wr_ne _ _ (Ne.symm hl)] at hq hp
  exact h hq p' hp

/-- A component with a zero fraction adds nothing to the write set. -/
theorem X_op_of_q {a b : Perm} {q : Rat} (ha : q ≤ a.q) (hq : (a.op b).q = q) {p : Val × Time} (hp : (a.op b).X p) :
    a.X p := by
  rcases hp with hp | hp
  · exact hp
  · have hb0 : b.q = 0 := by have := b.nonneg; simp only [Perm.op] at hq; grind
    exact absurd hp (b.zero hb0 p)

theorem ExH.cas {P : Params} {r : Res} {S : Val × Time → Prop} (h : ExH P r S) (hge : 1 / 2 ≤ (r.wr P.hd).q)
    (new : Val) (tw : Time) (C : Res) : ExH P ((r.addW P.hd (new, tw)).op C) (fun p => S p ∨ p = (new, tw)) := by
  intro hq p hp
  have hq0 : ((r.addW P.hd (new, tw)).wr P.hd).q = 1 / 2 := by
    have := (C.wr P.hd).nonneg
    have e : (((r.addW P.hd (new, tw)).op C).wr P.hd).q = ((r.addW P.hd (new, tw)).wr P.hd).q + (C.wr P.hd).q := rfl
    rw [Res.addW_q] at e ⊢; grind
  have hp' := X_op_of_q (Rat.le_refl) (show (((r.addW P.hd (new, tw)).wr P.hd).op (C.wr P.hd)).q = _ from
    (show (((r.addW P.hd (new, tw)).op C).wr P.hd).q = 1 / 2 from hq).trans hq0.symm) hp
  rw [Res.addW_X_self] at hp'
  rw [Res.addW_q] at hq0
  rcases hp' with hp' | ⟨-, rfl⟩
  · exact (h hq0 p hp').imp_right .inl
  · exact .inr (.inr rfl)

theorem ExN.cas {P : Params} {r : Res} {N : Loc → Time → Prop} (h : ExN r N) (hge : ∀ x : Loc, x.bytes = 8 → 1 ≤ (r.wr x).q)
    (new : Val) (tw : Time) (C : Res) : ExN ((r.addW P.hd (new, tw)).op C) N := by
  intro x hx hq p hp
  have hne : x ≠ P.hd := by intro he; rw [he] at hx; simp at hx
  have e : (r.addW P.hd (new, tw)).wr x = r.wr x := Res.addW_wr_ne _ _ hne
  have hq' : (((r.wr x)).op (C.wr x)).q = 1 := by rw [← e]; exact hq
  have hp' : ((r.wr x).op (C.wr x)).X p := by rw [← e]; exact hp
  have hq1 : (r.wr x).q = 1 := by
    have := (C.wr x).nonneg; have := hge x hx; simp only [Perm.op] at hq'; grind
  exact h x hx hq1 p (X_op_of_q (q := 1) (by rw [hq1]; exact Rat.le_refl) hq' hp')

theorem ExN.store {r : Res} {N : Loc → Time → Prop} (h : ExN r N) (L : Loc) (v : Val) (tw : Time) :
    ExN (r.addW L (v, tw)) (fun x t => N x t ∨ (x = L ∧ t = tw)) := by
  intro x hx hq p hp
  by_cases hxL : x = L
  · subst hxL
    rw [Res.addW_q] at hq
    rw [Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact (h x hx hq p hp).imp_right .inl
    · exact .inr (.inr ⟨rfl, rfl⟩)
  · rw [Res.addW_wr_ne _ _ hxL] at hq hp
    exact (h x hx hq p hp).imp_right .inl

theorem ExH.addW_nd {P : Params} {r : Res} {S : Val × Time → Prop} (h : ExH P r S) (p : BitVec 64) (q : Val × Time) :
    ExH P (r.addW (nd p) q) S := h.addW_ne (nd_ne_hd P p) q

end Kraken.Promising.X64.EnvG.VecABA
