/-
**The per-access VCs of Dekker's
`worker` on `EnvGX`**. x64, `Arch.tso`,
the empty plan (no planned release: every store pure; Dekker transfers no
resource), the shared layout `[(f, 4), (o, 4), (c, 4)]` (own flag, other
flag, counter).

The thread holds all of its flag `F` and half of the counter `C`; its
resource's write sets are tracked exactly (`Res0`), which at a final
configuration gives the histories of `EnvG/DekkerFinal.lean`
(`flagHist_of_erase`, `cntHist_of_erase`). The memory facts (`SBFact`,
windows, own messages) live in the snapshot and are carried along by
`MemLe` (each access re-anchors to an extension).

Stages (`D0` … `D6`), one per access of `worker`:
`movl $1,(F)` · `mfence` · `movl (O),%eax` · [`eax = 0`] `movl (C),%ecx` ·
`movl %ecx,(C)` (after `addl $1`) · `movl $0,(F)`. `D6` is `Entered` (the
final argument's per-thread facts) at the snapshot. Every stage is monotone
under `FenceLe` (`vcgen`'s silent steps).
-/
import Kraken.Promising.SLR.EnvG.DekkerFinal
import Kraken.Promising.SLR.EnvG.X64Link
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.Promising.SLR.EnvG.VCGenCommon
import Kraken.Promising.SLR.EnvG.Alias
import Kraken.Promising.SLR.EnvG.SpscCommon

namespace Kraken.Promising.X64.EnvG.Dekker

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Dekker
open Kraken.Promising.X64.EnvG

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Memory growth -/

/-- `m'` extends `m` (same initial values, memory prefix). -/
def MemLe (m m' : Memory) : Prop := m'.init = m.init ∧ m.msgs.toList <+: m'.msgs.toList

theorem MemLe.trans {m₁ m₂ m₃ : Memory} (h₁ : MemLe m₁ m₂) (h₂ : MemLe m₂ m₃) : MemLe m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

theorem memLe_snap {I : ISA} {tid : Nat} {c c' : Config I} (h : SnapLe tid c c') : MemLe c.mem c'.mem :=
  ⟨h.init, h.msgs⟩

theorem memLe_writeSnap {I : ISA} {tid : Nat} {c c' : Config I} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) : MemLe c.mem c'.mem := by
  rcases h.mem with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm]; exact ⟨rfl, List.prefix_refl _⟩
  · rw [hm]; exact ⟨rfl, by simp [Memory.append, Array.toList_push]⟩

-- A message read is at or below the last timestamp (neutral, `SpscCommon`).
hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.read?_le_last ↦ Kraken.Promising.X64.EnvG.Dekker.read?_le_last]

theorem MemLe.get? {m m' : Memory} (h : MemLe m m') {ts : Time} {w : Msg} (hg : m.get? ts = some w) :
    m'.get? ts = some w :=
  Memory.get?_of_prefix h.2 hg

theorem MemLe.read? {m m' : Memory} (h : MemLe m m') {l : Loc} {ts : Time} {v : Val} (hr : m.read? l ts = some v) :
    m'.read? l ts = some v :=
  read?_of_prefix h.1 h.2 hr

theorem MemLe.sbFact {m m' : Memory} (h : MemLe m m') {tid : Nat} {f l : Loc} {v v' : Val} {tw tr : Time}
    (hf : SBFact m tid f v l v' tw tr) : SBFact m' tid f v l v' tw tr :=
  hf.prefix h.1 h.2

theorem MemLe.noWriteIn {m m' : Memory} (h : MemLe m m') {l : Loc} {lo hi : Time} (hhi : hi ≤ m.last)
    (hn : NoWriteIn m l lo hi) : NoWriteIn m' l lo hi :=
  hn.prefix h.2 hhi

/-- `Entered` is stable under memory growth. -/
theorem MemLe.entered {m m' : Memory} (h : MemLe m m') {j : Nat} {Fj Fo C : Loc} {t r trc : Time} {a : Val}
    {tc u : Time} (he : Entered m j Fj Fo C t r trc a tc u) : Entered m' j Fj Fo C t r trc a tc u where
  raise := h.get? he.raise
  readF := by obtain ⟨v, hv, hz⟩ := he.readF; exact ⟨v, h.read? hv, hz⟩
  winF := h.noWriteIn (Memory.last_le_of_get?_eq_some m he.raise) he.winF
  readC := h.read? he.readC
  winC := h.noWriteIn (by obtain ⟨v, hv, -⟩ := he.readF; exact read?_le_last hv) he.winC
  write := h.get? he.write
  coh := he.coh
  lower := h.get? he.lower
  rel := he.rel

/-! ## The environment and the stages -/

/-- Dekker's plan: no planned release. -/
abbrev dkPlan : Plan := ⟨[]⟩

/-- The shared layout: own flag, other flag, counter. -/
abbrev dkS (f o c : BitVec 64) : SharedEnv.Layout := [(f, 4), (o, 4), (c, 4)]

/-- The environment of Dekker's thread `tid` (x64, `Arch.tso`). -/
abbrev E (tid : Nat) (f o c : BitVec 64) : SharedEnv := EnvGX Arch.tso tid dkPlan (dkS f o c)

/-- The three locations are distinct. -/
structure Locs (f o c : BitVec 64) : Prop where
  fo : (⟨f, 4⟩ : Loc) ≠ ⟨o, 4⟩
  fc : (⟨f, 4⟩ : Loc) ≠ ⟨c, 4⟩
  oc : (⟨o, 4⟩ : Loc) ≠ ⟨c, 4⟩

/-- Every release predicate is pure at every value (nothing is released). -/
def World (g : Ghost) : Prop := ∀ x v, Pred.Pure (g.rel x) v

theorem World.anchor {tid : Nat} {σ : EStateX} {c : Config isa} {g : Ghost} (h : World σ.g)
    (hanc : AnchorOk tid σ c g) : World g := by
  unfold World; rw [hanc.rel]; exact h

/-- The initial write only. -/
def X0 (p : Val × Time) : Prop := p.2 = 0 ∧ p.1 = 0

/-- The flag's writes after the raise at `t`. -/
def XF1 (t : Time) (p : Val × Time) : Prop := X0 p ∨ (p.2 = t ∧ p.1 = 1)

/-- The flag's writes after the lowering at `u` (`flagHist_of_erase`'s form). -/
def XF2 (t u : Time) (p : Val × Time) : Prop := X0 p ∨ (p.2 = t ∧ p.1 = 1) ∨ (some u = some p.2 ∧ p.1 = 0)

/-- The counter's writes after the increment `w` (`cntHist_of_erase`'s form). -/
def XC1 (w : Val × Time) (p : Val × Time) : Prop := X0 p ∨ p = w

/-- **The resource facts**: the world, all of the own flag and half of the
counter, with write sets inside `XF`/`XC`. -/
structure Res0 (f c : BitVec 64) (σ : EStateX) (XF XC : Val × Time → Prop) : Prop where
  world : World σ.g
  qF : (σ.r.wr ⟨f, 4⟩).q = 1
  xF : ∀ p, (σ.r.wr ⟨f, 4⟩).X p → XF p
  qC : (σ.r.wr ⟨c, 4⟩).q = 1 / 2
  xC : ∀ p, (σ.r.wr ⟨c, 4⟩).X p → XC p

theorem Res0.fence {f c : BitVec 64} {σ σ' : EStateX} {XF XC : Val × Time → Prop} (h : Res0 f c σ XF XC)
    (hf : FenceLe σ σ') : Res0 f c σ' XF XC := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [← hf.g] at h1; rw [← hf.r] at h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

theorem Res0.anchor {tid : Nat} {f c : BitVec 64} {σ σ' : EStateX} {XF XC : Val × Time → Prop}
    (h : Res0 f c σ XF XC) {c' : Config isa} (hanc : AnchorOk tid σ c' σ'.g) (hr : σ'.r = σ.r) :
    Res0 f c σ' XF XC := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [← hr] at h2 h3 h4 h5
  exact ⟨h1.anchor hanc, h2, h3, h4, h5⟩

/-- Before the raise. -/
def D0 (f o c : BitVec 64) (σ : EStateX) : Prop :=
  Res0 f c σ X0 X0 ∧ σ.vs.getFwd ⟨o, 4⟩ = none ∧ σ.vs.getFwd ⟨c, 4⟩ = none

/-- Before the fence: the raise at `t ≤ vwOld`. -/
def D1 (tid : Nat) (f o c : BitVec 64) (σ : EStateX) : Prop :=
  ∃ t, σ.snap.mem.get? t = some ⟨⟨f, 4⟩, 1, tid⟩ ∧ t ≤ σ.vs.vwOld ∧ Res0 f c σ (XF1 t) X0 ∧
    σ.vs.getFwd ⟨o, 4⟩ = none ∧ σ.vs.getFwd ⟨c, 4⟩ = none

/-- Before the read of the other flag: the raise at `t ≤ vrNew`. -/
def D2 (tid : Nat) (f o c : BitVec 64) (σ : EStateX) : Prop :=
  ∃ t, σ.snap.mem.get? t = some ⟨⟨f, 4⟩, 1, tid⟩ ∧ t ≤ σ.vs.vrNew ∧ Res0 f c σ (XF1 t) X0 ∧
    σ.vs.getFwd ⟨o, 4⟩ = none ∧ σ.vs.getFwd ⟨c, 4⟩ = none

/-- After reading `v` from the other flag: the `SBFact`, the acquire's
`r ≤ vrNew`. -/
def D3 (tid : Nat) (f o c : BitVec 64) (v : Val) (σ : EStateX) : Prop :=
  ∃ t r, SBFact σ.snap.mem tid ⟨f, 4⟩ 1 ⟨o, 4⟩ v t r ∧ r ≤ σ.vs.vrNew ∧ Res0 f c σ (XF1 t) X0 ∧
    σ.vs.getFwd ⟨c, 4⟩ = none

/-- After reading `a` from the counter (having read `0` from the other flag). -/
def D4 (tid : Nat) (f o c : BitVec 64) (a : Val) (σ : EStateX) : Prop :=
  ∃ t r trc v, SBFact σ.snap.mem tid ⟨f, 4⟩ 1 ⟨o, 4⟩ v t r ∧ v.setWidth 32 = 0 ∧
    σ.snap.mem.read? ⟨c, 4⟩ trc = some a ∧ NoWriteIn σ.snap.mem ⟨c, 4⟩ trc r ∧ trc ≤ σ.vs.getCoh ⟨c, 4⟩ ∧
    Res0 f c σ (XF1 t) X0

/-- After writing `inc a` to the counter at `tc`. -/
def D5 (tid : Nat) (f o c : BitVec 64) (a : Val) (σ : EStateX) : Prop :=
  ∃ t r trc v tc, SBFact σ.snap.mem tid ⟨f, 4⟩ 1 ⟨o, 4⟩ v t r ∧ v.setWidth 32 = 0 ∧
    σ.snap.mem.read? ⟨c, 4⟩ trc = some a ∧ NoWriteIn σ.snap.mem ⟨c, 4⟩ trc r ∧
    σ.snap.mem.get? tc = some ⟨⟨c, 4⟩, inc a, tid⟩ ∧ trc < tc ∧ tc ≤ σ.vs.vwOld ∧
    Res0 f c σ (XF1 t) (XC1 (inc a, tc))

/-- **After the lowering**: `Entered` at the snapshot, the write sets. -/
def D6 (tid : Nat) (f o c : BitVec 64) (σ : EStateX) : Prop :=
  ∃ t r trc a tc u, Entered σ.snap.mem tid ⟨f, 4⟩ ⟨o, 4⟩ ⟨c, 4⟩ t r trc a tc u ∧
    Res0 f c σ (XF2 t u) (XC1 (inc a, tc))

/-! ### Monotone under fences -/

section Fence

variable {tid : Nat} {f o c : BitVec 64} {σ σ' : EStateX}

theorem D0.fence (h : D0 f o c σ) (hf : FenceLe σ σ') : D0 f o c σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.fence hf, by rw [hf.getFwd]; exact h2, by rw [hf.getFwd]; exact h3⟩

theorem D1.fence (h : D1 tid f o c σ) (hf : FenceLe σ σ') : D1 tid f o c σ' := by
  obtain ⟨t, h1, h2, h3, h4, h5⟩ := h
  exact ⟨t, by rw [hf.snap]; exact h1, by rw [hf.vwOld]; exact h2, h3.fence hf, by rw [hf.getFwd]; exact h4,
    by rw [hf.getFwd]; exact h5⟩

theorem D2.fence (h : D2 tid f o c σ) (hf : FenceLe σ σ') : D2 tid f o c σ' := by
  obtain ⟨t, h1, h2, h3, h4, h5⟩ := h
  exact ⟨t, by rw [hf.snap]; exact h1, Nat.le_trans h2 hf.vrNew, h3.fence hf, by rw [hf.getFwd]; exact h4,
    by rw [hf.getFwd]; exact h5⟩

theorem D3.fence {v : Val} (h : D3 tid f o c v σ) (hf : FenceLe σ σ') : D3 tid f o c v σ' := by
  obtain ⟨t, r, h1, h2, h3, h4⟩ := h
  exact ⟨t, r, by rw [hf.snap]; exact h1, Nat.le_trans h2 hf.vrNew, h3.fence hf, by rw [hf.getFwd]; exact h4⟩

theorem D4.fence {a : Val} (h : D4 tid f o c a σ) (hf : FenceLe σ σ') : D4 tid f o c a σ' := by
  obtain ⟨t, r, trc, v, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨t, r, trc, v, by rw [hf.snap]; exact h1, h2, by rw [hf.snap]; exact h3, by rw [hf.snap]; exact h4,
    by rw [hf.getCoh]; exact h5, h6.fence hf⟩

theorem D5.fence {a : Val} (h : D5 tid f o c a σ) (hf : FenceLe σ σ') : D5 tid f o c a σ' := by
  obtain ⟨t, r, trc, v, tc, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨t, r, trc, v, tc, by rw [hf.snap]; exact h1, h2, by rw [hf.snap]; exact h3, by rw [hf.snap]; exact h4,
    by rw [hf.snap]; exact h5, h6, by rw [hf.vwOld]; exact h7, h8.fence hf⟩

theorem D6.fence (h : D6 tid f o c σ) (hf : FenceLe σ σ') : D6 tid f o c σ' := by
  obtain ⟨t, r, trc, a, tc, u, h1, h2⟩ := h
  exact ⟨t, r, trc, a, tc, u, by rw [hf.snap]; exact h1, h2.fence hf⟩

end Fence

/-! ## The VCs -/

section VC

variable {tid : Nat} {f o c : BitVec 64}

/-- The resource after an unplanned store of `v` to `l` at `tw`. -/
theorem r_after {σ σ' : EStateX} {l : Loc} {v : Val} {tw : Time}
    (hr : ∃ P : Prop, (σ.cl → P) ∧ σ'.r = dkPlan.after l v tw P σ.r) : σ'.r = σ.r.addW l (v, tw) := by
  obtain ⟨P, -, h⟩ := hr
  rw [h]; simp [Plan.after]

/-- An unplanned store to `l` is permitted with a positive share (and the
access in the layout). -/
theorem vc_store_ok {σ : EStateX} {a : BitVec 64} {v : Val} (hq : 0 < (σ.r.wr ⟨a, 4⟩).q) (hw : World σ.g)
    (hin : (a, 4) ∈ dkS f o c) : (E tid f o c).ok (.store .plain false a 4 v) σ :=
  ⟨⟨rfl, hq, fun _ => hw _ _, fun hr => by simp at hr⟩, hin⟩

/-- **The raise** `movl $1, (F)`. -/
theorem vc_raise (hL : Locs f o c) {σ : EStateX} (h : D0 f o c σ) :
    ∀ b (σ' : EStateX), (E tid f o c).step (.store .plain false f 4 1) σ b σ' → D1 tid f o c σ' := by
  intro b σ' hs
  obtain ⟨⟨hw, hqF, hxF, hqC, hxC⟩, hfo, hfc⟩ := h
  obtain ⟨c', tw, hanc, hsnap, -, hwv, -, hr, -⟩ := step_storeFacts hs
  have hr' := r_after hr
  refine ⟨tw, WriteSnap.get?_new' hsnap, hwv.vwOld (by decide), ⟨hw.anchor hanc, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hr', Res.addW_q]; exact hqF
  · intro p hp
    rw [hr'] at hp
    rcases (Res.addW_X_self _ _ _ _).mp hp with hp | ⟨-, rfl⟩
    · exact .inl (hxF p hp)
    · exact .inr ⟨rfl, rfl⟩
  · rw [hr', Res.addW_q]; exact hqC
  · intro p hp
    rw [hr', Res.addW_wr_ne _ _ (Ne.symm hL.fc)] at hp
    exact hxC p hp
  · rw [hwv.fwdOther _ (Ne.symm hL.fo)]; exact hfo
  · rw [hwv.fwdOther _ (Ne.symm hL.fc)]; exact hfc

/-- **The fence** `mfence`: `vrNew` reaches the raise. -/
theorem vc_fence {σ σ' : EStateX} (h : D1 tid f o c σ) (hfe : (E tid f o c).step (.fence .sy) σ () σ') :
    D2 tid f o c σ' := by
  obtain ⟨t, h1, h2, ⟨hw, hqF, hxF, hqC, hxC⟩, hfo, hfc⟩ := h
  have hfe' : FenceOut σ σ' .sy := hfe
  have e : σ' = _ := hfe'
  refine ⟨t, by rw [e]; exact h1, Nat.le_trans h2 (vwOld_le_vrNew_of_fence hfe'), ?_, ?_, ?_⟩
  · rw [e]; exact ⟨hw, hqF, hxF, hqC, hxC⟩
  · rw [e]; simp only [fenceViews_getFwd]; exact hfo
  · rw [e]; simp only [fenceViews_getFwd]; exact hfc

/-- **The read of the other flag** `movl (O), %eax`: the `SBFact`, and the
acquire (`acqPc` under TSO) raises `vrNew` to the message read. -/
theorem vc_readO {σ : EStateX} (h : D2 tid f o c σ) :
    ∀ v (σ' : EStateX), (E tid f o c).step (.load .plain false o 4) σ v σ' → D3 tid f o c v σ' := by
  intro v σ' hs
  obtain ⟨t, h1, h2, h3, hfo, hfc⟩ := h
  obtain ⟨hanc, hr, -, tr, hread, hlv, -⟩ := step_loadFacts (pl := dkPlan) hs
  refine ⟨t, tr, ⟨Memory.get?_of_prefix hanc.snap.msgs h1, hread.val,
    (noWriteIn_of_writeIn hread.window).mono (Nat.le_trans h2 (le_readBound_vrNew _ _ _ _))⟩,
    (hlv.acq rfl (not_fwded_of_none hfo)).1, h3.anchor hanc hr, ?_⟩
  rw [hlv.getFwd]; exact hfc

/-- **The read of the counter** `movl (C), %ecx` (the other flag read `0`):
its window reaches the flag read (`r ≤ vrNew ≤ readBound`), and coherence
rises to it. -/
theorem vc_readC {σ : EStateX} {v : Val} (h : D3 tid f o c v σ) (hz : v.setWidth 32 = 0) :
    ∀ a (σ' : EStateX), (E tid f o c).step (.load .plain false c 4) σ a σ' → D4 tid f o c a σ' := by
  intro a σ' hs
  obtain ⟨t, r, hsb, hr, h3, hfc⟩ := h
  obtain ⟨hanc, hres, -, trc, hread, hlv, -⟩ := step_loadFacts (pl := dkPlan) hs
  exact ⟨t, r, trc, v, (memLe_snap hanc.snap).sbFact hsb, hz, hread.val,
    (noWriteIn_of_writeIn hread.window).mono (Nat.le_trans hr (le_readBound_vrNew _ _ _ _)),
    hlv.coh (not_fwded_of_none hfc), h3.anchor hanc hres⟩

/-- **The write of the counter** `movl %ecx, (C)` (`ecx = a + 1`): after the
read in coherence, below `vwOld`; the counter's write set gains it. -/
theorem vc_writeC (hL : Locs f o c) {σ : EStateX} {a : Val} (h : D4 tid f o c a σ) :
    ∀ b (σ' : EStateX), (E tid f o c).step (.store .plain false c 4 (inc a)) σ b σ' → D5 tid f o c a σ' := by
  intro b σ' hs
  obtain ⟨t, r, trc, v, hsb, hz, hrd, hwin, hcoh, ⟨hw, hqF, hxF, hqC, hxC⟩⟩ := h
  obtain ⟨c', tw, hanc, hsnap, hwb, hwv, -, hr, -⟩ := step_storeFacts hs
  have hle := (memLe_snap hanc.snap).trans (memLe_writeSnap hsnap)
  have hr' := r_after hr
  refine ⟨t, r, trc, v, tw, hle.sbFact hsb, hz, hle.read? hrd,
    hle.noWriteIn (read?_le_last hsb.read) hwin, WriteSnap.get?_new' hsnap,
    Nat.lt_of_le_of_lt hcoh hwb.coh, hwv.vwOld (by decide), ⟨hw.anchor hanc, ?_, ?_, ?_, ?_⟩⟩
  · rw [hr', Res.addW_q]; exact hqF
  · intro p hp
    rw [hr', Res.addW_wr_ne _ _ hL.fc] at hp
    exact hxF p hp
  · rw [hr', Res.addW_q]; exact hqC
  · intro p hp
    rw [hr'] at hp
    rcases (Res.addW_X_self _ _ _ _).mp hp with hp | ⟨-, rfl⟩
    · exact .inl (hxC p hp)
    · exact .inr rfl

/-- **The lowering** `movl $0, (F)`: a release under TSO (`WriteBound.rel`),
so after the counter write; the thread's `Entered` facts are complete. -/
theorem vc_lower (hL : Locs f o c) {σ : EStateX} {a : Val} (h : D5 tid f o c a σ) :
    ∀ b (σ' : EStateX), (E tid f o c).step (.store .plain false f 4 0) σ b σ' → D6 tid f o c σ' := by
  intro b σ' hs
  obtain ⟨t, r, trc, v, tc, hsb, hz, hrd, hwin, hwc, hlt, hvw, ⟨hw, hqF, hxF, hqC, hxC⟩⟩ := h
  obtain ⟨c', u, hanc, hsnap, hwb, -, -, hr, -⟩ := step_storeFacts hs
  have hle := (memLe_snap hanc.snap).trans (memLe_writeSnap hsnap)
  have hr' := r_after hr
  have hrel := hwb.rel rfl
  have hsb' := hle.sbFact hsb
  refine ⟨t, r, trc, a, tc, u, ⟨hsb'.own, ⟨v, hsb'.read, hz⟩, hsb'.window, hle.read? hrd,
    hle.noWriteIn (read?_le_last hsb.read) hwin, hle.get? hwc, hlt, WriteSnap.get?_new' hsnap, ?_⟩,
    ⟨hw.anchor hanc, ?_, ?_, ?_, ?_⟩⟩
  · have : tc ≤ max (max σ.vs.vrOld σ.vs.vrOldNR) σ.vs.vwOld := Nat.le_trans hvw (Nat.le_max_right _ _)
    omega_t
  · rw [hr', Res.addW_q]; exact hqF
  · intro p hp
    rw [hr'] at hp
    rcases (Res.addW_X_self _ _ _ _).mp hp with hp | ⟨-, rfl⟩
    · rcases hxF p hp with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · exact .inr (.inr ⟨rfl, rfl⟩)
  · rw [hr', Res.addW_q]; exact hqC
  · intro p hp
    rw [hr', Res.addW_wr_ne _ _ (Ne.symm hL.fc)] at hp
    exact hxC p hp

end VC

end Kraken.Promising.X64.EnvG.Dekker
