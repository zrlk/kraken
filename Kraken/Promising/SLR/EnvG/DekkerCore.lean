/-
**Store-buffering exclusion from the `EnvG`
facts** — the key lemma of the Dekker proof. ISA-neutral; additive (no existing
definition used other than through its statement).

## Why no SC-fence logic is needed

`EnvG`'s state is a *lower bound on the actual machine*: `σ.snap` is a
configuration the actual one extends (`SnapLe`: memory grows by a prefix), and
the step facts (`EnvG/Facts.lean`) expose the machine's own timestamps:

- a store's message and its timestamp (`StoreFacts`: `WriteSnap`, and
  `WriteViews.vwOld`: `tw ≤ vwOld` for every store but a non-temporal one);
- a full fence's exact views (`FenceFacts = FenceOut`: `fenceViews vs .sy`
  folds `vwOld` into `vrNew`, `Thread.lean` `fenceStep`);
- a load's read window (`LoadFacts`: `ReadAt.window`, no write to the
  location in `(tr, readBound]`, and `vrNew ≤ readBound`).

So after `store f; fence .sy; load l` the thread knows, of its snapshot's
memory, that its own message to `f` is at some `tw` and that no write to `l`
lies in `(tr, tw]` (`SBFact`, `sbFact_of_steps`). The memory's timestamp
order is total, so of two threads with such facts, one read is at or above
the other's store (`sb_key`, `sb_exclusion`): Promising's global memory order
plays the part of the SC-fence order of RSL/FSL-style SC-fence rules. The
facts are stable under re-anchoring (`SBFact.prefix`, `SBFact.snapLe`) and
reach the final configuration through `EnvRel.snap` (`SBFact.of_envRel`),
where a final argument (the `hB`/`done` side of `ThreadRuleRX`) combines the
two threads' facts on one memory.

On x64 `vcgen` sees the exact fence step (`MachineWP.mfence_shared_spec`,
priority 50, above the monotone `envMonoX_lift_spec`), so a program proof can
carry `SBFact` in its invariant. On AArch64 the same holds for `dmb ish`
(`fence .sy`) wherever the program's `vcgen` call uses the exact fence rule.

## Contents

- `NoWriteIn`, `noWriteIn_of_writeIn`, `NoWriteIn.mono`, `NoWriteIn.prefix`.
- `sb_key`: two stores and two windows in one memory: one read is at or above
  the other thread's store. `sb_not_both_init`: the SB outcome (both read the
  initial message) is impossible.
- `SBFact`, `SBFact.prefix`, `SBFact.snapLe`, `SBFact.of_envRel`.
- `sbFact_of_steps`: `StoreFacts`, `FenceFacts … .sy`, `LoadFacts` give the
  `SBFact` at the load's snapshot.
- `sb_exclusion`: `sb_key` for two `SBFact`s.
-/
import Kraken.Promising.SLR.EnvG.Env
import Kraken.Promising.SLR.EnvG.NodeRel

namespace Kraken.Promising.SLR.EnvG.Dekker

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Write-free windows -/

/-- No write to `l` with a timestamp in `(lo, hi]` (`Memory.writeIn … = false`
as a `Prop`). -/
def NoWriteIn (m : Memory) (l : Loc) (lo hi : Time) : Prop :=
  ∀ ts w, lo < ts → ts ≤ hi → m.get? ts = some w → w.loc ≠ l

theorem noWriteIn_of_writeIn {m : Memory} {l : Loc} {lo hi : Time} (h : m.writeIn l lo hi = false) :
    NoWriteIn m l lo hi := by
  intro ts w h1 h2 hg hl
  have ht : m.writeIn l lo hi = true := by
    unfold Memory.writeIn
    rw [List.any_eq_true]
    refine ⟨ts - lo - 1, List.mem_range.mpr (by omega_t), ?_⟩
    have e : lo + (ts - lo - 1) + 1 = ts := by omega_t
    rw [e, hg]
    simp [hl]
  rw [h] at ht
  cases ht

theorem NoWriteIn.mono {m : Memory} {l : Loc} {lo hi hi' : Time} (h : NoWriteIn m l lo hi) (hle : hi' ≤ hi) :
    NoWriteIn m l lo hi' :=
  fun ts w h1 h2 hg => h ts w h1 (Nat.le_trans h2 hle) hg

/-- A window below the memory's last timestamp is one of every extension. -/
theorem NoWriteIn.prefix {m m' : Memory} (hp : m.msgs.toList <+: m'.msgs.toList) {l : Loc} {lo hi : Time}
    (hhi : hi ≤ m.last) (h : NoWriteIn m l lo hi) : NoWriteIn m' l lo hi :=
  fun ts w h1 h2 hg => h ts w h1 h2 (Memory.get?_of_prefix_le hp (Nat.le_trans h2 hhi) hg)

/-- `read?` is stable under extension (same initial values, memory prefix). -/
theorem read?_of_prefix {m m' : Memory} (hi : m'.init = m.init) (hp : m.msgs.toList <+: m'.msgs.toList)
    {l : Loc} {t : Time} {v : Val} (h : m.read? l t = some v) : m'.read? l t = some v := by
  unfold Memory.read? at *
  split
  · next h0 =>
    simp only [h0, ↓reduceIte] at h
    rw [← h]
    simp only [Memory.initVal, hi]
  · next h0 =>
    simp only [h0, ↓reduceIte] at h
    split at h
    · next w hw => rw [Memory.get?_of_prefix hp hw]; exact h
    · cases h

/-! ## The key lemma, at the memory level -/

/-- **SB exclusion, memory level.** Thread 0's message to `f0` is at `t0`,
thread 1's to `f1` at `t1`; thread 0 read `f1` at `r1` with no write to `f1`
in `(r1, t0]`, thread 1 read `f0` at `r0` with no write to `f0` in
`(r0, t1]`. Then one of the reads is at or above the other thread's store. -/
theorem sb_key {m : Memory} {f0 f1 : Loc} {t0 t1 r0 r1 : Time} {w0 w1 : Msg} (hf : f0 ≠ f1)
    (h0 : m.get? t0 = some w0) (hl0 : w0.loc = f0) (h1 : m.get? t1 = some w1) (hl1 : w1.loc = f1)
    (hr1 : NoWriteIn m f1 r1 t0) (hr0 : NoWriteIn m f0 r0 t1) : t1 ≤ r1 ∨ t0 ≤ r0 := by
  rcases Nat.lt_trichotomy t0 t1 with h | h | h
  · exact .inr (Nat.not_lt.mp fun hlt => hr0 t0 w0 hlt (Nat.le_of_lt h) h0 hl0)
  · subst h
    rw [h0] at h1
    cases h1
    exact absurd (hl0.symm.trans hl1) hf
  · exact .inl (Nat.not_lt.mp fun hlt => hr1 t1 w1 hlt (Nat.le_of_lt h) h1 hl1)

/-- **The SB outcome is impossible**: under the hypotheses of `sb_key`, the
two reads are not both of the initial messages. -/
theorem sb_not_both_init {m : Memory} {f0 f1 : Loc} {t0 t1 r0 r1 : Time} {w0 w1 : Msg} (hf : f0 ≠ f1)
    (h0 : m.get? t0 = some w0) (hl0 : w0.loc = f0) (h1 : m.get? t1 = some w1) (hl1 : w1.loc = f1)
    (hr1 : NoWriteIn m f1 r1 t0) (hr0 : NoWriteIn m f0 r0 t1) : ¬ (r1 = 0 ∧ r0 = 0) := by
  rintro ⟨rfl, rfl⟩
  have p0 : t0 ≠ 0 := by rintro rfl; simp [Memory.get?] at h0
  have p1 : t1 ≠ 0 := by rintro rfl; simp [Memory.get?] at h1
  rcases sb_key hf h0 hl0 h1 hl1 hr1 hr0 with h | h <;> omega_t

/-! ## The per-thread fact -/

/-- **The SB fact** of thread `tid` at memory `m`: its message `f := v` is at
`tw`, and its load of `l` read `v'` at `tr` with no write to `l` in
`(tr, tw]`. -/
structure SBFact (m : Memory) (tid : Nat) (f : Loc) (v : Val) (l : Loc) (v' : Val) (tw tr : Time) : Prop where
  own : m.get? tw = some ⟨f, v, tid⟩
  read : m.read? l tr = some v'
  window : NoWriteIn m l tr tw

variable {m m' : Memory} {tid : Nat} {f l : Loc} {v v' : Val} {tw tr : Time}

/-- `SBFact` is stable under memory extension. -/
theorem SBFact.prefix (h : SBFact m tid f v l v' tw tr) (hi : m'.init = m.init)
    (hp : m.msgs.toList <+: m'.msgs.toList) : SBFact m' tid f v l v' tw tr where
  own := Memory.get?_of_prefix hp h.own
  read := read?_of_prefix hi hp h.read
  window := h.window.prefix hp (Memory.last_le_of_get?_eq_some m h.own)

/-- `SBFact` is stable under re-anchoring (any thread's `SnapLe`). -/
theorem SBFact.snapLe {tid' : Nat} {c c' : Config I} (hs : SnapLe tid' c c')
    (h : SBFact c.mem tid f v l v' tw tr) : SBFact c'.mem tid f v l v' tw tr :=
  h.prefix hs.init hs.msgs

/-- `SBFact` of the env's snapshot holds of the actual configuration
(`EnvRel.snap`): in particular of a final one, in the `hB` of
`ThreadRuleRX.ofSafelyEnvG(X)`. -/
theorem SBFact.of_envRel {tid' : Nat} {pl : Plan} {σ : State I} {c : Config I} {t : Thread I} {r : Res}
    {g : Ghost} {cl : Prop} (hr : EnvRel tid' pl σ c t r g cl) (h : SBFact σ.snap.mem tid f v l v' tw tr) :
    SBFact c.mem tid f v l v' tw tr :=
  h.snapLe hr.snap

/-- **The SB fact from the load**: before the load of `l`, the snapshot holds
the own message `f := v` at `tw` and `vrNew` is at least `tw` (after a full
fence); the load's `LoadFacts` give the `SBFact` at its snapshot. -/
theorem sbFact_of_load {A : Arch} {σ σ' : State I} {kl : LoadKind}
    (hown : σ.snap.mem.get? tw = some ⟨f, v, tid⟩) (hvr : tw ≤ σ.vs.vrNew) (hl : LoadFacts A tid σ σ' kl l v') :
    ∃ tr, SBFact σ'.snap.mem tid f v l v' tw tr := by
  obtain ⟨hanc, -, -, tr, hread, -⟩ := hl
  have hb : σ.vs.vrNew ≤ readBound A σ.vs kl l := by
    unfold readBound
    omega_t
  exact ⟨tr, Memory.get?_of_prefix hanc.snap.msgs hown, hread.val,
    (noWriteIn_of_writeIn hread.window).mono (Nat.le_trans hvr hb)⟩

/-- A full fence raises `vrNew` to `vwOld` (`FenceOut`, `fenceStep .sy`). -/
theorem vwOld_le_vrNew_of_fence {σ σ' : State I} (hfe : FenceOut σ σ' .sy) : σ.vs.vwOld ≤ σ'.vs.vrNew := by
  rw [show σ' = _ from hfe]
  simp only [fenceViews, fenceStep]
  omega_t

/-- **The SB fact from the steps**: a store of `v` to `f` (not non-temporal),
a full fence, and a load of `l` reading `v'`, consecutive `EnvG` steps, give
the `SBFact` at the load's snapshot. -/
theorem sbFact_of_steps {A : Arch} {pl : Plan} {σ0 σ1 σ2 σ3 : State I} {k : StoreKind} {kl : LoadKind}
    (hnt : A.storeKind k ≠ .nt) (hs : StoreFacts A tid pl σ0 σ1 k f v) (hfe : FenceFacts σ1 σ2 .sy)
    (hl : LoadFacts A tid σ2 σ3 kl l v') : ∃ tw tr, SBFact σ3.snap.mem tid f v l v' tw tr := by
  obtain ⟨c, tw, -, hsnap, -, hwv, -⟩ := hs
  have hown : σ1.snap.mem.get? tw = some ⟨f, v, tid⟩ := WriteSnap.get?_new' hsnap
  have hsn : σ2.snap = σ1.snap := by rw [show σ2 = _ from hfe]
  rw [← hsn] at hown
  obtain ⟨tr, h⟩ := sbFact_of_load hown (Nat.le_trans (hwv.vwOld hnt) (vwOld_le_vrNew_of_fence hfe)) hl
  exact ⟨tw, tr, h⟩

/-- **SB exclusion for two threads' facts** in one memory (`sb_key`). -/
theorem sb_exclusion {tid0 tid1 : Nat} {f0 f1 : Loc} {v0 v1 x0 x1 : Val} {t0 t1 r0 r1 : Time} (hf : f0 ≠ f1)
    (h0 : SBFact m tid0 f0 v0 f1 x1 t0 r1) (h1 : SBFact m tid1 f1 v1 f0 x0 t1 r0) : t1 ≤ r1 ∨ t0 ≤ r0 :=
  sb_key hf h0.own rfl h1.own rfl h0.window h1.window

end Kraken.Promising.SLR.EnvG.Dekker
