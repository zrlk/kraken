/-
# TermLiveGrow — liveness lifts for a system whose thread count grows (2c, step 1)

`TermLiveMach` states runs, fairness and livelocks for a labelled system
`LSys` and lifts the step facts to runs under `LSys.Sound`, which keeps the
thread count constant (its `size` field, and `CohLe`'s first conjunct).  A
spawn step (`TermSpawnStep.Spawn`) appends a thread, so the spawn
machine is not `Sound`.  This module adds the growing version **beside** the
existing one: every statement of `TermLiveMach`/`TermLiveProps` over `Step`
and `LSys.Sound` is unchanged, and the `X` vocabulary below is new.

* **`SoundX sys p k arch G cap`.**  Memory only grows; `CfgCoh` is kept
  and no existing thread's view goes down (`CohLeX`: `CohLe` with `≤` on the
  thread count); the thread count never shrinks, and a step that grows it
  ends at most at the capacity `cap c'`, which no step changes (a field of
  the configuration after M0, a constant before); the thread label `thr i` is the machine's certified
  thread step **or** a growing step `G c i c'` of thread `i` (a spawn of
  parent `i`, so F4 treats a spawn as a move of its parent).
* **No copied proofs: `restrict` and `shift`.**  `restrict sys` keeps only
  the steps that keep the thread count; `restrict_sound` shows it is `Sound`.
  The thread count of a run is monotone and bounded (`runX_size_mono`,
  `runX_size_le`), hence eventually constant (`runX_stable`, by
  `TermLiveMach.ev_const`); from there the run is a `restrict` run
  (`eventually_restrict`), i.e. **every infinite run is eventually free of
  growing steps** (`ev_noGrow`).  Each run lemma of `TermLiveMach` is then
  applied, unchanged, to the shifted suffix (`runX_freeze_or_grow`,
  `frozenX_noraise`, `frozenX_views_const`, `frozenX_stale_cas`,
  `frozenX_load_stale`).
* **Fairness.**  `LiveX`: present at some point (not necessarily at the start)
  and never crashed; `FairX` is F4 with `LiveX`.  On a suffix where the size
  is constant a `FairX` run is `Fair` for `restrict` (`fair_shift`).
* **The explorer bridge** (`class_runX`).  A class closed under every thread
  label of `sys` (growing steps included: a growing step is an exit) has all
  its edges size-preserving, so `class_run` applies to `restrict`, and the
  run it builds is a `FairX` run of `sys`.
* **Reachability facts** (`ReachS`): the `TermLiveProps` facts the criterion
  rests on, for any `SoundX` system: memory, thread count and views are
  constant on a class (`reachS_mem_eq`, `reachS_size_eq`, `classS_coh_eq`).
* **Statements** (§8, propositions as in `TermLiveMach` §4): `LivelockX`,
  `InducedX`, `no_induced_livelock_robustX`, `forced_wait_is_livelockX`,
  `no_induced_livelockX` (with `FairX`/`LiveX`); `inducedX_iff_shift`: an
  induced livelock of a run is exactly one of its constant-size suffix.
-/
import WeakCore.TermLiveMach

namespace TermLiveGrow
open CoreLang CoreTerm TermRun TermLiveProps TermLiveMach
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Promises.Sim (MemExt)

/-! ## §1 Growing sound systems -/

/-- No existing thread's coherence view went down; threads may be added. -/
def CohLeX (c c' : Cfg) : Prop :=
  c.ths.size ≤ c'.ths.size ∧
  ∀ (i : Nat) (th th' : TTh), c.ths[i]? = some th → c'.ths[i]? = some th' →
    ∀ b, th.vs.coh b ≤ th'.vs.coh b

theorem CohLeX.ofCohLe {c c' : Cfg} (h : CohLe c c') : CohLeX c c' := ⟨Nat.le_of_eq h.1, h.2⟩

theorem CohLeX.toCohLe {c c' : Cfg} (h : CohLeX c c') (hs : c'.ths.size = c.ths.size) :
    CohLe c c' := ⟨hs.symm, h.2⟩

theorem CohLeX.refl (c : Cfg) : CohLeX c c := CohLeX.ofCohLe (CohLe.refl c)

theorem CohLeX.trans {c1 c2 c3 : Cfg} (a : CohLeX c1 c2) (b : CohLeX c2 c3) : CohLeX c1 c3 := by
  refine ⟨Nat.le_trans a.1 b.1, fun j th th3 h1 h3 x => ?_⟩
  have hj : j < c2.ths.size := Nat.lt_of_lt_of_le (lt_of_get h1) a.1
  have h2 : c2.ths[j]? = some c2.ths[j] := Array.getElem?_eq_getElem hj
  exact Nat.le_trans (a.2 j th _ h1 h2 x) (b.2 j _ th3 h2 h3 x)

/-- What the lifts need of a system whose thread count may grow.  `G c i c'`
is a growing step of thread `i` (a spawn by parent `i`); it is part of thread
`i`'s label. -/
structure SoundX (sys : LSys) (p : Prog) (k : Promises.Knobs) (arch : Arch)
    (G : Cfg → Nat → Cfg → Prop) (capOf : Cfg → Nat) : Prop where
  mem : ∀ c l c', sys.S c l c' → MemExt c.mem c'.mem
  coh : ∀ c l c', sys.S c l c' → CfgCoh c → CfgCoh c' ∧ CohLeX c c'
  mono : ∀ c l c', sys.S c l c' → c.ths.size ≤ c'.ths.size
  cap : ∀ c l c', sys.S c l c' → c.ths.size < c'.ths.size → c'.ths.size ≤ capOf c'
  capInv : ∀ c l c', sys.S c l c' → capOf c' = capOf c
  thr : ∀ c i c', sys.S c (sys.thr i) c' ↔
    ((c' ∈ threadSteps p k arch c i ∧ Certified p k arch c' i) ∨ G c i c')
  grow : ∀ c i c', G c i c' → c.ths.size < c'.ths.size
  actor_thr : ∀ i, sys.actor (sys.thr i) = some i

/-- The size-preserving part of a system. -/
def restrict (sys : LSys) : LSys where
  L := sys.L
  S c l c' := sys.S c l c' ∧ c'.ths.size = c.ths.size
  actor := sys.actor
  thr := sys.thr

/-- A sound system is a growing sound system with no growing step. -/
theorem soundX_of_sound {sys : LSys} {p : Prog} {k : Promises.Knobs} {arch : Arch}
    (hs : sys.Sound p k arch) (cap : Nat) : SoundX sys p k arch (fun _ _ _ => False) (fun _ => cap) where
  mem := hs.mem
  coh c l c' h hc := let h' := hs.coh c l c' h hc; ⟨h'.1, CohLeX.ofCohLe h'.2⟩
  mono c l c' h := Nat.le_of_eq (hs.size c l c' h).symm
  cap c l c' h hlt := absurd (hs.size c l c' h) (Nat.ne_of_gt hlt)
  capInv _ _ _ _ := rfl
  thr c i c' := (hs.thr c i c').trans (or_iff_left id).symm
  grow _ _ _ h := h.elim
  actor_thr := hs.actor_thr

section Grow
variable {sys : LSys} {p : Prog} {k : Promises.Knobs} {arch : Arch}
  {G : Cfg → Nat → Cfg → Prop} {cap : Cfg → Nat}

/-- **The size-preserving part is `Sound`.** -/
theorem restrict_sound (hs : SoundX sys p k arch G cap) : (restrict sys).Sound p k arch where
  mem c l c' h := hs.mem c l c' h.1
  coh c l c' h hc := let h' := hs.coh c l c' h.1 hc; ⟨h'.1, h'.2.toCohLe h.2⟩
  size _ _ _ h := h.2
  thr c i c' := by
    constructor
    · rintro ⟨h, hsz⟩
      rcases (hs.thr c i c').1 h with h | h
      · exact h
      · have := hs.grow _ _ _ h
        omega
    · intro h
      exact ⟨(hs.thr c i c').2 (Or.inl h), threadSteps_size h.1⟩
  actor_thr := hs.actor_thr

theorem restrict_S {c c' : Cfg} {l : sys.L} (h : (restrict sys).S c l c') : sys.S c l c' := h.1

theorem moveX_mem (hs : SoundX sys p k arch G cap) {c c' : Cfg} {o : Option sys.L}
    (h : sys.Move c o c') : MemExt c.mem c'.mem := by
  cases o with
  | none => cases h; exact Promises.Sim.MemExt.refl _
  | some l => exact hs.mem _ _ _ h

theorem moveX_coh (hs : SoundX sys p k arch G cap) {c c' : Cfg} {o : Option sys.L}
    (h : sys.Move c o c') (hc : CfgCoh c) : CfgCoh c' ∧ CohLeX c c' := by
  cases o with
  | none => cases h; exact ⟨hc, CohLeX.refl _⟩
  | some l => exact hs.coh _ _ _ h hc

theorem moveX_size (hs : SoundX sys p k arch G cap) {c c' : Cfg} {o : Option sys.L}
    (h : sys.Move c o c') :
    c.ths.size ≤ c'.ths.size ∧ (c.ths.size < c'.ths.size → c'.ths.size ≤ cap c') ∧ cap c' = cap c := by
  cases o with
  | none => cases h; exact ⟨Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _), rfl⟩
  | some l => exact ⟨hs.mono _ _ _ h, hs.cap _ _ _ h, hs.capInv _ _ _ h⟩

/-- A `restrict` run is a run. -/
theorem run_of_restrict {r : LRun sys.L} (hr : (restrict sys).Run r) : sys.Run r := fun n => by
  have h := hr n
  cases e : r.lbl n with
  | none => rw [e] at h; exact h
  | some l => rw [e] at h; exact h.1

/-! ## §2 Runs: the thread count is monotone, bounded, eventually constant -/

/-- **A1 along a run.**  Memory only grows. -/
theorem runX_mem (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r) {n m : Nat}
    (h : n ≤ m) : MemExt (r.cfg n).mem (r.cfg m).mem := by
  induction h with
  | refl => exact Promises.Sim.MemExt.refl _
  | step _ ih => exact Promises.Sim.MemExt.trans ih (moveX_mem hs (hr _))

theorem runX_coh (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) : ∀ n, CfgCoh (r.cfg n)
  | 0 => hc
  | n + 1 => (moveX_coh hs (hr n) (runX_coh hs hr hc n)).1

/-- **`Run_size` becomes monotone.** -/
theorem runX_size_mono (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r)
    {n m : Nat} (h : n ≤ m) : (r.cfg n).ths.size ≤ (r.cfg m).ths.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (moveX_size hs (hr _)).1

/-- The capacity is constant along a run. -/
theorem runX_cap (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r) :
    ∀ n, cap (r.cfg n) = cap (r.cfg 0)
  | 0 => rfl
  | n + 1 => ((moveX_size hs (hr n)).2.2).trans (runX_cap hs hr n)

/-- **… and bounded by the capacity** (or the start, if it is above). -/
theorem runX_size_le (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r) :
    ∀ n, (r.cfg n).ths.size ≤ max (cap (r.cfg 0)) (r.cfg 0).ths.size
  | 0 => Nat.le_max_right _ _
  | n + 1 => by
      have ih := runX_size_le hs hr n
      have h := moveX_size hs (hr n)
      by_cases hlt : (r.cfg n).ths.size < (r.cfg (n + 1)).ths.size
      · have h2 := h.2.1 hlt
        rw [runX_cap hs hr (n + 1)] at h2
        exact Nat.le_trans h2 (Nat.le_max_left _ _)
      · omega

/-- With the start within capacity, every configuration is. -/
theorem runX_size_cap (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r)
    (h0 : (r.cfg 0).ths.size ≤ cap (r.cfg 0)) (n : Nat) : (r.cfg n).ths.size ≤ cap (r.cfg 0) := by
  have := runX_size_le hs hr n
  omega

/-- **The thread count is eventually constant.** -/
theorem runX_stable (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r) :
    ∃ n₀, ∀ m, n₀ ≤ m → (r.cfg m).ths.size = (r.cfg n₀).ths.size := by
  obtain ⟨n₁, -, h⟩ := ev_const (fun m => (r.cfg m).ths.size) (max (cap (r.cfg 0)) (r.cfg 0).ths.size) _ 0 rfl
    (fun m _ => runX_size_mono hs hr (Nat.le_succ m)) (fun m _ => runX_size_le hs hr m)
  exact ⟨n₁, h⟩

/-- The suffix of a run from `n₀`. -/
def shift {L : Type} (r : LRun L) (n₀ : Nat) : LRun L where
  cfg n := r.cfg (n₀ + n)
  lbl n := r.lbl (n₀ + n)

/-- On a suffix of constant size, a run is a `restrict` run. -/
theorem shift_run {r : LRun sys.L} (hr : sys.Run r) {n₀ : Nat}
    (hst : ∀ m, n₀ ≤ m → (r.cfg m).ths.size = (r.cfg n₀).ths.size) :
    (restrict sys).Run (shift r n₀) := fun n => by
  have h := hr (n₀ + n)
  have e : (r.cfg (n₀ + n + 1)).ths.size = (r.cfg (n₀ + n)).ths.size := by
    have h1 := hst (n₀ + n + 1) (by omega)
    have h2 := hst (n₀ + n) (by omega)
    omega
  show (restrict sys).Move (r.cfg (n₀ + n)) (r.lbl (n₀ + n)) (r.cfg (n₀ + n + 1))
  cases o : r.lbl (n₀ + n) with
  | none => rw [o] at h; exact h
  | some l => rw [o] at h; exact ⟨h, e⟩

/-- **Every infinite run is eventually a run of the size-preserving part.** -/
theorem eventually_restrict (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r) :
    ∃ n₀, (restrict sys).Run (shift r n₀) ∧
      ∀ m, n₀ ≤ m → (r.cfg m).ths.size = (r.cfg n₀).ths.size := by
  obtain ⟨n₀, h⟩ := runX_stable hs hr
  exact ⟨n₀, shift_run hr h, h⟩

/-- **Every infinite run is eventually free of growing steps** (spawn-free). -/
theorem ev_noGrow (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r) :
    Ev (fun n => ∀ i, ¬ G (r.cfg n) i (r.cfg (n + 1))) := by
  obtain ⟨n₀, h⟩ := runX_stable hs hr
  refine ⟨n₀, fun m hm i hg => ?_⟩
  have := hs.grow _ _ _ hg
  rw [h m hm, h (m + 1) (by omega)] at this
  exact Nat.lt_irrefl _ this

/-! ## §3 Shifting `Often`, `Ev`, `Frozen` -/

theorem ev_unshift {P : Nat → Prop} {n₀ : Nat} (h : Ev (fun n => P (n₀ + n))) : Ev P := by
  obtain ⟨m, hm⟩ := h
  refine ⟨n₀ + m, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = n₀ + d := ⟨n - n₀, by omega⟩
  exact hm d (by omega)

theorem ev_shift {P : Nat → Prop} (n₀ : Nat) (h : Ev P) : Ev (fun n => P (n₀ + n)) := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun n hn => hm _ (by omega)⟩

theorem often_shift {P : Nat → Prop} (n₀ : Nat) (h : Often P) : Often (fun n => P (n₀ + n)) := by
  intro n
  obtain ⟨m, hm, hp⟩ := h (n₀ + n)
  obtain ⟨d, rfl⟩ : ∃ d, m = n₀ + d := ⟨m - n₀, by omega⟩
  exact ⟨d, by omega, hp⟩

theorem often_unshift {P : Nat → Prop} {n₀ : Nat} (h : Often (fun n => P (n₀ + n))) : Often P := by
  intro n
  obtain ⟨m, hm, hp⟩ := h n
  exact ⟨n₀ + m, by omega, hp⟩

theorem ev_mono {P Q : Nat → Prop} (hpq : ∀ n, P n → Q n) (h : Ev P) : Ev Q :=
  let ⟨m, hm⟩ := h
  ⟨m, fun n hn => hpq n (hm n hn)⟩

theorem often_mono {P Q : Nat → Prop} (hpq : ∀ n, P n → Q n) (h : Often P) : Often Q := fun n =>
  let ⟨m, hm, hp⟩ := h n
  ⟨m, hm, hpq m hp⟩

theorem frozen_unshift {L : Type} {r : LRun L} {n₀ n₁ : Nat} (h : Frozen (shift r n₀) n₁) :
    Frozen r (n₀ + n₁) := fun n hn => by
  obtain ⟨d, rfl⟩ : ∃ d, n = n₀ + d := ⟨n - n₀, by omega⟩
  exact h d (by omega)

theorem frozen_shift {L : Type} {r : LRun L} {n₀ m : Nat} (h : Frozen r n₀) (hm : n₀ ≤ m) :
    Frozen (shift r m) 0 := fun n _ => by
  show (r.cfg (m + n)).mem = (r.cfg (m + 0)).mem
  rw [h (m + n) (by omega), h (m + 0) (by omega)]

/-! ## §4 Fairness with threads that appear later -/

/-- A live thread: present at some point, and never crashed. -/
def LiveX {L : Type} (r : LRun L) (D : Nat → Option Nat) (i : Nat) : Prop :=
  (∃ n, i < (r.cfg n).ths.size) ∧ D i = none

theorem liveX_of_live {L : Type} {r : LRun L} {D : Nat → Option Nat} {i : Nat}
    (h : Live r D i) : LiveX r D i := ⟨⟨0, h.1⟩, h.2⟩

/-- **F4 for a growing system** (`Fair` with `LiveX`). -/
structure FairX (sys : LSys) (r : LRun sys.L) (D : Nat → Option Nat)
    (RF : LRun sys.L → Prop) : Prop where
  weak : ∀ i, LiveX r D i → Ev (fun n => ∃ c', sys.S (r.cfg n) (sys.thr i) c') →
    Often (fun n => r.lbl n = some (sys.thr i))
  prog : ∀ i, LiveX r D i →
    Often (fun n => ∃ c', sys.S (r.cfg n) (sys.thr i) c' ∧ Progress (r.cfg n) c' i) →
    Often (fun n => r.lbl n = some (sys.thr i) ∧ Progress (r.cfg n) (r.cfg (n + 1)) i)
  ext : RF r

/-- A `FairX` run is `Fair` for `restrict` on each suffix. -/
theorem fair_shift {r : LRun sys.L} {D : Nat → Option Nat} {RF : LRun sys.L → Prop}
    (hF : FairX sys r D RF) (n₀ : Nat) :
    Fair (restrict sys) (shift r n₀) D (fun _ => RF r) where
  weak i hi hen := often_shift (P := fun n => r.lbl n = some (sys.thr i)) n₀
    (hF.weak i ⟨⟨n₀ + 0, hi.1⟩, hi.2⟩
      (ev_unshift (ev_mono (fun _ ⟨c', hc⟩ => ⟨c', restrict_S hc⟩) hen)))
  prog i hi hio := often_shift
    (P := fun n => r.lbl n = some (sys.thr i) ∧ Progress (r.cfg n) (r.cfg (n + 1)) i) n₀
    (hF.prog i ⟨⟨n₀ + 0, hi.1⟩, hi.2⟩
      (often_unshift (often_mono (fun _ ⟨c', hc, hp⟩ => ⟨c', restrict_S hc, hp⟩) hio)))
  ext := hF.ext

/-- A thread live in the run is present on a suffix of constant size. -/
theorem live_shift (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r)
    {D : Nat → Option Nat} {i n₀ : Nat}
    (hst : ∀ m, n₀ ≤ m → (r.cfg m).ths.size = (r.cfg n₀).ths.size) (hi : LiveX r D i) :
    Live (shift r n₀) D i := by
  obtain ⟨⟨n, hn⟩, hD⟩ := hi
  refine ⟨?_, hD⟩
  show i < (r.cfg (n₀ + 0)).ths.size
  by_cases h : n ≤ n₀
  · exact Nat.lt_of_lt_of_le hn (runX_size_mono hs hr h)
  · rw [Nat.add_zero, ← hst n (by omega)]
    exact hn

/-! ## §5 The run lemmas of `TermLiveMach`, lifted -/

/-- A suffix point past both `n₀` and the stabilisation point. -/
theorem stable_past (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r) (n₀ : Nat) :
    ∃ m, n₀ ≤ m ∧ ∀ m', m ≤ m' → (r.cfg m').ths.size = (r.cfg m).ths.size := by
  obtain ⟨n₁, h⟩ := runX_stable hs hr
  refine ⟨max n₀ n₁, Nat.le_max_left _ _, fun m' hm' => ?_⟩
  rw [h m' (by omega), h (max n₀ n₁) (Nat.le_max_right _ _)]

/-- **A run appends infinitely often or freezes.** -/
theorem runX_freeze_or_grow (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r) :
    (∃ n₀, Frozen r n₀) ∨ Often (fun n => (r.cfg n).mem.size < (r.cfg (n + 1)).mem.size) := by
  obtain ⟨n₀, hr', -⟩ := eventually_restrict hs hr
  rcases run_freeze_or_grow (restrict_sound hs) hr' with ⟨n₁, h⟩ | h
  · exact Or.inl ⟨_, frozen_unshift h⟩
  · exact Or.inr (often_unshift
      (P := fun n => (r.cfg n).mem.size < (r.cfg (n + 1)).mem.size) h)

/-- **Views settle on a frozen suffix.** -/
theorem frozenX_noraise (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) {n₀ : Nat} (hfz : Frozen r n₀) (i : Nat) :
    ∃ n₁, n₀ ≤ n₁ ∧ ∀ m, n₁ ≤ m → ∀ b, cohOf (r.cfg (m + 1)) i b ≤ cohOf (r.cfg m) i b := by
  obtain ⟨m₀, hm₀, hst⟩ := stable_past hs hr n₀
  obtain ⟨n₁, -, h⟩ := frozen_noraise (restrict_sound hs) (shift_run hr hst)
    (runX_coh hs hr hc (m₀ + 0)) (frozen_shift hfz hm₀) i
  refine ⟨m₀ + n₁, by omega, fun m hm b => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, m = m₀ + d := ⟨m - m₀, by omega⟩
  exact h d (by omega) b

/-- Each thread's coherence views are eventually constant on a frozen suffix. -/
theorem frozenX_views_const (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) {n₀ : Nat} (hfz : Frozen r n₀) (i : Nat) :
    ∃ n₁, n₀ ≤ n₁ ∧ ∀ m, n₁ ≤ m → ∀ b, cohOf (r.cfg m) i b = cohOf (r.cfg n₁) i b := by
  obtain ⟨m₀, hm₀, hst⟩ := stable_past hs hr n₀
  obtain ⟨n₁, -, h⟩ := frozen_views_const (restrict_sound hs) (shift_run hr hst)
    (runX_coh hs hr hc (m₀ + 0)) (frozen_shift hfz hm₀) i
  refine ⟨m₀ + n₁, by omega, fun m hm b => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, m = m₀ + d := ⟨m - m₀, by omega⟩
  exact h d (by omega) b

/-- **A3 on a frozen suffix of a fair run.** -/
theorem frozenX_stale_cas (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) {D : Nat → Option Nat} {RF : LRun sys.L → Prop}
    (hF : FairX sys r D RF) {i : Nat} (hi : LiveX r D i) {n₀ : Nat} (hfz : Frozen r n₀) :
    Ev (fun n => ¬ FreshCas (r.cfg n) i) := by
  obtain ⟨m₀, hm₀, hst⟩ := stable_past hs hr n₀
  exact ev_unshift (P := fun n => ¬ FreshCas (r.cfg n) i)
    (frozen_stale_cas (restrict_sound hs) (shift_run hr hst) (runX_coh hs hr hc (m₀ + 0))
      (fair_shift hF m₀) (live_shift hs hr hst hi) (frozen_shift hfz hm₀))

/-- **A4 on a frozen suffix.** -/
theorem frozenX_load_stale (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) {n₀ : Nat} (hfz : Frozen r n₀) (i : Nat) :
    ∃ n₁, n₀ ≤ n₁ ∧ ∀ m, n₁ ≤ m → r.lbl m = some (sys.thr i) →
      ∀ (th : TTh) (x : String) (acq : Bool) (a : At) (e : Expr) (t : Ty) (pw : Word) (μ : Mode)
        (u : Ty) (b : Address),
      (r.cfg m).ths[i]? = some th → th.term = .let_ x (.load acq a) e →
      evalAt th.env a = some (t, [pw]) → cellOf t = some (μ, u) → addrOf pw = some b →
      accs u = some [.one] →
      ∃ th1 t' w, (r.cfg (m + 1)).ths[i]? = some th1 ∧ th1.env.head? = some (x, t', [w]) ∧
        w.rts ≤ th.vs.coh b := by
  obtain ⟨m₀, hm₀, hst⟩ := stable_past hs hr n₀
  obtain ⟨n₁, -, h⟩ := frozen_load_stale (restrict_sound hs) (shift_run hr hst)
    (runX_coh hs hr hc (m₀ + 0)) (frozen_shift hfz hm₀) i
  refine ⟨m₀ + n₁, by omega, fun m hm => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, m = m₀ + d := ⟨m - m₀, by omega⟩
  exact h d (by omega)

/-! ## §6 The explorer bridge for a growing system -/

/-- Along a walk of steps of `sys` the thread count does not go down. -/
theorem chain_size (hs : SoundX sys p k arch G cap) {E : List Edge}
    (hE : ∀ e ∈ E, sys.S e.2.1 (sys.thr e.1) e.2.2) {c d : Cfg} {L : List Edge}
    (h : Chain E c L d) : c.ths.size ≤ d.ths.size := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons he hsrc _ ih =>
      subst hsrc
      exact Nat.le_trans (hs.mono _ _ _ (hE _ he)) ih

/-- A class of `sys` (closed under every thread label, growing steps
included) is a class of `restrict`: none of its edges grows. -/
theorem classHyp_restrict (hs : SoundX sys p k arch G cap) {C : List Cfg} {E : List Edge}
    {c₀ : Cfg} {i : Nat} (h : ClassHyp sys C E c₀ i) : ClassHyp (restrict sys) C E c₀ i where
  edge e he := by
    obtain ⟨hS, h1, h2, hne⟩ := h.edge e he
    obtain ⟨L, hL⟩ := h.conn _ h2 _ h1
    have := chain_size hs (fun e he => (h.edge e he).1) hL
    exact ⟨⟨hS, Nat.le_antisymm this (hs.mono _ _ _ hS)⟩, h1, h2, hne⟩
  conn := h.conn
  inside := h.inside
  start := h.start
  closed c hc j c' hj hS := h.closed c hc j c' hj hS.1
  coh := h.coh
  guard := h.guard

/-- **The explorer's class is a fair run** of the growing system. -/
theorem class_runX (hs : SoundX sys p k arch G cap) {C : List Cfg} {E : List Edge} {c₀ : Cfg}
    {i : Nat} (h : ClassHyp sys C E c₀ i) :
    ∃ r : LRun sys.L, sys.Run r ∧ r.cfg 0 = c₀ ∧ (∀ n, r.cfg n ∈ C) ∧
      CrashOK sys r (crashAt i) ∧ FairX sys r (crashAt i) (fun _ => True) ∧
      (∀ n, ∃ j, j ≠ i ∧ r.lbl n = some (sys.thr j)) ∧ Livelock sys r (crashAt i) := by
  have hR := classHyp_restrict hs h
  obtain ⟨r, hr, h0, hin, hcr, hF, hlbl, hll⟩ := class_run (restrict_sound hs) hR
  -- every configuration of `C` has `c₀`'s thread count
  have hsz : ∀ n, (r.cfg n).ths.size = c₀.ths.size := fun n => by
    obtain ⟨L1, h1⟩ := h.conn _ (hin n) _ h.start
    obtain ⟨L2, h2⟩ := h.conn _ h.start _ (hin n)
    exact Nat.le_antisymm (chain_size hs (fun e he => (h.edge e he).1) h1)
      (chain_size hs (fun e he => (h.edge e he).1) h2)
  -- every enabled thread step from the class is a `restrict` step
  have hen : ∀ n j c', sys.S (r.cfg n) (sys.thr j) c' → j ≠ i → (restrict sys).S (r.cfg n) (sys.thr j) c' :=
    fun n j c' hS hj => (hR.edge _ (h.closed _ (hin n) j c' hj hS)).1
  have hlive : ∀ j, LiveX r (crashAt i) j → Live r (crashAt i) j ∧ j ≠ i := fun j ⟨⟨n, hn⟩, hD⟩ =>
    ⟨⟨by rw [hsz 0, ← hsz n]; exact hn, hD⟩, fun e => by subst e; simp [crashAt] at hD⟩
  refine ⟨r, run_of_restrict hr, h0, hin, hcr, ⟨fun j hj he => ?_, fun j hj hio => ?_, trivial⟩,
    hlbl, hll⟩
  · obtain ⟨hl, hji⟩ := hlive j hj
    exact hF.weak j hl (ev_mono (fun n ⟨c', hc⟩ => ⟨c', hen n j c' hc hji⟩) he)
  · obtain ⟨hl, hji⟩ := hlive j hj
    exact hF.prog j hl (often_mono (fun n ⟨c', hc, hp⟩ => ⟨c', hen n j c' hc hji, hp⟩) hio)

/-! ## §7 Reachability: the class facts of `TermLiveProps` for a growing system -/

/-- Reachability by steps of `sys` (any label). -/
inductive ReachS (sys : LSys) : Cfg → Cfg → Prop
  | refl (c : Cfg) : ReachS sys c c
  | step {c c' c'' : Cfg} (l : sys.L) : sys.S c l c' → ReachS sys c' c'' → ReachS sys c c''

theorem reachS_mem (hs : SoundX sys p k arch G cap) {c c' : Cfg} (h : ReachS sys c c') :
    MemExt c.mem c'.mem := by
  induction h with
  | refl => exact Promises.Sim.MemExt.refl _
  | step l hS _ ih => exact Promises.Sim.MemExt.trans (hs.mem _ _ _ hS) ih

theorem reachS_size (hs : SoundX sys p k arch G cap) {c c' : Cfg} (h : ReachS sys c c') :
    c.ths.size ≤ c'.ths.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | step l hS _ ih => exact Nat.le_trans (hs.mono _ _ _ hS) ih

theorem reachS_coh (hs : SoundX sys p k arch G cap) {c c' : Cfg} (h : ReachS sys c c')
    (hc : CfgCoh c) : CfgCoh c' ∧ CohLeX c c' := by
  induction h with
  | refl => exact ⟨hc, CohLeX.refl _⟩
  | step l hS _ ih =>
      obtain ⟨h1, l1⟩ := hs.coh _ _ _ hS hc
      obtain ⟨h2, l2⟩ := ih h1
      exact ⟨h2, l1.trans l2⟩

/-- **A2.**  Two configurations that reach each other have the same memory. -/
theorem reachS_mem_eq (hs : SoundX sys p k arch G cap) {c c' : Cfg} (h : ReachS sys c c')
    (h' : ReachS sys c' c) : c'.mem = c.mem :=
  (memExt_antisymm (reachS_mem hs h) (reachS_mem hs h')).symm

/-- … and the same thread count: no growing step inside a class. -/
theorem reachS_size_eq (hs : SoundX sys p k arch G cap) {c c' : Cfg} (h : ReachS sys c c')
    (h' : ReachS sys c' c) : c'.ths.size = c.ths.size :=
  Nat.le_antisymm (reachS_size hs h') (reachS_size hs h)

/-- Views are constant on a class (`TermLiveProps.class_coh_eq` for a growing
system). -/
theorem classS_coh_eq (hs : SoundX sys p k arch G cap) {c c' : Cfg} (h : ReachS sys c c')
    (h' : ReachS sys c' c) (hc : CfgCoh c) :
    c.ths.size = c'.ths.size ∧ ∀ (i : Nat) (th th' : TTh), c.ths[i]? = some th →
      c'.ths[i]? = some th' → ∀ b, th.vs.coh b = th'.vs.coh b := by
  obtain ⟨hc', l1⟩ := reachS_coh hs h hc
  obtain ⟨_, l2⟩ := reachS_coh hs h' hc'
  exact ⟨(reachS_size_eq hs h h').symm, fun i th th' h1 h2 b =>
    Nat.le_antisymm (l1.2 i th th' h1 h2 b) (l2.2 i th' th h2 h1 b)⟩

/-! ## §8 Livelocks and the headline statements, for a growing system

The `TermLiveMach` statements quantify over `Fair` runs and `Live` threads
(present at the start).  Their growing versions use `FairX`/`LiveX`; they are
propositions, as there.  `inducedX_iff_shift`: an induced livelock of a run is
one of its constant-size suffix, a run of `restrict`. -/

/-- `Livelock` with `LiveX`. -/
def LivelockX (sys : LSys) (r : LRun sys.L) (D : Nat → Option Nat) : Prop :=
  ∃ n₀, Frozen r n₀ ∧ ∃ i, LiveX r D i ∧ Often (fun n => r.lbl n = some (sys.thr i))

/-- `Induced` with `LiveX`. -/
def InducedX (sys : LSys) (hv : HoldView) (r : LRun sys.L) (D : Nat → Option Nat) : Prop :=
  ∃ i b n P h, LiveX r D i ∧ StuckOn sys r i b ∧ Ev (fun m => hv.heldAt (r.cfg m) b n P) ∧
    Ev (fun m => hv.holder (r.cfg m) b n h) ∧ D h ≠ none

theorem livelockX_of_livelock {r : LRun sys.L} {D : Nat → Option Nat} (h : Livelock sys r D) :
    LivelockX sys r D :=
  let ⟨n₀, hf, i, hi, ho⟩ := h
  ⟨n₀, hf, i, liveX_of_live hi, ho⟩

/-- **An induced livelock lives on the constant-size suffix.** -/
theorem inducedX_iff_shift (hs : SoundX sys p k arch G cap) {r : LRun sys.L} (hr : sys.Run r)
    {hv : HoldView} {D : Nat → Option Nat} {n₀ : Nat}
    (hst : ∀ m, n₀ ≤ m → (r.cfg m).ths.size = (r.cfg n₀).ths.size) :
    InducedX sys hv r D ↔ Induced (restrict sys) hv (shift r n₀) D := by
  constructor
  · rintro ⟨i, b, n, P, h, hi, ⟨⟨m₁, v, hl⟩, ho, ht⟩, hh, hd, hD⟩
    refine ⟨i, b, n, P, h, live_shift hs hr hst hi,
      ⟨⟨m₁, v, fun m hm => hl (n₀ + m) (by omega)⟩,
        often_shift (P := fun m => r.lbl m = some (sys.thr i)) n₀ ho,
        often_shift (P := fun m => Touches (r.cfg m) i b) n₀ ht⟩,
      ev_shift (P := fun m => hv.heldAt (r.cfg m) b n P) n₀ hh,
      ev_shift (P := fun m => hv.holder (r.cfg m) b n h) n₀ hd, hD⟩
  · rintro ⟨i, b, n, P, h, hi, ⟨⟨m₁, v, hl⟩, ho, ht⟩, hh, hd, hD⟩
    refine ⟨i, b, n, P, h, ⟨⟨n₀ + 0, hi.1⟩, hi.2⟩,
      ⟨⟨n₀ + m₁, v, fun m hm => ?_⟩,
        often_unshift (P := fun m => r.lbl m = some (sys.thr i)) ho,
        often_unshift (P := fun m => Touches (r.cfg m) i b) ht⟩,
      ev_unshift (P := fun m => hv.heldAt (r.cfg m) b n P) hh,
      ev_unshift (P := fun m => hv.holder (r.cfg m) b n h) hd, hD⟩
    obtain ⟨d, rfl⟩ : ∃ d, m = n₀ + d := ⟨m - n₀, by omega⟩
    exact hl d (by omega)

/-- The robust branch for a growing system. -/
def no_induced_livelock_robustX (sys : LSys) (Setting : Cfg → Prop) (Mentioned : Proto → Prop)
    (hv : HoldView) : Prop :=
  ∀ c₀, Setting c₀ → ProgRobust Mentioned →
  ∀ (r : LRun sys.L) (D : Nat → Option Nat), sys.Run r → r.cfg 0 = c₀ → CfgCoh c₀ →
    (∀ n, ResNonAffine (r.cfg n)) → CrashOK sys r D → FairX sys r D (fun _ => True) →
    ¬ InducedX sys hv r D

/-- C for a growing system. -/
def forced_wait_is_livelockX (sys : LSys) (Setting : Cfg → Prop) (hv : HoldView) : Prop :=
  ∀ c₀, Setting c₀ →
  ∀ (r : LRun sys.L) (D : Nat → Option Nat) i b n P h m n₀, sys.Run r → r.cfg 0 = c₀ →
    CrashOK sys r D → FairX sys r D (fun _ => True) → LiveX r D i →
    hv.heldAt (r.cfg n₀) b n P → hv.holder (r.cfg n₀) b n h → D h = some m → m ≤ n₀ →
    Often (fun n => r.lbl n = some (sys.thr i)) → Often (fun n => Touches (r.cfg n) i b) →
    StuckOn sys r i b

/-- The headline, both branches, for a growing system. -/
def no_induced_livelockX (sys : LSys) (Setting : Cfg → Prop) (Mentioned Reclaimed : Proto → Prop)
    (hv : HoldView) (RF : LRun sys.L → Prop)
    (ReclaimerOK : LRun sys.L → (Nat → Option Nat) → Prop) : Prop :=
  ∀ c₀, Setting c₀ → ProgRobustOrWindowed Mentioned Reclaimed →
  ∀ (r : LRun sys.L) (D : Nat → Option Nat), sys.Run r → r.cfg 0 = c₀ → CfgCoh c₀ →
    (∀ n, ResNonAffine (r.cfg n)) → CrashOK sys r D → FairX sys r D RF → ReclaimerOK r D →
    ¬ InducedX sys hv r D

end Grow

#print axioms inducedX_iff_shift
#print axioms restrict_sound
#print axioms soundX_of_sound
#print axioms runX_size_mono
#print axioms runX_cap
#print axioms runX_size_le
#print axioms runX_stable
#print axioms eventually_restrict
#print axioms ev_noGrow
#print axioms fair_shift
#print axioms runX_freeze_or_grow
#print axioms frozenX_noraise
#print axioms frozenX_views_const
#print axioms frozenX_stale_cas
#print axioms frozenX_load_stale
#print axioms class_runX
#print axioms reachS_mem_eq
#print axioms reachS_size_eq
#print axioms classS_coh_eq

end TermLiveGrow

/-! Axiom reports (auditor, every theorem). -/
#print axioms TermLiveGrow.CohLeX.ofCohLe
#print axioms TermLiveGrow.CohLeX.toCohLe
#print axioms TermLiveGrow.CohLeX.refl
#print axioms TermLiveGrow.CohLeX.trans
#print axioms TermLiveGrow.restrict_S
#print axioms TermLiveGrow.moveX_mem
#print axioms TermLiveGrow.moveX_coh
#print axioms TermLiveGrow.moveX_size
#print axioms TermLiveGrow.run_of_restrict
#print axioms TermLiveGrow.runX_mem
#print axioms TermLiveGrow.runX_coh
#print axioms TermLiveGrow.runX_size_cap
#print axioms TermLiveGrow.shift_run
#print axioms TermLiveGrow.ev_unshift
#print axioms TermLiveGrow.ev_shift
#print axioms TermLiveGrow.often_shift
#print axioms TermLiveGrow.often_unshift
#print axioms TermLiveGrow.ev_mono
#print axioms TermLiveGrow.often_mono
#print axioms TermLiveGrow.frozen_unshift
#print axioms TermLiveGrow.frozen_shift
#print axioms TermLiveGrow.liveX_of_live
#print axioms TermLiveGrow.live_shift
#print axioms TermLiveGrow.stable_past
#print axioms TermLiveGrow.chain_size
#print axioms TermLiveGrow.classHyp_restrict
#print axioms TermLiveGrow.reachS_mem
#print axioms TermLiveGrow.reachS_size
#print axioms TermLiveGrow.reachS_coh
#print axioms TermLiveGrow.livelockX_of_livelock
