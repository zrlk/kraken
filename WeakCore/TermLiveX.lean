/-
# TermLiveX — liveness over the spawn machine `StepX` (2c, step 2)

`TermLiveMach.machine` is the promise machine (`TermRun.Step`) as a labelled
system, and every liveness statement of `TermLiveMach`/`TermLiveProps` is
about it; **those statements are unchanged**.  This module is new: it puts
the spawn step (`TermSpawnStep.Spawn`, `StepX := Step ∨ Spawn`) into a
labelled system and instantiates `TermLiveGrow`'s growing-system lifts.

* **Labels.**  `machineX` has the machine's labels; a spawn by parent `i` is
  labelled `(i, true)`, i.e. it is one of thread `i`'s moves, so F4's weak
  fairness covers a parent waiting at a spawn site.  Every lemma of the form
  "`(i, true)` is a thread step" therefore needs the spawn split
  (`mstepX_thr`; `SoundX.thr`).
* **`mstepX_iff_StepX`** (the analogue of `mstep_iff_Step`): the labelled
  steps are exactly `StepX`; `reachS_iff_stepsX`: reachability is `StepsX`.
* **`machineX_sound`**: the spawn machine is a growing sound system with
  growing step `SpawnBy` and bound `cap` (a spawn keeps memory, keeps
  `CfgCoh`: parent and child sit at the parent's coherence views, which the
  barrier does not move; it adds exactly one thread, below `cap`).
* **Consequences**: the thread count of a `StepX` run is monotone and at most
  `cap` (`machineX_size_mono`, `machineX_size_cap`); every infinite run is
  eventually spawn-free (`machineX_ev_spawnFree`), and from that point on it
  is a run of the original `machine` (`machineX_eventually_machine`), so the
  `Step`-based results apply to the suffix as they stand.
-/
import WeakCore.TermLiveGrow
import WeakCore.TermSpawnStep

namespace TermLiveX
open CoreLang CoreTerm TermRun TermLiveProps TermLiveMach TermLiveGrow TermSpawnStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Promises.Sim (MemExt)

/-! ## §1 The spawn step of a given parent -/

/-- Thread `i` of `c` spawns, giving `c'` (`Spawn` with the parent named). -/
def SpawnBy (_p : Prog) (_k : Promises.Knobs) (_arch : Arch) (cap : Nat) (c : Cfg) (i : Nat)
    (c' : Cfg) : Prop :=
  ∃ (x f : String) (a : At) (T : Ty) (ts : List Ty) (e : Expr) (th : TTh) (rt : Ty)
    (ws : List Word), c.ths[i]? = some th ∧ th.term = .let_ x (.spawn f a T ts) e ∧
    th.promises = [] ∧ c.ths.size < cap ∧ evalAt th.env a = some (rt, ws) ∧
    c' = spawnCfg c i th x e f ts T ws

section Spawn
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat}

theorem spawn_iff {c c' : Cfg} : Spawn p k arch cap c c' ↔ ∃ i, SpawnBy p k arch cap c i c' := by
  constructor
  · intro h
    obtain ⟨i, x, f, a, T, ts, e, th, rt, ws, h1, h2, h3, h4, h5, h6⟩ := Spawn.elim h
    exact ⟨i, x, f, a, T, ts, e, th, rt, ws, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨i, x, f, a, T, ts, e, th, rt, ws, h1, h2, h3, h4, h5, rfl⟩
    exact Spawn.mk i x f a T ts e th rt ws h1 h2 h3 h4 h5

/-- The barrier does not move coherence views. -/
theorem spawnS_coh (c : Cfg) (th : TTh) : (spawnS c th).vs.coh = th.vs.coh := by
  simp only [spawnS, fenceS]
  exact stepFence_coh _ _

theorem spawnCfg_size (c : Cfg) (i : Nat) (th : TTh) (x : String) (e : Expr)
    (f : String) (ts : List Ty) (T : Ty) (ws : List Word) :
    (spawnCfg c i th x e f ts T ws).ths.size = c.ths.size + 1 := by
  simp [spawnCfg, spawnT]

theorem spawnCfg_get {c : Cfg} {i : Nat} (hi : i < c.ths.size) (th : TTh) (x : String) (e : Expr)
    (f : String) (ts : List Ty) (T : Ty) (ws : List Word) (j : Nat) :
    (spawnCfg c i th x e f ts T ws).ths[j]? =
      if j = c.ths.size then some (spawnKid c i th f ts T ws)
      else if i = j then some (spawnPar c i th x e) else c.ths[j]? := by
  simp only [spawnCfg, spawnT, Array.getElem?_push, Array.set!_eq_setIfInBounds,
    Array.size_setIfInBounds, Array.getElem?_setIfInBounds, hi, ↓reduceIte]

/-- **What a spawn does to the lifts' quantities.** -/
theorem spawnBy_sound {c c' : Cfg} {i : Nat} (h : SpawnBy p k arch cap c i c') :
    MemExt c.mem c'.mem ∧ (CfgCoh c → CfgCoh c' ∧ CohLeX c c') ∧
      c.ths.size < c'.ths.size ∧ c'.ths.size ≤ cap := by
  obtain ⟨x, f, a, T, ts, e, th, rt, ws, hth, -, -, hcap, -, rfl⟩ := h
  have hi := lt_of_get hth
  have hsz := spawnCfg_size c i th x e f ts T ws
  refine ⟨Promises.Sim.MemExt.refl _, fun hc => ⟨fun j t hj => ?_, ⟨by omega, ?_⟩⟩, by omega,
    by omega⟩
  · rw [spawnCfg_get hi] at hj
    show CohAt c.mem t.vs
    split at hj
    · cases hj
      intro b
      show (spawnS c th).vs.coh b = 0 ∨ ∃ m, c.mem[(spawnS c th).vs.coh b]? = some m ∧ m.loc = b
      rw [spawnS_coh]
      exact hc i th hth b
    · split at hj
      · cases hj
        intro b
        show (spawnS c th).vs.coh b = 0 ∨ ∃ m, c.mem[(spawnS c th).vs.coh b]? = some m ∧ m.loc = b
        rw [spawnS_coh]
        exact hc i th hth b
      · exact hc j t hj
  · intro j t t' h1 h2 b
    rw [spawnCfg_get hi] at h2
    have hj : j ≠ c.ths.size := Nat.ne_of_lt (lt_of_get h1)
    simp only [hj, ↓reduceIte] at h2
    split at h2
    · rename_i hij
      subst hij
      cases h2
      rw [hth] at h1
      cases h1
      show th.vs.coh b ≤ (spawnS c th).vs.coh b
      rw [spawnS_coh]
      exact Nat.le_refl _
    · rw [h1] at h2
      cases h2
      exact Nat.le_refl _

/-! ## §2 The labelled spawn machine -/

/-- The machine's labelled steps, with a spawn by parent `i` under label `(i, true)`. -/
def mstepX (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) (c : Cfg) :
    Nat × Bool → Cfg → Prop
  | (i, true), c' => mstep p k arch c (i, true) c' ∨ SpawnBy p k arch cap c i c'
  | (i, false), c' => mstep p k arch c (i, false) c'

/-- The spawn machine as a labelled system. -/
def machineX (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) : LSys where
  L := Nat × Bool
  S := mstepX p k arch cap
  actor l := some l.1
  thr i := (i, true)

/-- **The spawn split.**  A move under thread `i`'s label is a certified thread
step or a spawn by `i`. -/
theorem mstepX_thr {c c' : Cfg} {i : Nat} :
    mstepX p k arch cap c (i, true) c' ↔
      (c' ∈ threadSteps p k arch c i ∧ Certified p k arch c' i) ∨ SpawnBy p k arch cap c i c' :=
  Iff.rfl

/-- **The labelled steps are exactly `StepX`.** -/
theorem mstepX_iff_StepX {c c' : Cfg} :
    (∃ l, mstepX p k arch cap c l c') ↔ StepX p k arch cap c c' := by
  constructor
  · rintro ⟨⟨i, (_ | _)⟩, h⟩
    · exact Or.inl (mstep_iff_Step.1 ⟨(i, false), h⟩)
    · rcases h with h | h
      · exact Or.inl (mstep_iff_Step.1 ⟨(i, true), h⟩)
      · exact Or.inr (spawn_iff.2 ⟨i, h⟩)
  · rintro (h | h)
    · obtain ⟨⟨i, b⟩, hm⟩ := mstep_iff_Step.2 h
      cases b with
      | false => exact ⟨(i, false), hm⟩
      | true => exact ⟨(i, true), Or.inl hm⟩
    · obtain ⟨i, hs⟩ := spawn_iff.1 h
      exact ⟨(i, true), Or.inr hs⟩

/-- Reachability in `machineX` is `StepsX`. -/
theorem reachS_iff_stepsX {c c' : Cfg} :
    ReachS (machineX p k arch cap) c c' ↔ StepsX p k arch cap c c' := by
  constructor
  · intro h
    induction h with
    | refl => exact StepsG.refl _
    | step l hS _ ih => exact StepsG.step (mstepX_iff_StepX.1 ⟨l, hS⟩) ih
  · intro h
    induction h with
    | refl => exact ReachS.refl _
    | step hS _ ih =>
        obtain ⟨l, hl⟩ := mstepX_iff_StepX.2 hS
        exact ReachS.step l hl ih

/-- **The spawn machine is a growing sound system.** -/
theorem machineX_sound (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) :
    SoundX (machineX p k arch cap) p k arch (SpawnBy p k arch cap) (fun _ => cap) where
  mem := by
    rintro c ⟨i, (_ | _)⟩ c' h
    · exact (machine_sound p k arch).mem c (i, false) c' h
    · rcases h with h | h
      · exact (machine_sound p k arch).mem c (i, true) c' h
      · exact (spawnBy_sound h).1
  coh := by
    rintro c ⟨i, (_ | _)⟩ c' h hc
    · have h' := (machine_sound p k arch).coh c (i, false) c' h hc
      exact ⟨h'.1, CohLeX.ofCohLe h'.2⟩
    · rcases h with h | h
      · have h' := (machine_sound p k arch).coh c (i, true) c' h hc
        exact ⟨h'.1, CohLeX.ofCohLe h'.2⟩
      · exact (spawnBy_sound h).2.1 hc
  mono := by
    rintro c ⟨i, (_ | _)⟩ c' h
    · exact Nat.le_of_eq ((machine_sound p k arch).size c (i, false) c' h).symm
    · rcases h with h | h
      · exact Nat.le_of_eq ((machine_sound p k arch).size c (i, true) c' h).symm
      · exact Nat.le_of_lt (spawnBy_sound h).2.2.1
  cap := by
    rintro c ⟨i, (_ | _)⟩ c' h hlt
    · have := (machine_sound p k arch).size c (i, false) c' h
      omega
    · rcases h with h | h
      · have := (machine_sound p k arch).size c (i, true) c' h
        omega
      · exact (spawnBy_sound h).2.2.2
  capInv _ _ _ _ := rfl
  thr _ _ _ := Iff.rfl
  grow _ _ _ h := (spawnBy_sound h).2.2.1
  actor_thr _ := rfl

/-- The size-preserving part of the spawn machine is the machine. -/
theorem restrict_machineX {c c' : Cfg} {l : Nat × Bool} :
    (restrict (machineX p k arch cap)).S c l c' ↔ (machine p k arch).S c l c' := by
  obtain ⟨i, b⟩ := l
  constructor
  · rintro ⟨h, hsz⟩
    cases b with
    | false => exact h
    | true =>
        rcases h with h | h
        · exact h
        · have := (spawnBy_sound h).2.2.1
          omega
  · intro h
    have hsz := (machine_sound p k arch).size c (i, b) c' h
    cases b with
    | false => exact ⟨h, hsz⟩
    | true => exact ⟨Or.inl h, hsz⟩

/-! ## §3 Runs of the spawn machine -/

/-- **`Run_size` for `StepX`: monotone …** -/
theorem machineX_size_mono {r : LRun (Nat × Bool)} (hr : (machineX p k arch cap).Run r)
    {n m : Nat} (h : n ≤ m) : (r.cfg n).ths.size ≤ (r.cfg m).ths.size :=
  runX_size_mono (machineX_sound p k arch cap) hr h

/-- **… and at most `cap`** (from a start within capacity). -/
theorem machineX_size_cap {r : LRun (Nat × Bool)} (hr : (machineX p k arch cap).Run r)
    (h0 : (r.cfg 0).ths.size ≤ cap) (n : Nat) : (r.cfg n).ths.size ≤ cap :=
  runX_size_cap (machineX_sound p k arch cap) hr h0 n

/-- **Every infinite `StepX` run is eventually spawn-free.** -/
theorem machineX_ev_spawnFree {r : LRun (Nat × Bool)} (hr : (machineX p k arch cap).Run r) :
    Ev (fun n => ∀ i, ¬ SpawnBy p k arch cap (r.cfg n) i (r.cfg (n + 1))) :=
  ev_noGrow (machineX_sound p k arch cap) hr

/-- **… and from then on it is a run of the promise machine**, to which the
`Step`-based liveness results apply unchanged. -/
theorem machineX_eventually_machine {r : LRun (Nat × Bool)} (hr : (machineX p k arch cap).Run r) :
    ∃ n₀, (machine p k arch).Run (shift r n₀) := by
  obtain ⟨n₀, h, -⟩ := eventually_restrict (machineX_sound p k arch cap) hr
  refine ⟨n₀, fun n => ?_⟩
  have hm : (restrict (machineX p k arch cap)).Move (r.cfg (n₀ + n)) (r.lbl (n₀ + n))
      (r.cfg (n₀ + n + 1)) := h n
  show (machine p k arch).Move (r.cfg (n₀ + n)) (r.lbl (n₀ + n)) (r.cfg (n₀ + n + 1))
  cases e : r.lbl (n₀ + n) with
  | none => rw [e] at hm; exact hm
  | some l => rw [e] at hm; exact restrict_machineX.1 hm

end Spawn

#print axioms spawn_iff
#print axioms spawnBy_sound
#print axioms mstepX_iff_StepX
#print axioms reachS_iff_stepsX
#print axioms machineX_sound
#print axioms restrict_machineX
#print axioms machineX_size_mono
#print axioms machineX_size_cap
#print axioms machineX_ev_spawnFree
#print axioms machineX_eventually_machine

end TermLiveX

/-! Axiom reports (auditor, every theorem). -/
#print axioms TermLiveX.spawnS_coh
#print axioms TermLiveX.spawnCfg_size
#print axioms TermLiveX.spawnCfg_get
#print axioms TermLiveX.mstepX_thr
