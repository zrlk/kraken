/-
# TermLiveXE — the liveness explorer with spawn moves (2c, step 2, explorer)

`TermLive.exploreG`/`analyse` are unchanged.  This module adds the spawn
machine's explorer beside them:

* **Spawn moves are exits.**  `successorsLX` is `successorsL` plus every
  enabled spawn (`spawnMoves`), labelled `(parent, true)`, so `analyse` counts
  it as a thread move: one that leaves the class, since a spawn adds a thread
  and nothing removes one (`spawn_exit`: no `StepX` path returns).
* **The reduction never prunes a spawn**.  A thread at a spawn
  site has no thread step (`threadSteps_spawn`), so `successorsL`'s silent
  choice never picks it (`site_not_silent`); and spawn moves are appended at
  every node, reduced or not (`spawn_offered`), so two parents spawning in
  either order are both explored.  Inside a class there is no spawn, so the
  reduction argument of `TermLive`'s header is unchanged (it stays the open
  `ExplorerBridge` item).
* **`extra` (crash) moves are labelled `cap`**, not `d.ths.size` (the next
  child's index).
* **A parent at capacity counts as stuck** (`capStuck`, added to `stuck` by
  `analyseX`): a thread at a spawn site, with no promise out, in a
  configuration with `cap` threads.
* `spawnSucc_iff`: the computable spawn successors are exactly `SpawnBy`.
* **One program text**: `exploreGX` is `TermLive.exploreGP` (as `exploreG` is)
  on `successorsLX`.
* **`ExplorerBridgeX`**: the open explorer half, stated as the existing
  `ExplorerBridge` is (an open item, not a premise); `livelock_runX` is what it
  would give.
-/
import WeakCore.TermLiveX
import WeakCore.TermLive

namespace TermLiveXE
open CoreLang CoreTerm TermRun TermSmoke TermLiveProps TermLiveMach TermLiveGrow TermSpawnStep
  TermLiveX TermLive
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §1 Spawn successors -/

/-- The spawn successors of thread `i` (at most one). -/
def spawnSucc (cap : Nat) (c : Cfg) (i : Nat) : List Cfg :=
  match c.ths[i]? with
  | some th =>
      match th.term with
      | .let_ x (.spawn f a T ts) e =>
          if th.promises.isEmpty && decide (c.ths.size < cap) then
            match evalAt th.env a with
            | some (_, ws) => [spawnCfg c i th x e f ts T ws]
            | none => []
          else []
      | _ => []
  | none => []

theorem spawnSucc_iff {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    {i : Nat} : c' ∈ spawnSucc cap c i ↔ SpawnBy p k arch cap c i c' := by
  constructor
  · intro h
    unfold spawnSucc at h
    split at h
    · rename_i th hth
      split at h
      · rename_i x f a T ts e hterm
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hc
          split at h
          · rename_i rt ws hev
            simp only [List.mem_singleton] at h
            exact ⟨x, f, a, T, ts, e, th, rt, ws, hth, hterm, hc.1, hc.2, hev, h⟩
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · rintro ⟨x, f, a, T, ts, e, th, rt, ws, hth, hterm, hp, hcap, hev, rfl⟩
    simp [spawnSucc, hth, hterm, hp, hcap, hev]

/-- Every enabled spawn of `c`, labelled with its parent and `true`. -/
def spawnMoves (cap : Nat) (c : Cfg) : List (Nat × Bool × Cfg) :=
  (List.range c.ths.size).flatMap fun i => (spawnSucc cap c i).map fun c' => (i, true, c')

theorem spawnMoves_iff {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    {i : Nat} {t : Bool} : (i, t, c') ∈ spawnMoves cap c ↔ t = true ∧ SpawnBy p k arch cap c i c' := by
  simp only [spawnMoves, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨j, -, d, hd, rfl, rfl, rfl⟩
    exact ⟨rfl, spawnSucc_iff.1 hd⟩
  · rintro ⟨rfl, h⟩
    have hi : i < c.ths.size := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hth, -⟩ := h
      exact lt_of_get hth
    exact ⟨i, hi, c', spawnSucc_iff.2 h, rfl, rfl, rfl⟩

/-- `successorsL` plus the spawn moves. -/
def successorsLX (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (cap : Nat) (c : Cfg) :
    List (Nat × Bool × Cfg) :=
  successorsL p k arch b c ++ spawnMoves cap c

/-! ## §2 The reduction and spawns -/

/-- **Every enabled spawn is offered**, at every node (none is pruned). -/
theorem spawn_offered {p : Prog} {k : Promises.Knobs} {arch : Arch} {b : Bounds} {cap : Nat}
    {c c' : Cfg} {i : Nat} (h : SpawnBy p k arch cap c i c') :
    (i, true, c') ∈ successorsLX p k arch b cap c :=
  List.mem_append_right _ (spawnMoves_iff.2 ⟨rfl, h⟩)

/-- **A thread at a spawn site is never the reduction's silent choice**: it has
no thread step. -/
theorem site_not_silent {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {th : TTh} (hth : c.ths[i]? = some th) (hs : AtSite th) :
    (threadSteps p k arch c i).isEmpty = true := by
  obtain ⟨x, f, a, T, ts, e, h⟩ := hs
  rw [threadSteps_spawn hth h]
  rfl

/-- **A spawn is an exit**: no `StepX` path leads back. -/
theorem spawn_exit {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg} {i : Nat}
    (h : SpawnBy p k arch cap c i c') : ¬ StepsX p k arch cap c' c := fun hb => by
  have h1 := reachS_size (machineX_sound p k arch cap) (reachS_iff_stepsX.2 hb)
  have h2 := (spawnBy_sound h).2.2.1
  omega

/-! ## §3 The explorer and the analysis -/

/-- `TermLive.exploreGP` with `successorsLX`, and `extra` (crash) moves labelled `cap`. -/
def exploreGX (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (cap fuel : Nat) (c : Cfg)
    (extra : Cfg → List Cfg := fun _ => []) : Graph :=
  exploreGP (successorsLX p k arch b cap) (fun _ => cap) fuel c extra

/-- Thread `th` sits at a spawn site with no promise out (decidable `AtSite`). -/
def atSiteB (th : TTh) : Bool :=
  match th.term with
  | .let_ _ (.spawn ..) _ => th.promises.isEmpty
  | _ => false

/-- Expanded configurations in which a parent waits at a spawn site at capacity. -/
def capStuck (g : Graph) (cap : Nat) : Nat :=
  ((List.range g.nodes.size).filter fun v =>
    g.expanded[v]! && decide (cap ≤ (g.nodes[v]!).ths.size) && (g.nodes[v]!).ths.any atSiteB).length

/-- `analyse`, with a parent at capacity counted as stuck. -/
def analyseX (g : Graph) (cap : Nat) : Live :=
  let l := analyse g
  { l with stuck := l.stuck + capStuck g cap }

/-- **Open: the explorer's half of the bridge, for the spawn machine** (as
`TermLiveMach.ExplorerBridge`, which stays open; not a premise of any final).
Every fair livelock `analyseX` reports on `exploreGX` (with `crashCfg` edges
for thread `i`) comes from a class satisfying `ClassHyp` on `machineX`; an
index `≥ cap` encodes "nobody crashed" (no configuration has `cap` threads or
more).  Needs what `ExplorerBridge` needs, plus `spawnSucc_iff` (spawn moves
are exactly `SpawnBy`) and `spawn_offered` (none is pruned). -/
def ExplorerBridgeX (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (cap fuel : Nat)
    (c : Cfg) (i : Nat) : Prop :=
  let g := exploreGX p k arch b cap fuel c (fun d => (crashCfg d i).toList)
  ∀ ll ∈ (analyseX g cap).livelocks, ∃ C E c₀ j, (j = i ∨ cap ≤ j) ∧
    ClassHyp (machineX p k arch cap) C E c₀ j ∧ C.length = ll.size

/-- What the open bridge would give: each reported livelock carries a `FairX`
run of the spawn machine that stays in its class (`class_runX`). -/
theorem livelock_runX {p : Prog} {k : Promises.Knobs} {arch : Arch} {b : Bounds} {cap fuel : Nat}
    {c : Cfg} {i : Nat} (hB : ExplorerBridgeX p k arch b cap fuel c i) :
    ∀ ll ∈ (analyseX (exploreGX p k arch b cap fuel c (fun d => (crashCfg d i).toList)) cap).livelocks,
      ∃ (C : List Cfg) (j : Nat) (r : LRun (Nat × Bool)), (j = i ∨ cap ≤ j) ∧ C.length = ll.size ∧
        (machineX p k arch cap).Run r ∧ (∀ n, r.cfg n ∈ C) ∧
        CrashOK (machineX p k arch cap) r (crashAt j) ∧
        FairX (machineX p k arch cap) r (crashAt j) (fun _ => True) ∧
        Livelock (machineX p k arch cap) r (crashAt j) := by
  intro ll hll
  obtain ⟨C, E, c₀, j, hj, hC, hlen⟩ := hB ll hll
  obtain ⟨r, hr, -, hin, hcr, hF, -, hll'⟩ := class_runX (machineX_sound p k arch cap) hC
  exact ⟨C, j, r, hj, hlen, hr, hin, hcr, hF, hll'⟩

/-! ## §4 Pinned

A parent spawns a child that returns its argument.  With room for the child
every fair run terminates; at capacity the parent is stuck.  The old explorer
reports the spawn site as stuck either way (a false alarm). -/

def kidD : Decl where
  name := "kid"; idx := []; arg := "a"; argTy := .int; retTy := .int
  body := .ret (v "a")

def parD : Decl where
  name := "par"; idx := []; arg := "a"; argTy := .int; retTy := .int
  body := .let_ "x" (.spawn "kid" (v "a") .int []) (.ret (v "x"))

def spProg : Prog := [kidD, parD]

def spStart : Cfg :=
  { mem := #[], ths := #[{ term := .tail "par" [] (v "a") [], env := [("a", .int, [cst (.num 7)])] }] }

def spGraph (cap : Nat) : Graph :=
  exploreGX spProg Promises.Knobs.all .arm { maxP := 0 } cap 50 spStart

#guard let l := analyseX (spGraph 2) 2; l.livelocks.isEmpty && l.stuck == 0 && !l.cut
#guard let l := analyseX (spGraph 1) 1; l.stuck > 0 && !l.cut
#guard let l := analyse (exploreG spProg Promises.Knobs.all .arm { maxP := 0 } 50 spStart); l.stuck > 0

-- On a spawn-free program `exploreGX` builds `exploreG`'s graph (the mutex).
#guard match mSetup with
  | some s =>
      let c := TermSmoke.spawn s (mThr s)
      let g := exploreG mutexLib Promises.Knobs.all .arm { maxP := 0 } 300 c
      let gx := exploreGX mutexLib Promises.Knobs.all .arm { maxP := 0 } 2 300 c
      g.nodes.size == gx.nodes.size && g.edges.toList == gx.edges.toList && g.cut == gx.cut
  | none => false

#guard match mSetup with
  | some s =>
      let c := TermSmoke.spawn s (mThr s)
      let l := analyseX (exploreGX mutexLib Promises.Knobs.all .arm { maxP := 0 } 2 300 c
        (fun d => (crashCfg d 0).toList)) 2
      !l.livelocks.isEmpty && l.stuck == 0 && !l.cut &&
      l.livelocks.all fun ll => ll.stepping == [1] && ll.done == [0] && ll.blocked == [] && !ll.promised
  | none => false

#print axioms spawnSucc_iff
#print axioms spawnMoves_iff
#print axioms spawn_offered
#print axioms site_not_silent
#print axioms spawn_exit
#print axioms livelock_runX

end TermLiveXE
