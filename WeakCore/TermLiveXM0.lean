/-
# TermLiveXM0 (M0 rebase of 2c; additive)

Under M0 the configuration carries its thread capacity `Cfg.cap`, which no machine step
changes (`TermStep.step_cap`) and which a spawn copies (`spawnCfg` only touches `ths`).
This module reads the capacity off the configuration instead of a parameter:

* `machineXC`: the spawn machine at the source configuration's capacity
  (`mstepX p k arch c.cap`); `machineXC_sound`: a growing sound system with
  `capOf := Cfg.cap`, `capInv` from `step_cap` (`TermLiveM0.machine_cap`) and the spawn's
  `spawnCfg_cap`; every other field is `machineX_sound` at `c.cap`.
* `reachS_iff_stepsXC`: reachability is `StepsX p k arch c.cap` (the `Spawn` keeps its
  `cap` parameter; it is instantiated with `c0.cap`).
* `exploreGXC`: `exploreGP` with `successorsLX … c.cap` and `extra` moves labelled `c.n`
  (`Cfg.n = max cap ths.size`): `cap` once the start is within capacity, `ths.size` on
  today's machine (`cap = 0`).

The parametric `TermLiveX`/`TermLiveXE` statements are unchanged.
-/
import WeakCore.TermLiveXE
import WeakCore.TermLiveM0

namespace TermLiveXM0
open CoreLang CoreTerm TermRun TermSmoke TermLiveProps TermLiveMach TermLiveGrow TermSpawnStep
open TermLiveX TermLiveXE TermLive
open WeakMem (Arch)

/-- (M0) The spawn machine at the source configuration's own capacity. -/
def machineXC (p : Prog) (k : Promises.Knobs) (arch : Arch) : LSys where
  L := Nat × Bool
  S c l c' := mstepX p k arch c.cap c l c'
  actor l := some l.1
  thr i := (i, true)

section M0
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}

theorem spawnCfg_cap (c : Cfg) (i : Nat) (th : TTh) (x : String) (e : Expr)
    (f : String) (ts : List Ty) (T : Ty) (ws : List Word) :
    (spawnCfg c i th x e f ts T ws).cap = c.cap := by
  rfl

/-- (M0) Every spawn-machine step keeps `Cfg.cap`. -/
theorem mstepX_cap {cap : Nat} {c c' : Cfg} {l : Nat × Bool} (h : mstepX p k arch cap c l c') :
    c'.cap = c.cap := by
  obtain ⟨i, (_ | _)⟩ := l
  · exact machine_cap (l := (i, false)) h
  · rcases h with h | h
    · exact machine_cap (l := (i, true)) h
    · obtain ⟨x, f, a, T, ts, e, th, rt, ws, -, -, -, -, -, rfl⟩ := h
      exact spawnCfg_cap c i th x e f ts T ws

/-- **(M0) The spawn machine is a growing sound system with capacity `Cfg.cap`.** -/
theorem machineXC_sound (p : Prog) (k : Promises.Knobs) (arch : Arch) :
    SoundX (machineXC p k arch) p k arch (fun c i c' => SpawnBy p k arch c.cap c i c') Cfg.cap where
  mem c l c' h := (machineX_sound p k arch c.cap).mem c l c' h
  coh c l c' h := (machineX_sound p k arch c.cap).coh c l c' h
  mono c l c' h := (machineX_sound p k arch c.cap).mono c l c' h
  cap c l c' h hlt := by
    have := (machineX_sound p k arch c.cap).cap c l c' h hlt
    rw [mstepX_cap h]
    exact this
  capInv _ _ _ h := mstepX_cap h
  thr c i c' := (machineX_sound p k arch c.cap).thr c i c'
  grow c i c' h := (machineX_sound p k arch c.cap).grow c i c' h
  actor_thr _ := rfl

/-- (M0) Reachability in `machineXC` is `StepsX` at the start's capacity. -/
theorem reachS_iff_stepsXC {c c' : Cfg} :
    ReachS (machineXC p k arch) c c' ↔ StepsX p k arch c.cap c c' := by
  constructor
  · intro h
    induction h with
    | refl => exact StepsG.refl _
    | step l hS _ ih =>
        rw [mstepX_cap hS] at ih
        exact StepsG.step (mstepX_iff_StepX.1 ⟨l, hS⟩) ih
  · intro h
    have key : ∀ {cap : Nat} {a b : Cfg}, StepsX p k arch cap a b → a.cap = cap →
        ReachS (machineXC p k arch) a b := by
      intro cap a b hab
      induction hab with
      | refl => intro _; exact ReachS.refl _
      | @step x y _ hS _ ih =>
          intro ha
          obtain ⟨l, hl⟩ := mstepX_iff_StepX.2 hS
          have hl' : (machineXC p k arch).S x l y := by
            show mstepX p k arch x.cap x l y
            rw [ha]
            exact hl
          exact ReachS.step l hl' (ih ((mstepX_cap hl).trans ha))
    exact key h rfl

end M0

/-- (M0) The explorer at the start's capacity, `extra` moves labelled `Cfg.n`. -/
def exploreGXC (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (fuel : Nat) (c : Cfg)
    (extra : Cfg → List Cfg := fun _ => []) : Graph :=
  exploreGP (successorsLXT p k arch b c.cap) (·.n) fuel c extra

/-- The spawn demo at capacity `n`, read off the start configuration. -/
def spGraphC (n : Nat) : Graph :=
  exploreGXC spProg Promises.Knobs.all .arm { maxP := 0 } 50 { spStart with cap := n }

#guard let l := analyseX (spGraphC 2) 2; l.livelocks.isEmpty && l.stuck == 0 && !l.cut
#guard let l := analyseX (spGraphC 1) 1; l.stuck > 0 && !l.cut
#guard let l := analyseX (spGraphC 0) 0; l.stuck > 0 && !l.cut

#print axioms spawnCfg_cap
#print axioms mstepX_cap
#print axioms machineXC_sound
#print axioms reachS_iff_stepsXC

end TermLiveXM0
