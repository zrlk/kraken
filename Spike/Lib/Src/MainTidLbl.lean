/-
**Main's box label along wake's source runs**: every configuration
`wakeS arch` reaches has thread 0 with `tidLbl = some (mainTidLbl 2)`
(`ClonePre`'s `th0.tidLbl`, `OpenW.hCl`'s `htid`).

The start `tidStartT 2` sets it (`wake_start`). A step only replaces a thread
in place or pushes a new one (`spawnT`), so thread 0 stays at index 0, and
its label is kept:
- a thread step keeps it (`BoxCount.threadSteps_th`);
- a promise and a wake change other fields;
- a spawn's parent keeps a set label (`spawnPar`'s `orElse`);
- an extern step sets the label only when none is set (`curCfg`).

- `T0`: the invariant; `t0_set`: a thread replaced by one keeping a set label;
  `t0_step`: one source step; `reach_t0`: along every run of `wakeS arch`.
- `mainTidLbl_of_reach`: thread 0 of a one-thread reachable configuration.
-/
import Spike.Lib.Src.BoxCount
import Spike.Lib.WakeA64

namespace Spike.Lib.MainTidLbl

open CoreLang CoreTerm TermRun
open Scc.Sem (SrcSem Ev)
open Spike.Lib.WakeT1 (wakeSrc mainTidLbl)

/-- **Thread 0 holds main's box label.** -/
def T0 (c : Cfg) : Prop := ∃ th, c.ths[0]? = some th ∧ th.tidLbl = some (mainTidLbl 2)

/-- **A thread replaced by one that keeps a set label** keeps `T0`. -/
theorem t0_set {c c' : Cfg} {i : Nat} {th th' : TTh} (hi : c.ths[i]? = some th)
    (hths : c'.ths = c.ths.set! i th') (ht : th.tidLbl = some (mainTidLbl 2) → th'.tidLbl = some (mainTidLbl 2))
    (H : T0 c) : T0 c' := by
  obtain ⟨t0, h0, hl⟩ := H
  by_cases hz : i = 0
  · subst hz
    rw [h0] at hi; cases hi
    have hlt := (Array.getElem?_eq_some_iff.mp h0).1
    exact ⟨th', by simp [hths, Array.set!_eq_setIfInBounds, hlt], ht hl⟩
  · exact ⟨t0, by rw [hths]; simpa [Array.set!_eq_setIfInBounds, hz] using h0, hl⟩

/-- **One step of wake's source** keeps `T0`. -/
theorem t0_step {arch : WeakMem.Arch} {i : Nat} {c c' : Cfg} {es : List Ev}
    (hs : (SrcSem.sourceG (WakeT1.srcPo 2 arch wakeSrc) wakeSrc).step i c es c') (H : T0 c) : T0 c' := by
  obtain ⟨hs, -⟩ := hs
  rcases hs with hs | hs | hs
  · rcases hs with ⟨hs, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
    · unfold threadSteps at hs
      cases hth : c.ths[i]? with
      | none => rw [hth] at hs; cases hs
      | some th =>
        rw [hth] at hs
        simp only [List.mem_map] at hs
        obtain ⟨⟨mem', pairs', th'⟩, hr, rfl⟩ := hs
        exact t0_set hth rfl (fun h => (TermTidLbl.tstep_tidLbl hr).trans h) H
    · unfold promise
      cases hth : c.ths[i]? with
      | none => exact H
      | some th => exact t0_set hth rfl id H
  · obtain ⟨x, f, a, T, ts, e, th, rt, ws, h1, -, -, -, -, rfl⟩ := hs
    have hmid : T0 { c with ths := c.ths.set! i (TermSpawnStep.spawnPar c i th x e) } :=
      t0_set h1 rfl (fun h => by simp [TermSpawnStep.spawnPar, h, Option.orElse]) H
    obtain ⟨t0, h0, hl⟩ := hmid
    have hlt := (Array.getElem?_eq_some_iff.mp h0).1
    refine ⟨t0, ?_, hl⟩
    simp only [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT]
    rw [Array.getElem?_push, ite_eq_right_iff.mpr fun h => absurd h (by simp only at hlt; omega)]
    exact h0
  · obtain ⟨x, n, a, e, th1, rt, ws, rs, h1, -, -, -, -, -, rfl⟩ := hs
    have hext : T0 (extCfg c i th1 x n e ws rs) := by
      cases n with
      | current =>
        cases hl : th1.tidLbl with
        | some l =>
          simp only [extCfg, curCfg, hl]
          exact t0_set h1 rfl (fun h => by rw [← hl]; exact h) H
        | none =>
          simp only [extCfg, curCfg, hl]
          exact t0_set h1 rfl (fun h => by rw [hl] at h; cases h) H
      | _ => exact t0_set h1 rfl id H
    rcases TermExtStep.wake_eq (extCfg c i th1 x n e ws rs) _ _ _ _ with h | ⟨j, th, u, hj, h2⟩
    · rw [h]; exact hext
    · rw [h2]; exact t0_set hj rfl id hext

/-- **`T0` along every run of wake's source** (from `tidStartT 2`). -/
theorem reach_t0 {arch : WeakMem.Arch} {tr : List Ev} {s : Cfg} (h : (WakeA64.wakeS arch).Reach tr s) : T0 s := by
  obtain ⟨s0, h0, hr⟩ := h
  have H : T0 s0 := by
    change WakeT1.progInitT wakeSrc 2 s0 at h0
    rw [WakeT1.wake_start] at h0
    subst h0
    exact ⟨_, rfl, rfl⟩
  clear h0
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, -, hs⟩ := hs
    exact ih (t0_step hs H)

/-- **Main's box label at a one-thread reachable configuration.** -/
theorem mainTidLbl_of_reach {arch : WeakMem.Arch} {tr : List Ev} {s : Cfg} {th0 : TTh}
    (h : (WakeA64.wakeS arch).Reach tr s) (hs : s.ths = #[th0]) : th0.tidLbl = some (mainTidLbl 2) := by
  obtain ⟨t, h0, hl⟩ := reach_t0 h
  rw [hs] at h0
  cases h0
  exact hl

end Spike.Lib.MainTidLbl

/-- info: 'Spike.Lib.MainTidLbl.mainTidLbl_of_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.MainTidLbl.mainTidLbl_of_reach
