/-
**Main's box label along hello's source runs on the x86-64 side** (the twin of
`Spike/Lib/HelloMainTidLbl.lean`, over `Spike/Lib/Src/X64MainTidLbl.lean` and `Spike/Lib/X64HelloSrc.lean`):
every configuration `helloS arch` reaches has thread 0 with `tidLbl = some (mainTidLbl 2)`.

`X64MainTidLbl.t0_step` is stated at wake's `wakeSrc`, but its proof reads no program: a step replaces a thread
in place or pushes a new one, keeping a set label. `t0_stepP` is the same step lemma at any program;
`reach_t0H` runs it from hello's start `setupStartT 2` (`X64HelloSrc.hello_start`), whose one thread has the
label.

- `t0_stepP`: one source step of any program keeps `X64MainTidLbl.T0`.
- `reach_t0H`: `T0` along every run of `helloS arch`.
- `mainTidLbl_of_reachH`: thread 0 of a one-thread configuration `helloS arch` reaches.

## Differences from the AArch64 version

- None in the proofs: the source machine, its start and `T0` are the x86-64 side's (`X64WakeT1`,
  `X64HelloSrc`, `X64MainTidLbl`), which reach no AArch64 syntax.
-/
import Spike.Lib.Src.X64MainTidLbl
import Spike.Lib.X64HelloSrc

namespace Spike.Lib.X64HelloMainTidLbl

open CoreLang CoreTerm TermRun
open Scc.Sem (SrcSem Ev)
open Spike.Lib.X64WakeT1 (mainTidLbl)
open Spike.Lib.X64MainTidLbl (T0 t0_set)
open Spike.Lib.X64HelloSrc (helloSrc helloS)

/-- **One step of any program's source** keeps `T0` (`X64MainTidLbl.t0_step`'s proof, program-generic). -/
theorem t0_stepP {p : Prog} {arch : WeakMem.Arch} {i : Nat} {c c' : Cfg} {es : List Ev}
    (hs : (SrcSem.sourceG (Spike.Lib.X64WakeT1.srcPo 2 arch p) p).step i c es c') (H : T0 c) : T0 c' := by
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

/-- **`T0` along every run of hello's source** (from `setupStartT 2`). -/
theorem reach_t0H {arch : WeakMem.Arch} {tr : List Ev} {s : Cfg} (h : (helloS arch).Reach tr s) : T0 s := by
  obtain ⟨s0, h0, hr⟩ := h
  have H : T0 s0 := by
    change Spike.Lib.X64WakeT1.progInitT helloSrc 2 s0 at h0
    rw [Spike.Lib.X64HelloSrc.hello_start] at h0
    subst h0
    exact ⟨_, rfl, rfl⟩
  clear h0
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, -, hs⟩ := hs
    exact ih (t0_stepP hs H)

/-- **Main's box label at a one-thread configuration hello's source reaches.** -/
theorem mainTidLbl_of_reachH {arch : WeakMem.Arch} {tr : List Ev} {s : Cfg} {th0 : TTh}
    (h : (helloS arch).Reach tr s) (hs : s.ths = #[th0]) : th0.tidLbl = some (mainTidLbl 2) := by
  obtain ⟨t, h0, hl⟩ := reach_t0H h
  rw [hs] at h0
  cases h0
  exact hl

end Spike.Lib.X64HelloMainTidLbl

/-- info: 'Spike.Lib.X64HelloMainTidLbl.t0_stepP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainTidLbl.t0_stepP

/-- info: 'Spike.Lib.X64HelloMainTidLbl.mainTidLbl_of_reachH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainTidLbl.mainTidLbl_of_reachH
