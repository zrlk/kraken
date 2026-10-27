import WeakCore.TermLiveCertRun
import WeakCore.TermLiveL3
/-! # TermLiveCertScen — item 38 v1: scenario starts are coherent

`check`'s theorems take `CfgCoh c0`.  A scenario start (`ScenarioStartK`, the real `spawnS` start) has it:
`InitOK` gives a coherent pre-spawn configuration, `TermStep.Steps` keeps coherence, and `spawnS` copies thread 0's
views into each kid. -/

namespace TermLiveCert
open CoreLang CoreTerm TermRun TermLiveProps TermLiveL3

theorem steps_coh {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c c' : Cfg}
    (h : TermStep.Steps p k arch c c') (hc : CfgCoh c) : CfgCoh c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (Step_coh hs hc).1

theorem cfgCoh_spawnS {cs : Cfg} {res : List Word} {kids : List TermSpawn.Kid} (hc : CfgCoh cs) :
    CfgCoh (TermSpawn.spawnS cs res kids) := by
  unfold TermSpawn.spawnS
  split
  · exact hc
  · rename_i th hth
    intro i t ht
    simp only [List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
    obtain ⟨kd, -, rfl⟩ := ht
    exact hc 0 th hth

/-- **A scenario start is coherent**, so `check`'s theorems apply at it. -/
theorem cfgCoh_scenario {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Init : TermSound.Res}
    {kids : List TermSpawn.Kid} {c0 : Cfg} (hS : ScenarioStartK p k arch Init kids c0) : CfgCoh c0 := by
  obtain ⟨cpre, cs, _, th, _, _, _, _, _, res, _, _, h3, _, _, _, _, _, _, _, _, h12, _, _, _, _, _, _, _, _, rfl⟩ := hS
  exact cfgCoh_spawnS (steps_coh h12 h3.2.2)

end TermLiveCert
#print axioms TermLiveCert.cfgCoh_scenario
