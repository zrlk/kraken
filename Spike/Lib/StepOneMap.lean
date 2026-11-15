/-
**One instruction of a thread under a state map, at one state**
(ISA-neutral). `Kraken/Promising/LiveRunnerSim.lean`'s `stepOne_mapT` asks
the map to commute with `exec` on a step-closed set of states (`ExecSim`);
the post-pass transfer relabels states whose leaves leave that set (they
may stop at a system call or at the end), so `stepOne_map` asks it only at
the thread's own state.
-/
import Kraken.Promising.LiveRunnerSim

namespace Spike.Lib.StepOneMap

open Kraken Kraken.Promising Kraken.Promising.Live.RunnerSim

variable {I : ISA}

/-- **One instruction of a mapped thread is the instruction, mapped**, when
`exec`, the register dependencies and the instruction's text commute with
the map at the thread's state. -/
theorem stepOne_map (A : Arch) {f : I.State → I.State} {t : Thread I}
    (hex : I.exec (f t.st) = (I.exec t.st).map (EvTree.map f)) (hd : I.deps (f t.st) = I.deps t.st)
    (hsh : I.showInstr (f t.st) = I.showInstr t.st) (tid : Nat) (mem : Memory) :
    stepOne A (mapT f t) tid mem = (stepOne A t tid mem).map (List.map (Except.map (mapO f))) := by
  simp only [stepOne, mapT_st, hex, hd, hsh, instrViews_mapT]
  cases I.exec t.st with
  | none => rfl
  | some tree =>
    show some _ = some _
    rw [runTree_map, List.flatMap_map, List.map_flatMap]
    simp only [mapT_views, mapT_prom]
    refine congrArg (fun g => some (List.flatMap g _)) (funext fun x => ?_)
    rcases x with m | ⟨st, c'⟩
    · rfl
    · simp only [Except.map, List.map_map]
      rw [finishInstr_mapT _ f t (mapT f t) rfl rfl, List.map_map]
      rfl

/-- **The outcomes of a mapped thread are the mapped outcomes** (at one
state, as `stepOne_map`). -/
theorem ok_mem_map {A : Arch} {f : I.State → I.State} {t : Thread I}
    (hex : I.exec (f t.st) = (I.exec t.st).map (EvTree.map f)) (hd : I.deps (f t.st) = I.deps t.st)
    (hsh : I.showInstr (f t.st) = I.showInstr t.st) {tid : Nat} {mem : Memory}
    {outs' : List (Except String (Outcome I))} (hs : stepOne A (mapT f t) tid mem = some outs')
    {o' : Outcome I} (ho : .ok o' ∈ outs') :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o' = mapO f o := by
  rw [stepOne_map A hex hd hsh] at hs
  cases h : stepOne A t tid mem with
  | none => rw [h] at hs; cases hs
  | some outs =>
    rw [h] at hs
    cases hs
    obtain ⟨x, hx, he⟩ := List.mem_map.1 ho
    rcases x with m | o
    · cases he
    · exact ⟨outs, o, rfl, hx, by cases he; rfl⟩

end Spike.Lib.StepOneMap

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.StepOneMap.stepOne_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.StepOneMap.stepOne_map

/-- info: 'Spike.Lib.StepOneMap.ok_mem_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.StepOneMap.ok_mem_map
