/-
**Stage 3: `Progressive` along a state map**, for
the runner starts (threads with declarations `decls = ds`). ISA-neutral.

The per-lock invariants behind `Witness.progressive_of_inv` assume
`decls = {}`. The runner's threads carry declarations; `LiveRunnerSim.lean`
relates them to declaration-free threads by a map `f` (`State.noDecls`) that
commutes with `exec` on a step-closed set `G` (`RunnerSim.ExecSim`). This file
transfers `Progressive` (executable machine, newest-reading promise-free
steps) from the mapped start configuration back to the original:

- `reachPI_mapC`: a configuration reachable by newest-reading promise-free
  steps stays `GoodC G`, and its map is reachable from the mapped start;
- **`progressive_of_mapC`**: `Progressive A (mapC f c0)` gives
  `Progressive A c0` (a `GoodT` outcome of the mapped thread is the map of a
  `GoodT` outcome of the thread: same promises, views and reads);
- `startPF_of_goodC`.

With `Witness.fair_exists` / `fairSem_exists` this gives the fair traces
from the runner starts (`LiveSemWitnessX64.lean`, `LiveSemWitnessTicketAl.lean`,
`LiveSemWitnessA64Runner.lean`).
-/
import Kraken.Promising.LiveSemWitness
import Kraken.Promising.LiveRunnerSim

namespace Kraken.Promising.Live.Witness

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.RunnerSim

variable {I : ISA} {f : I.State → I.State} {G : I.State → Prop}

theorem startPF_of_goodC {c0 : Config I} (hg0 : GoodC G c0) : StartPF c0 :=
  fun tid t h => (hg0 tid t h).2

/-- A configuration reachable by newest-reading promise-free steps from a
`GoodC G` start is `GoodC G`, and its map is reachable from the mapped
start. -/
theorem reachPI_mapC (hS : ExecSim f G) {A : Arch} {c0 c : Config I} (hg0 : GoodC G c0)
    (h : ReachPI A c0 c) : GoodC G c ∧ ReachPI A (mapC f c0) (mapC f c) := by
  induction h with
  | refl => exact ⟨hg0, .refl⟩
  | @step c tid t outs o _ ht hs ho hp ih =>
    obtain ⟨hG, -⟩ := ih.1 tid t ht
    refine ⟨goodC_step hS ih.1 ⟨t, outs, o, ht, hs, ho, rfl⟩, ?_⟩
    rw [mapC_withThread]
    exact .step (t := mapT f t) (o := mapO f o) ih.2 (by simp [ht]) (by rw [mapC_mem, stepOne_mapT hS A hG, hs]; rfl)
      (List.mem_map.mpr ⟨_, ho, rfl⟩) hp

/-- **`Progressive` transfers back along the map** (executable machine). -/
theorem progressive_of_mapC (hS : ExecSim f G) {A : Arch} {c0 : Config I} (hg0 : GoodC G c0)
    (hP : Progressive A (mapC f c0)) : Progressive A c0 := by
  intro c hr tid t ht hh
  obtain ⟨hg, hr'⟩ := reachPI_mapC hS hg0 hr
  obtain ⟨hG, -⟩ := hg tid t ht
  obtain ⟨o', outs', hs', ho', hp', hc'⟩ :=
    hP _ hr' tid (mapT f t) (by simp [ht]) (by rw [halted_mapT hS hG]; exact hh)
  obtain ⟨outs, o, hs, ho, rfl⟩ := ok_mem_mapT hS hG hs' ho'
  refine ⟨o, outs, hs, ho, hp', fun l hm ts w hw hl => hc' l ?_ ts w hw hl⟩
  obtain ⟨mem, outs1, o1, h1, h2, h3⟩ := hm
  exact ⟨mem, _, mapO f o1, by rw [stepOne_mapT hS A hG, h1]; rfl, List.mem_map.mpr ⟨_, h2, rfl⟩, h3⟩

end Kraken.Promising.Live.Witness
