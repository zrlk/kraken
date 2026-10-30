import Spike.Test.WakeLinkedA64

/-!
# `wake.w` on AArch64: the counters' layout facts at `Λe`

`PlaceW` does not place the runtime's counters (`scc_rt_pinned_next`,
`scc_rt_stack_lock`, `scc_rt_stack_free_n`, `scc_rt_stack_next`). A8's
`wordOk` puts their bytes in `.data` or in the pinned region. So the facts
below are facts of the concrete layout `Le`, decided here on the linked ELF, one word at a time (the
whole list in one `decide +kernel` exceeds 4 GB):

* `hctrD_e`: the counters lie in `.data`. In `wake.s` they are `.bss` words
  below `scc_rt_heap`. This is `StartPlaceLy.hctr2_of_data`'s `hctrD`
  (`Spike/Lib/A64WakeStartPlaceLy.lean`).
* `hctr2_e`: the counters are not the second TCB's limit word
  `lim2A = pinA + 112`. This is `StartPlace.wake_start_wc_place`'s `hctr2`,
  decided directly.

* `hA13_e`: A13's data part (`Scc.Cert.Spawn.A64.a13data`) at `Le`:
  `scc_rt_nthreads` a decided word off the runtime's words. This is
  `StartPlaceLy.wsep_W`'s `hA13`, which `PlaceW` lacks.

`hpin2` at `Le` is `WakeLinkedA64.hpin2`.
-/

namespace Spike.Test.WakeLinkedA64

/-- **The counters lie in `.data`** at `Le` (`hctrD`). -/
theorem hctrD_e : ∀ a ∈ [Le.pnA, Le.lockA, Le.freeNA, Le.nextA], Le.Λ.data.contains a.toNat := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The counters are not the second limit word** at `Le` (`hctr2`). -/
theorem hctr2_e : ∀ a ∈ [Le.pnA, Le.lockA, Le.freeNA, Le.nextA], a ≠ Spike.Lib.WakeGOf2.lim2A Le := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **A13's data part** at `Le` (`hA13`). -/
theorem hA13_e : Scc.Cert.Spawn.A64.a13data Le.Λ SccCertificate.outLit.prog SccCertificate.outLit.secs = true := by
  decide +kernel

end Spike.Test.WakeLinkedA64

/-- info: 'Spike.Test.WakeLinkedA64.hctrD_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedA64.hctrD_e

/-- info: 'Spike.Test.WakeLinkedA64.hctr2_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedA64.hctr2_e

/-- info: 'Spike.Test.WakeLinkedA64.hA13_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedA64.hA13_e
