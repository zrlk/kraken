/-
`ValidLayout` for the fixed-size layouts `Kraken.Layout.ofSize`: with
`Directive.fakeSize` (instructions 4 bytes, labels 0, data its length), the
layout of a program is valid when no data directive is empty and the program
fits in the address space. Both conditions are decidable, so a concrete
program discharges them by `decide`.
-/
import Kraken.AArch64.WP.SegmentExtract

namespace Kraken.Executable

/-- **The fixed-size layout of a program is valid** (`Directive.fakeSize`, the
sizes of the runners and the litmus driver), at any start address. -/
theorem validLayout_ofSize_fakeSize (start : Int64) (prog : Program)
    (hdata : ∀ d ∈ prog, d.isLabel = false → 0 < d.fakeSize)
    (hwrap : (prog.map Directive.fakeSize).sum < 2 ^ 64) :
    ValidLayout (Kraken.Layout.ofSize start Directive.fakeSize prog prog) := by
  rw [Kraken.Layout.ofSize_apply]
  have hget : ∀ (i : Nat) d z, (prog.map fun d => (d, d.fakeSize))[i]? = some (d, z) → d ∈ prog ∧ z = d.fakeSize := by
    intro i d z h
    rw [List.getElem?_map] at h
    obtain ⟨d', hd', he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact ⟨List.mem_of_getElem? hd', rfl⟩
  refine ⟨fun i l z h => ?_, fun i ins z h => ?_, fun i a z h => ?_, ?_⟩
  · rw [(hget i _ z h).2]; rfl
  · rw [(hget i _ z h).2]; rfl
  · obtain ⟨hm, rfl⟩ := hget i _ z h
    exact hdata _ hm rfl
  · show ((prog.map fun d => (d, d.fakeSize)).map (·.2)).sum < 2 ^ 64
    rw [List.map_map]
    exact hwrap

end Kraken.Executable
