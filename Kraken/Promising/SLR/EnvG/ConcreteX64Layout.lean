/-
**The `.kl` runner's x64 text layout, generically**.

Text laid out as the `.kl` runner lays it out
(`Kraken.Litmus.X64.prepareProgram`: labels 0 bytes, every other directive 1,
as `SLR/X64SpinConcrete.lean`):

- `klLayout p start`: that layout for any program `p` at `start`;
- `cellOk`, `validLayout_of_cells`: `Executable.ValidLayout` from a decidable
  check of the cells (labels 0 bytes, everything else at least 1, no
  alignment directive, total size below `2 ^ 64`).

Users: `EnvG/ConcreteX64.lean`, `EnvG/X64TakeMpConcrete.lean`.
-/
import Kraken.X64.Syntax
import Kraken.SegmentExtract

namespace Kraken.Promising.X64.EnvG.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64

/-! ## The `.kl` runner's layout, generically -/

/-- The text layout of the `.kl` runner for `p` at `start`: labels 0 bytes,
every other directive 1. -/
@[reducible] def klLayout (p : Program) (start : Int64) : _root_.Layout :=
  { start := start,
    size := fun i => match p[i]? with
      | some (.label _) => 0
      | some _ => 1
      | none => 0 }

/-- The size check of a cell: labels 0 bytes, everything else at least 1, no
alignment directive. -/
def cellOk : Directive × Nat → Bool
  | (.label _, z) => z == 0
  | (.instr (.regular _ _ (.nopalign _ _)), _) => false
  | (_, z) => 0 < z

/-- `Executable.ValidLayout` from a decidable check of the cells. -/
theorem validLayout_of_cells (e : Kraken.Executable Directive) (hc : e.2.all cellOk = true)
    (hw : (e.2.map (·.2)).sum < 2 ^ 64) : Executable.ValidLayout e := by
  have hok : ∀ {i d z}, e.2[i]? = some (d, z) → cellOk (d, z) = true := fun h =>
    List.all_eq_true.mp hc _ (List.mem_of_getElem? h)
  refine ⟨fun i l z h => by simpa [cellOk] using hok h, fun i d z h hd => ?_, hw,
    fun i aw w n pad z h => by simpa [cellOk] using hok h⟩
  have := hok h
  cases d with
  | label l => exact absurd rfl (hd l)
  | instr ins =>
    cases ins with
    | regular aw w op => cases op <;> simp_all [cellOk]
    | avx => simp_all [cellOk]
  | byteArray => simp_all [cellOk]

end Kraken.Promising.X64.EnvG.Concrete
