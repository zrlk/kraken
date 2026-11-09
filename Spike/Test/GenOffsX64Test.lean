import Spike.Gen.GenOffsX64

/-!
# The single instructions' generator at work (x64)

`Spike.Gen.OffsX64.evOf` on a hand-made run, and `evsOf` on `ret0.w`'s
table: a generator that writes no single instruction (or all of them)
fails these.
-/

namespace Spike.Test.GenOffsX64

open Kraken.Promising.X64 Scc.Cert.Rt.X64 Spike.Gen.OffsX64

/-- Some instruction cell (the first of `ret0.w`'s code). -/
def c : Directive × Nat := (SccCode.ret0Cells.find? notLab).getD (.label "none", 0)

#guard notLab c

/-- A run of four cells after `L`, then `M`'s. -/
def cells : List (Directive × Nat) := [(.label "L", 0), c, c, c, c, (.label "M", 0), c]

/- One row over cells 1–2 of `L`'s run: the single instructions are 0 and
3; `M`'s cell is not in `L`'s run. -/
#guard evOf cells ⟨"L", [(1, 0, [c, c])]⟩ == [0, 3]
/- No row: the whole run. -/
#guard evOf cells ⟨"L", []⟩ == [0, 1, 2, 3]
/- Rows tiling the run: none. -/
#guard evOf cells ⟨"L", [(0, 0, [c]), (1, 0, [c, c, c])]⟩ == []
/- `M`'s run is one cell; a label not in the cells has none. -/
#guard evOf cells ⟨"M", []⟩ == [0]
#guard evOf cells ⟨"N", []⟩ == []

/- `ret0.w`: one list per group, some nonempty, and every index within its
label's run. -/
#guard (evsOf SccCode.ret0Cells SccCode.ret0T).length == SccCode.ret0T.length
#guard (evsOf SccCode.ret0Cells SccCode.ret0T).any (· ≠ [])
#guard (SccCode.ret0T.zip (evsOf SccCode.ret0Cells SccCode.ret0T)).all fun (g, e) =>
  e.all fun i => i < (((after g.l SccCode.ret0Cells).map cellRun).getD []).length

end Spike.Test.GenOffsX64
