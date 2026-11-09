import Spike.Gen.GenOffsA64

/-!
# The single instructions' generator at work (AArch64)

`Spike.Gen.OffsA64.evOf` on a hand-made run, and `evsOf` on `ret0.w`'s
table: a generator that writes no single instruction (or all of them)
fails these.
-/

namespace Spike.Test.GenOffsA64

open Kraken.Promising.AArch64 Scc.Cert.Rt.A64 Spike.Gen.OffsA64

/-- Some instruction (the first of `ret0.w`'s program). -/
def c : Directive := (SccCode.ret0Prog.find? isIns).getD (.label "none")

#guard isIns c

/-- A run of four instructions after `L`, then `M`'s. -/
def cells : List Directive := [.label "L", c, c, c, c, .label "M", c]

/- One row over instructions 1–2 of `L`'s run: the single instructions are
0 and 3; `M`'s instruction is not in `L`'s run. -/
#guard evOf cells ⟨"L", [(1, [c, c])]⟩ == [0, 3]
/- No row: the whole run. -/
#guard evOf cells ⟨"L", []⟩ == [0, 1, 2, 3]
/- Rows tiling the run: none. -/
#guard evOf cells ⟨"L", [(0, [c]), (1, [c, c, c])]⟩ == []
/- `M`'s run is one instruction; a label not in the cells has none. -/
#guard evOf cells ⟨"M", []⟩ == [0]
#guard evOf cells ⟨"N", []⟩ == []

/- `ret0.w`: one list per group, some nonempty, and every index within its
label's run. -/
#guard (evsOf SccCode.ret0Prog SccCode.ret0T).length == SccCode.ret0T.length
#guard (evsOf SccCode.ret0Prog SccCode.ret0T).any (· ≠ [])
#guard (SccCode.ret0T.zip (evsOf SccCode.ret0Prog SccCode.ret0T)).all fun (g, e) =>
  e.all fun i => i < (((after g.l SccCode.ret0Prog).map insRun).getD []).length

end Spike.Test.GenOffsA64
