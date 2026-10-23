/-
**Cells of a laid-out x64 program** (`CellAt`, the hypothesis of every row of
`Lower/EventsX64.lean`), from the directive list: the x64 twin of
`Lower/CodeSegA64.lean`, with cells of any size.

- `cellAt_of_codeAt`: a cell `codeAt` finds at the pc is a `CellAt`, given a
  valid layout and the end address at the end of the text;
- `cellAt_segment`: every cell of a label-free run that `codeAt` finds at
  `pc` is the cell at `pc` plus the sizes of the cells before it.

The index computations are `Kraken/CodeAt.lean`.
-/
import Kraken.Promising.Lower.EventsX64
import Kraken.CodeAt

namespace Kraken.Promising.Lower.X64

open Kraken Kraken.Promising Kraken.Promising.X64

/-- **A cell `codeAt` finds at the pc is a `CellAt`**, when the end address is
the end of the text. -/
theorem cellAt_of_codeAt {st : State} {d : Directive} {sz : Nat} {rest : List (Directive × Nat)}
    (hv : Kraken.Executable.ValidLayout st.exe)
    (hend : st.endPc = st.exe.1 + .ofNat (st.exe.2.map (·.2)).sum)
    (h : Kraken.Executable.codeAt st.exe st.st.2 = (d, sz) :: rest) : CellAt st d sz := by
  refine ⟨hv, ?_, rest, h⟩
  rw [hend]
  exact beq_false_of_ne (Kraken.Executable.codeAt_ne_end st.exe h)

/-- **A label-free run of cells at `pc`**: cell `j` of `cs` is the cell at
`pc` plus the sizes of the cells before it, in any machine data `m`. -/
theorem cellAt_segment {st : State} {pc : Int64} {cs rest : List (Directive × Nat)}
    (hv : Kraken.Executable.ValidLayout st.exe)
    (hend : st.endPc = st.exe.1 + .ofNat (st.exe.2.map (·.2)).sum)
    (h : Kraken.Executable.codeAt st.exe pc = cs ++ rest)
    (hcs : ∀ c ∈ cs, c.1.isLabel = false) {j : Nat} {d : Directive} {sz : Nat} (hd : cs[j]? = some (d, sz))
    (m : MachineData) :
    CellAt { st with st := (m, pc + .ofNat ((cs.take j).map (·.2)).sum) } d sz := by
  have hj : j < cs.length := by
    rcases Nat.lt_or_ge j cs.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hd; cases hd
  have hseg := Kraken.Executable.codeAt_segment st.exe h hcs j hj
  rw [List.drop_eq_getElem_cons hj, List.cons_append,
    show cs[j] = (d, sz) by rw [List.getElem?_eq_getElem hj] at hd; exact Option.some.inj hd] at hseg
  exact cellAt_of_codeAt (st := { st with st := (m, pc + .ofNat ((cs.take j).map (·.2)).sum) }) hv hend hseg

end Kraken.Promising.Lower.X64
