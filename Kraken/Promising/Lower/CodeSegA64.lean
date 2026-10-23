/-
**Cells of a laid-out AArch64 program** (`CellAt`, the hypothesis of every
row of `Lower/EventsA64.lean`), from the directive list.

- `cellAt_of_codeAt`: a cell `codeAt` finds at the pc is a `CellAt`, given a
  valid layout and the end address at the end of the text;
- `cellAt_segment4`: every instruction of a label-free run that `codeAt`
  finds at `pc` is the 4-byte cell at `pc + 4j`, in any machine data;
- `mkState_exe`, `mkState_endPc`, `mkState_validLayout`: the layout of
  `Promising.AArch64.mkState` meets these hypotheses.

The index computations are `Kraken/AArch64/WP/CodeAt.lean`.
-/
import Kraken.Promising.Lower.EventsA64
import Kraken.AArch64.WP.CodeAt

namespace Kraken.Promising.Lower.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- **A cell `codeAt` finds at the pc is a `CellAt`**, when the end address is
the end of the text. -/
theorem cellAt_of_codeAt {st : State} {d : Directive} {sz : Nat} {rest : List (Directive × Nat)}
    (hv : Kraken.Executable.ValidLayout st.exe)
    (hend : st.endPc = st.exe.1 + .ofNat (st.exe.2.map (·.2)).sum)
    (h : Kraken.Executable.codeAt st.exe st.st.2 = (d, sz) :: rest) : CellAt st d sz := by
  refine ⟨hv, ?_, rest, h⟩
  rw [hend]
  exact beq_false_of_ne (Kraken.Executable.codeAt_ne_end st.exe h)

/-- **A label-free run of instructions at `pc`**: instruction `j` of `ds` is
the 4-byte cell at `pc + 4j`, in any machine data `m`. -/
theorem cellAt_segment4 {st : State} {pc : Int64} {ds : List Directive} {rest : List (Directive × Nat)}
    (hv : Kraken.Executable.ValidLayout st.exe)
    (hend : st.endPc = st.exe.1 + .ofNat (st.exe.2.map (·.2)).sum)
    (h : Kraken.Executable.codeAt st.exe pc = ds.map (·, 4) ++ rest)
    (hds : ∀ d ∈ ds, d.isLabel = false) {j : Nat} {d : Directive} (hd : ds[j]? = some d)
    (m : MachineData) : CellAt { st with st := (m, pc + .ofNat (4 * j)) } d 4 := by
  have hj : j < ds.length := by
    rcases Nat.lt_or_ge j ds.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hd; cases hd
  have hseg := Kraken.Executable.codeAt_segment4 st.exe h hds j hj
  rw [List.drop_eq_getElem_cons hj, List.map_cons, List.cons_append,
    show ds[j] = d by rw [List.getElem?_eq_getElem hj] at hd; exact Option.some.inj hd] at hseg
  exact cellAt_of_codeAt (st := { st with st := (m, pc + .ofNat (4 * j)) }) hv hend hseg

end Kraken.Promising.Lower.A64

namespace Kraken.Promising.AArch64

/-- `mkState`'s executable: the program at `0x100000 * (tid + 1)`, each
directive its `fakeSize`. -/
theorem mkState_exe (tid : Nat) (prog : Program) (regs : Reg64s) (dmem : DataMem) (texts : List String)
    (decls : Decls) :
    (mkState tid prog regs dmem texts decls).exe =
      (Int64.ofNat (0x100000 * (tid + 1)), prog.map fun d => (d, d.fakeSize)) :=
  Kraken.Layout.ofSize_apply _ Directive.fakeSize prog

/-- `mkState` starts at the start of its text. -/
theorem mkState_pc (tid : Nat) (prog : Program) (regs : Reg64s) (dmem : DataMem) (texts : List String)
    (decls : Decls) :
    (mkState tid prog regs dmem texts decls).st.2 = (mkState tid prog regs dmem texts decls).exe.1 := by
  rw [mkState_exe]; rfl

/-- `mkState`'s end address is the end of its text. -/
theorem mkState_endPc (tid : Nat) (prog : Program) (regs : Reg64s) (dmem : DataMem) (texts : List String)
    (decls : Decls) :
    (mkState tid prog regs dmem texts decls).endPc =
      (mkState tid prog regs dmem texts decls).exe.1 +
        .ofNat ((mkState tid prog regs dmem texts decls).exe.2.map (·.2)).sum := by
  rw [mkState_exe, List.map_map]
  rfl

/-- `mkState`'s layout is valid when no data directive is empty and the text
fits the address space (both decidable). -/
theorem mkState_validLayout (tid : Nat) (prog : Program) (regs : Reg64s) (dmem : DataMem)
    (texts : List String) (decls : Decls)
    (hdata : ∀ d ∈ prog, d.isLabel = false → 0 < d.fakeSize)
    (hwrap : (prog.map Directive.fakeSize).sum < 2 ^ 64) :
    Kraken.Executable.ValidLayout (mkState tid prog regs dmem texts decls).exe :=
  Kraken.Executable.validLayout_ofSize_fakeSize _ prog hdata hwrap

end Kraken.Promising.AArch64
