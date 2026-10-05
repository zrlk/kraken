import Kraken.MachineWP
import Kraken.SepCells

/-!
# Procedures under the SysV x86-64 calling convention

What a procedure specification (`ProcSpec`, `ProcSpecK` in `MachineWP`) says
about the stack and the registers when the code follows the SysV convention,
stated once for every procedure:

* `RetCell ra a`: the return address `ra` at `a` (`[rsp]` on entry);
* `Reserve d r`: `d` bytes of free stack below `r`, the procedure's *stack
  reservation* (Bedrock's `reserving` clause): the caller supplies it, the
  procedure may use it, and it comes back as owned bytes. The amount is a
  parameter; a recursive procedure exports it as a function of its argument
  (`need` in the `EvenOdd*` examples). It is exact, not "at least": a caller
  with more stack frames the excess off with `Reserve.excess`, so that the
  reservation is one cell the rules of `SepCells` move around whole;
* `SavedRegs t s`: the callee-saved registers other than `rbp` as they were;
* `CallPre d R ra t`, `CallPost d R ra t s`: the convention's share of a
  procedure's pre- and postcondition with caller's memory `R`; a procedure's
  specification is these plus its semantics (`ArgU32`, `RetU8` for the
  register conventions of `unsigned`/`bool`, and whatever it computes).

Kraken has no faulting model, so stack exhaustion cannot be a runtime error;
the reservation in the precondition is the only sound treatment. A tail call
is a run that reaches `ra` through the callee, so it is covered by the
callee's spec at the same `ra` and needs nothing here; a convention that
hands over `ra` or the frame differently (a segmented stack, a link register)
would replace `RetCell`/`Reserve` by its own cells and keep the rest.
-/

open Mem
open Std.ExtHashMap

namespace Kraken.SysV

/-- The bytes a return address occupies: the slot at `a` holds `ra`, as the
`call` wrote it. -/
abbrev RetCell (ra : Int64) (a : BitVec 64) : Mem 64 → Prop :=
  Int.toBytes 8 ra.toBitVec.toInt =@ a

/-- `d` bytes of free stack just below `r`: a procedure's stack reservation.
A `def`, so that `grind` moves it as one cell (`Split.here_reserve`). -/
def Reserve (d : Nat) (r : BitVec 64) : Mem 64 → Prop := d ?@ (r - .ofNat 64 d)

/-- The reservation, with `a` bytes carved off its top: the rest is a smaller
reservation `a` bytes lower. The one lemma the stack discipline needs, at a
procedure's entry (its own bytes off the top), at a call (the return address
slot off what is left), and in reverse at its exit. -/
theorem Reserve_split (a d : Nat) (r : BitVec 64) (h : a + d ≤ 2 ^ 64) :
    Reserve (a + d) r = a ?@ (r - .ofNat 64 a) ⋆ Reserve d (r - .ofNat 64 a) := by
  unfold Reserve
  rw [Block.split_at (r - BitVec.ofNat 64 (a + d)) (a + d) d (by omega) h, sep_comm]
  have e1 : r - BitVec.ofNat 64 (a + d) + BitVec.ofNat 64 d = r - BitVec.ofNat 64 a := by
    bv_omega
  have e2 : r - BitVec.ofNat 64 a - BitVec.ofNat 64 d = r - BitVec.ofNat 64 (a + d) := by
    bv_omega
  rw [e1, e2, Nat.add_sub_cancel]

/-- A caller with `d'` bytes where `d` are needed: the excess sits below. -/
theorem Reserve.excess (d d' : Nat) (r : BitVec 64) (h : d ≤ d') (hw : d' ≤ 2 ^ 64) :
    Reserve d' r = Reserve d r ⋆ (d' - d) ?@ (r - .ofNat 64 d') := by
  have := Reserve_split d (d' - d) r (by omega)
  rw [Nat.add_sub_cancel' h] at this
  rw [this]
  unfold Reserve
  have e : r - BitVec.ofNat 64 d - BitVec.ofNat 64 (d' - d) = r - BitVec.ofNat 64 d' := by
    bv_omega
  rw [e]

/-- A reservation is a head the cell rules can pull out of a tree: the
callee's stack moves between the caller's tree and the callee's specification
whole. -/
theorem Split.here_reserve (d : Nat) (r : BitVec 64) (R : Mem 64 → Prop) :
    Split (Reserve d r) R (Reserve d r ⋆ R) := Split.here _ _

grind_pattern Split.here_reserve => sep (Reserve d r) R

/-- The callee-saved registers other than `rbp` (which a frame-pointer
prologue moves and the epilogue restores) hold their entry values. -/
abbrev SavedRegs (t s : MachineData) : Prop :=
  s.regs.get64 .rbx = t.regs.get64 .rbx
  ∧ s.regs.get64 .r12 = t.regs.get64 .r12 ∧ s.regs.get64 .r13 = t.regs.get64 .r13
  ∧ s.regs.get64 .r14 = t.regs.get64 .r14 ∧ s.regs.get64 .r15 = t.regs.get64 .r15

/-- The convention's share of a procedure's precondition, with caller's memory
`R`: the return address on the stack, and `d` bytes reserved below it. -/
abbrev CallPre (d : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  t.dmem =⋆ RetCell ra (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R)

/-- The convention's share of a procedure's postcondition: the return address
popped, `rbp` and the callee-saved registers as they were, the reservation and
the slot given back. -/
abbrev CallPost (d : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.get64 .rsp = t.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t.regs.get64 .rbp ∧ SavedRegs t s
  ∧ (s.dmem =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R))

/-- An `unsigned` argument: the low 32 bits of `rdi`. -/
abbrev ArgU32 (t : MachineData) (n : Nat) : Prop := (t.regs.get64 .rdi).toNat % 2 ^ 32 = n

/-- A `bool`/byte result in `al` — all 8 bits of it. -/
abbrev RetU8 (s : MachineData) (v : Nat) : Prop := (s.regs.get64 .rax).toNat % 256 = v

end Kraken.SysV

/-- The `grind` call that walks a frame of cells: more E-matching rounds than
the default (a chain of `Split`s per cell), and without the two `toInt`
lemmas, which only add case splits. -/
macro "grind_cells" : tactic =>
  `(tactic| grind (ematch := 20) (gen := 20) (instances := 5000)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])
