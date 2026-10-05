import Kraken.X64.Examples.EvenOddGhost.Spec

/-!
# `odd`, proved against the spec of `even` at smaller arguments

`odd_spec`: for every `n`, from `EvenSpecBelow n` (the spec of `even` at every
`m < n`, an assumption here; `Link.lean` discharges it), `odd` meets
`OddSpec n`. The mirror image of `Even.lean`; the notes there apply. The
conditions are in `Spec.lean`, sorted into calling convention and semantics.

## What the proof needs beyond the specification

* The placement `PlacedIn odd_body`: the three blocks sit at their labels'
  addresses in the ambient code, and fall through as the text has it. Nothing
  is assumed about where `even` is: the call goes through `even`'s `ProcSpec`,
  which is stated at `even`'s address, whatever it is.
* The table below, one entry per block, as for any procedure. The *own* 24
  bytes of the frame are listed cell by cell, in the layout clang chose
  (`Own`, `OwnCells` in `Spec.lean`); below them sits the reservation for the
  callee, `Reserve (below n) (r - 24)`, passed around whole and opened only
  at the call (`Reserve_below_succ`). Every entry carries `ArgU32 t₀ n`: it
  links the spilled argument to `n` for the callee's argument, and bounds `n`
  for the stack arithmetic.

## How the blocks are discharged

Every block is `vcgen`, then `grind_cells` (the cell rules of `SepCells` and
the `grind` rules of `Spec.lean`), as in the other examples. The call block
has two more steps, both from the shape of `call_proc_spec_at` and the same
at every call site (see `call_simp` in `MachineWP`): `call_simp` reads the
registers and the memory out of the pushed state, and a `refine` opens the
rule's `∀ ra, Pre ∧ ∀ s', Post → wp` so that the second `vcgen` can step
the instructions after the return.

## Safety

Every memory access of the body is to one of those cells or, through the
call, to the callee's reservation; the proof would not go through otherwise.
The `n = 0` case never reaches the call block: its table entry has `n ≠ 0`,
and `jne` is taken only when the argument is nonzero.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.EvenOddGhost

variable [CodeEnv]

/-- The table of `odd` at `n`, for caller's memory `R`, return address `ra`
and entry state `t₀` (`r` its `rsp`). -/
abbrev odd_table (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "odd", s =>
    let r := t₀.regs.get64 .rsp
    s = t₀ ∧ ArgU32 t₀ n
    ∧ (t₀.dmem =⋆ RetCell ra r ⋆ OwnCells r (Reserve (below n) (r - 24) ⋆ R))
  | ".LBB1_2", s =>
    let r := t₀.regs.get64 .rsp
    n ≠ 0 ∧ ArgU32 t₀ n
    ∧ s.regs.get64 .rsp = r - 24 ∧ s.regs.get64 .rbp = r - 8 ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ 1 ?@ (r - 9) ⋆ Own r (t₀.regs.get64 .rbp) ((t₀.regs.get64 .rdi).setWidth 32).toInt
        (RetCell ra r ⋆ (Reserve (below n) (r - 24) ⋆ R)))
  | ".LBB1_3", s =>
    let r := t₀.regs.get64 .rsp
    ArgU32 t₀ n
    ∧ s.regs.get64 .rsp = r - 24 ∧ s.regs.get64 .rbp = r - 8 ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ Int.toBytes 1 ((n % 2 : Nat) : Int) =@ (r - 9)
        ⋆ Own r (t₀.regs.get64 .rbp) ((t₀.regs.get64 .rdi).setWidth 32).toInt
        (RetCell ra r ⋆ (Reserve (below n) (r - 24) ⋆ R)))
  | _, _ => False

-- The blocks walk the frame's cells with `grind`; the default budget does not
-- cover it.
set_option maxHeartbeats 4000000 in
theorem odd_spec (hpl : Program.PlacedIn odd_body) (n : Nat) (ih : EvenSpecBelow n) :
    OddSpec n := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := odd_body) (odd_table n)
    (fun R ra t₀ s => n < 2 ^ 32 ∧ CallPostCells n R ra t₀ s ∧ RetU8 s (n % 2))
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [odd_body]
    · -- entry: prologue, spill, test
      vcgen
      all_goals call_simp
      all_goals grind_cells
    · -- the call: `even` at `n - 1` by its spec; its caller's memory is our cells
      rcases n with _ | k
      · exact Triple.intro fun s h => absurd rfl h.1.1
      · vcgen [MachineWP.call_proc_spec_at
          (1 ?@ (t₀.regs.get64 .rsp - 9) ⋆ Own (t₀.regs.get64 .rsp) (t₀.regs.get64 .rbp)
            ((t₀.regs.get64 .rdi).setWidth 32).toInt (RetCell ra (t₀.regs.get64 .rsp) ⋆ R))
          "even" (ih k (Nat.lt_succ_self k))]
        all_goals call_simp
        all_goals try refine ⟨fun w => ⟨?_, fun s' hpost => ?_⟩, ?_⟩
        all_goals try (vcgen; all_goals call_simp)
        all_goals grind_cells
    · -- the result and the epilogue
      vcgen
      all_goals call_simp
      all_goals grind_cells
  · rintro R ra t ⟨hcall, harg⟩
    exact ⟨rfl, harg, CallPre.cells (ArgU32.lt harg) hcall⟩
  · rintro R ra t₀ s ⟨hn, hcells, hal⟩
    exact ⟨CallPost.of_cells hn hcells, hal⟩

end Kraken.Examples.EvenOddGhost
