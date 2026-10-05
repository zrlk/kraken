import Kraken.X64.Examples.EvenOddGhost.Spec

/-!
# `even`, proved against the spec of `odd` at smaller arguments

`even_spec`: for every `n`, from `OddSpecBelow n` (the spec of `odd` at every
`m < n`, an assumption here; `Link.lean` discharges it), `even` meets
`EvenSpec n`. The conditions are in `Spec.lean`, sorted into calling
convention and semantics; see its header.

## What the proof needs beyond the specification

* The placement `PlacedIn even_body`: the three blocks sit at their labels'
  addresses in the ambient code, and fall through as the text has it. Nothing
  is assumed about where `odd` is: the call goes through `odd`'s `ProcSpec`,
  which is stated at `odd`'s address, whatever it is.
* The table below. The *own* 24 bytes of the frame are listed cell by cell,
  in the layout clang chose: the saved `rbp` at `r - 8`, the `bool` local at
  `r - 9`, 3 bytes of padding, the spilled argument at `r - 16`, 8 unused
  bytes at `r - 24` (`r` the entry `rsp`). The cell rules match stores and
  loads to exact cells, so the split is done once, at the entry. Below the
  own bytes sits the reservation for the callee, `Reserve (below n) (r - 24)`,
  passed around whole and opened only at the call (`Reserve_below_succ`).
* Every entry carries `rdi₀.toNat % 2^32 = n`: it links the spilled argument
  to `n` for the callee's argument, and bounds `n` for the stack arithmetic.

## Safety

Every memory access of the body is to one of those cells or, through the
call, to the callee's reservation; the proof would not go through otherwise.
The `n = 0` case never reaches the call block: its table entry has `n ≠ 0`,
and `jne` is taken only when the argument is nonzero.
-/

open Kraken.X64.Parser
open Kraken
open Std.WP
open Mem
open MachineWP

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.EvenOddGhost

variable [CodeEnv]

/-- The table of `even` at `n`, for caller's memory `R`, return address `ra`
and entry state `t₀` (`r` its `rsp`). -/
abbrev even_table (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "even", s =>
    let r := t₀.regs.get64 .rsp
    s = t₀ ∧ (t₀.regs.get64 .rdi).toNat % 2 ^ 32 = n
    ∧ (t₀.dmem =⋆ RetCell ra r ⋆ OwnCells r (Reserve (below n) (r - 24) ⋆ R))
  | ".LBB0_2", s =>
    let r := t₀.regs.get64 .rsp
    n ≠ 0 ∧ (t₀.regs.get64 .rdi).toNat % 2 ^ 32 = n
    ∧ s.regs.get64 .rsp = r - 24 ∧ s.regs.get64 .rbp = r - 8 ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ 1 ?@ (r - 9) ⋆ Own r (t₀.regs.get64 .rbp) ((t₀.regs.get64 .rdi).setWidth 32).toInt
        (RetCell ra r ⋆ (Reserve (below n) (r - 24) ⋆ R)))
  | ".LBB0_3", s =>
    let r := t₀.regs.get64 .rsp
    (t₀.regs.get64 .rdi).toNat % 2 ^ 32 = n
    ∧ s.regs.get64 .rsp = r - 24 ∧ s.regs.get64 .rbp = r - 8 ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ Int.toBytes 1 (((n + 1) % 2 : Nat) : Int) =@ (r - 9)
        ⋆ Own r (t₀.regs.get64 .rbp) ((t₀.regs.get64 .rdi).setWidth 32).toInt
        (RetCell ra r ⋆ (Reserve (below n) (r - 24) ⋆ R)))
  | _, _ => False

/-- The `grind` call of every obligation: the cell rules need several rounds
of E-matching; the two `toInt` lemmas only add case splits. -/
macro "even_grind" : tactic =>
  `(tactic| grind (ematch := 20) (gen := 20) (instances := 5000)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

-- The entry and exit blocks walk the frame's cells under `sym`; the default budget
-- does not cover it.
set_option maxHeartbeats 2000000 in
theorem even_spec (hpl : Program.PlacedIn even_body) (n : Nat) (ih : OddSpecBelow n) :
    EvenSpec n := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := even_body) (even_table n)
    (fun R ra t₀ s => n < 2 ^ 32 ∧ CallPostCells n R ra t₀ s
      ∧ (s.regs.get64 .rax).toNat % 256 = (n + 1) % 2)
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [even_body]
    · -- entry: prologue, spill, test
      clear ih
      sym (ematch := 20) (gen := 20) (instances := 5000)
        [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod] => vcgen <;> finish
    · -- the call: `odd` at `n - 1` by its spec; its caller's memory is our cells
      rcases n with _ | k
      · exact Triple.intro fun s h => absurd rfl h.1.1
      · have hc := MachineWP.call_proc_spec_at
          (1 ?@ (t₀.regs.get64 .rsp - 9) ⋆ Own (t₀.regs.get64 .rsp) (t₀.regs.get64 .rbp)
            ((t₀.regs.get64 .rdi).setWidth 32).toInt (RetCell ra (t₀.regs.get64 .rsp) ⋆ R))
          "odd" (ih k (by omega))
        clear ih
        vcgen [hc]
        -- `vcgen` leaves the table entry as an unreduced `match` and the state as a
        -- literal; `grind` does better with the entry taken apart, the state
        -- computed (`simp only`), and only the hypotheses a conjunct needs.
        · -- the load of the spilled argument
          clear hc hpl
          rename_i htab
          obtain ⟨-, -, -, hrbp, -, hmem⟩ := htab.1
          even_grind
        · clear hc hpl
          rename_i htab x hx
          obtain ⟨-, hn, hrsp, hrbp, hsv, hmem⟩ := htab.1
          have hk : k < 2 ^ 32 := by omega
          refine ⟨fun w => ⟨⟨⟨?_, ?_⟩, hk⟩, ?_⟩, ?_⟩
          · -- the callee's stack: the slot the call writes, then its reservation
            clear hsv hx hn hrbp
            simp only [MachineData.dmem_pushRa, MachineData.get64_pushRa, Reg64s.get64_set64,
              reduceCtorEq, ite_true, ite_false, hrsp]
            even_grind
          · -- the callee's argument: `edi = n - 1`, read back from the spill
            clear hsv hrsp
            simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true,
              ite_false]
            even_grind
          · -- after the return: the rest of the block
            intro s' hpost
            obtain ⟨⟨hrsp', hrbp', hsv', hmem'⟩, hal⟩ := hpost
            clear hx
            simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true,
              ite_false, hrsp, hrbp] at hrsp' hrbp' hsv' hmem'
            vcgen
            · -- the store of the result is to the `bool` cell
              clear hsv hsv' hn
              even_grind
            · simp only []
              refine ⟨⟨hn, ?_, ?_, ?_, ?_⟩, Nat.zero_le _⟩
              · even_grind
              · even_grind
              · even_grind
              · clear hsv hsv' hn
                even_grind
          · -- the slot the call writes is mapped
            clear hsv hx hrbp hn
            simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp]
            even_grind
    · -- the result and the epilogue
      clear ih
      sym (ematch := 20) (gen := 20) (instances := 5000)
        [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod] => vcgen <;> finish
  · rintro R ra t ⟨hpre, hn⟩
    exact ⟨rfl, hpre.2, hpre.cells hn⟩
  · rintro R ra t₀ s ⟨hn, hcells, hal⟩
    exact ⟨CallPost.of_cells hn hcells, hal⟩

end Kraken.Examples.EvenOddGhost
