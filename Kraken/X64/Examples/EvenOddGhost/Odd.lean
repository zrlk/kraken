import Kraken.X64.Examples.EvenOddGhost.Spec

/-!
# `odd`, proved against the spec of `even` at smaller arguments

`odd_spec`: for every `n`, from `EvenSpecBelow n` (the spec of `even` at every
`m < n`, an assumption here; `Link.lean` discharges it), `odd` meets
`OddSpec n`. The mirror of `Even.lean`: the base case stores `0`, the call
goes to `even`, and the result is `n % 2`. See `Even.lean` for what the proof
needs beyond the specification and for the safety notes; they hold here
unchanged.
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

/-- The table of `odd` at `n`, for caller's memory `R`, return address `ra`
and entry state `t₀` (`r` its `rsp`). -/
abbrev odd_table (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "odd", s =>
    let r := t₀.regs.get64 .rsp
    s = t₀ ∧ (t₀.regs.get64 .rdi).toNat % 2 ^ 32 = n
    ∧ (t₀.dmem =⋆ RetCell ra r ⋆ OwnCells r (Reserve (below n) (r - 24) ⋆ R))
  | ".LBB1_2", s =>
    let r := t₀.regs.get64 .rsp
    n ≠ 0 ∧ (t₀.regs.get64 .rdi).toNat % 2 ^ 32 = n
    ∧ s.regs.get64 .rsp = r - 24 ∧ s.regs.get64 .rbp = r - 8 ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ 1 ?@ (r - 9) ⋆ Own r (t₀.regs.get64 .rbp) ((t₀.regs.get64 .rdi).setWidth 32).toInt
        (RetCell ra r ⋆ (Reserve (below n) (r - 24) ⋆ R)))
  | ".LBB1_3", s =>
    let r := t₀.regs.get64 .rsp
    (t₀.regs.get64 .rdi).toNat % 2 ^ 32 = n
    ∧ s.regs.get64 .rsp = r - 24 ∧ s.regs.get64 .rbp = r - 8 ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ Int.toBytes 1 ((n % 2 : Nat) : Int) =@ (r - 9)
        ⋆ Own r (t₀.regs.get64 .rbp) ((t₀.regs.get64 .rdi).setWidth 32).toInt
        (RetCell ra r ⋆ (Reserve (below n) (r - 24) ⋆ R)))
  | _, _ => False

/-- The `grind` call of every obligation: the cell rules need several rounds
of E-matching; the two `toInt` lemmas only add case splits. -/
macro "odd_grind" : tactic =>
  `(tactic| grind (ematch := 20) (gen := 20) (instances := 5000)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

-- The entry and exit blocks walk the frame's cells under `sym`; the default budget
-- does not cover it.
set_option maxHeartbeats 2000000 in
theorem odd_spec (hpl : Program.PlacedIn odd_body) (n : Nat) (ih : EvenSpecBelow n) :
    OddSpec n := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := odd_body) (odd_table n)
    (fun R ra t₀ s => n < 2 ^ 32 ∧ CallPostCells n R ra t₀ s
      ∧ (s.regs.get64 .rax).toNat % 256 = n % 2)
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [odd_body]
    · -- entry: prologue, spill, test
      clear ih
      sym (ematch := 20) (gen := 20) (instances := 5000)
        [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod] => vcgen <;> finish
    · -- the call: `even` at `n - 1` by its spec; its caller's memory is our cells
      rcases n with _ | k
      · exact Triple.intro fun s h => absurd rfl h.1.1
      · have hc := MachineWP.call_proc_spec_at
          (1 ?@ (t₀.regs.get64 .rsp - 9) ⋆ Own (t₀.regs.get64 .rsp) (t₀.regs.get64 .rbp)
            ((t₀.regs.get64 .rdi).setWidth 32).toInt (RetCell ra (t₀.regs.get64 .rsp) ⋆ R))
          "even" (ih k (by omega))
        clear ih
        vcgen [hc]
        -- `vcgen` leaves the table entry as an unreduced `match` and the state as a
        -- literal; `grind` does better with the entry taken apart, the state
        -- computed (`simp only`), and only the hypotheses a conjunct needs.
        · -- the load of the spilled argument
          clear hc hpl
          rename_i htab
          obtain ⟨-, -, -, hrbp, -, hmem⟩ := htab.1
          odd_grind
        · clear hc hpl
          rename_i htab x hx
          obtain ⟨-, hn, hrsp, hrbp, hsv, hmem⟩ := htab.1
          have hk : k < 2 ^ 32 := by omega
          refine ⟨fun w => ⟨⟨⟨?_, ?_⟩, hk⟩, ?_⟩, ?_⟩
          · -- the callee's stack: the slot the call writes, then its reservation
            clear hsv hx hn hrbp
            simp only [MachineData.dmem_pushRa, MachineData.get64_pushRa, Reg64s.get64_set64,
              reduceCtorEq, ite_true, ite_false, hrsp]
            odd_grind
          · -- the callee's argument: `edi = n - 1`, read back from the spill
            clear hsv hrsp
            simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true,
              ite_false]
            odd_grind
          · -- after the return: the rest of the block
            intro s' hpost
            obtain ⟨⟨hrsp', hrbp', hsv', hmem'⟩, hal⟩ := hpost
            clear hx
            simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true,
              ite_false, hrsp, hrbp] at hrsp' hrbp' hsv' hmem'
            vcgen
            · -- the store of the result is to the `bool` cell
              clear hsv hsv' hn
              odd_grind
            · simp only []
              refine ⟨⟨hn, ?_, ?_, ?_, ?_⟩, Nat.zero_le _⟩
              · odd_grind
              · odd_grind
              · odd_grind
              · clear hsv hsv' hn
                odd_grind
          · -- the slot the call writes is mapped
            clear hsv hx hrbp hn
            simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp]
            odd_grind
    · -- the result and the epilogue
      clear ih
      sym (ematch := 20) (gen := 20) (instances := 5000)
        [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod] => vcgen <;> finish
  · rintro R ra t ⟨hpre, hn⟩
    exact ⟨rfl, hpre.2, hpre.cells hn⟩
  · rintro R ra t₀ s ⟨hn, hcells, hal⟩
    exact ⟨CallPost.of_cells hn hcells, hal⟩

end Kraken.Examples.EvenOddGhost
