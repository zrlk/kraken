import Kraken.X64.Examples.EvenOddExistential.Spec

/-!
# `odd`, existential style

`odd_specK`: from `EvenSpecK N` (`even` for arguments below `N`), `odd` for
arguments below `N + 1`. The mirror of `Even.lean` here, as
`EvenOddGhost/Odd.lean` is of `EvenOddGhost/Even.lean`.
-/

open Kraken.X64.Parser
open Kraken
open Std.WP
open Mem
open MachineWP

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.EvenOddExistential

open EvenOddGhost

variable [CodeEnv]

/-- The table of `odd` at `n`, for caller's memory `R`, return address `ra`
and entry state `t₀` (`r` its `rsp`); as in `EvenOddGhost/Odd.lean`. -/
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

macro "odd_grind" : tactic =>
  `(tactic| grind (ematch := 20) (gen := 20) (instances := 5000)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

set_option maxHeartbeats 2000000 in
theorem odd_specK (hpl : Program.PlacedIn odd_body) (N : Nat) (ih : EvenSpecK N) :
    OddSpecK (N + 1) := by
  refine Kraken.Executable.ProcSpecK.of_cfg (p := odd_body)
    (fun ra K t₀ l s => ∃ x : Nat × (Mem 64 → Prop),
      (x.1 < N + 1 ∧ ∀ s', OddPost x.1 x.2 ra t₀ s' → K s') ∧ odd_table x.1 x.2 ra t₀ l s)
    (hblocks := ?_) (hpre := ?_)
  · intro ra K t₀
    refine MachineWP.cfg_blocks_exists (β := Nat × (Mem 64 → Prop))
      (fun x => odd_table x.1 x.2 ra t₀)
      (fun x => x.1 < N + 1 ∧ ∀ s', OddPost x.1 x.2 ra t₀ s' → K s') (fun _ _ => 0)
      (fun x a s => ExitCells x.1 x.2 ra t₀ (x.1 % 2) a s) (fun a s => a = ra ∧ K s)
      ?_ ?_
    · -- the blocks, at a witness: the ghost proof
      rintro ⟨n, R⟩ ⟨hN, -⟩
      dsimp only
      cfg_cases [odd_body]
      · -- entry: prologue, spill, test
        clear ih
        sym (ematch := 20) (gen := 20) (instances := 5000)
          [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod] => vcgen <;> finish
      · -- the call: `even` at `n - 1` by its spec; its caller's memory is our cells
        rcases n with _ | k
        · exact Triple.intro fun s h => absurd rfl h.1.1
        · have hc := MachineWP.call_proc_specK_at "even" ih
          clear ih
          vcgen [hc]
          · -- the load of the spilled argument
            clear hc hpl
            rename_i htab
            obtain ⟨-, -, -, hrbp, -, hmem⟩ := htab.1
            odd_grind
          · clear hc hpl
            rename_i htab x hx
            obtain ⟨-, hn, hrsp, hrbp, hsv, hmem⟩ := htab.1
            have hk : k < 2 ^ 32 := by omega
            -- the witnesses: `odd`'s argument, and the memory it is to leave alone
            refine ⟨fun w => ⟨k, 1 ?@ (t₀.regs.get64 .rsp - 9) ⋆ Own (t₀.regs.get64 .rsp)
              (t₀.regs.get64 .rbp) ((t₀.regs.get64 .rdi).setWidth 32).toInt
              (RetCell ra (t₀.regs.get64 .rsp) ⋆ R), by omega, ⟨⟨?_, ?_⟩, hk⟩, ?_⟩, ?_⟩
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
    · -- the exit, into the continuation
      rintro ⟨n, R⟩ ⟨-, hK⟩ a s h
      exact exit_K hK a s h
  · rintro ra K t ⟨n, R, hN, ⟨hpre, hn⟩, hK⟩
    exact ⟨(n, R), ⟨hN, hK⟩, rfl, hpre.2, hpre.cells hn⟩

end Kraken.Examples.EvenOddExistential
