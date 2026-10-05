import Kraken.X64.Examples.EvenOddExistential.Spec

/-!
# `odd`, existential style, proved against `even` below `N`

`odd_specK`: from `EvenSpecK N` (the spec of `even` for arguments below `N`,
one proposition, an assumption here; `Link.lean` discharges it), `odd` meets
`OddSpecK (N + 1)`. The mirror image of `Even.lean`; the notes there apply.
See `Spec.lean` for the form of the specification and
`EvenOddGhost/Spec.lean` for the conditions in it.

## How this differs from the ghost proof

`ProcSpecK.of_cfg_exists` (`MachineWP`) takes the witness `(n, R)` of the
specification as a logical variable, so the table and the block obligations
are those of `EvenOddGhost/Odd.lean`, with the bound `n < N + 1` in hand.
The one place the style shows is the call: the callee's spec is existential,
so the call site *produces* the witnesses — `even`'s argument `k` and the
memory it is to leave alone (our cells) — where the ghost proof passes the
memory to `call_proc_spec_at`. The steps around the call are the same
(`call_simp`, the `refine` for the rule's shape, `vcgen` for the tail,
`grind_cells`).
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.EvenOddExistential

open EvenOddGhost

variable [CodeEnv]

/-- The table of `odd` at `n`, for caller's memory `R`, return address `ra`
and entry state `t₀` (`r` its `rsp`); the one of `EvenOddGhost/Odd.lean`. -/
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

set_option maxHeartbeats 4000000 in
theorem odd_specK (hpl : Program.PlacedIn odd_body) (N : Nat) (ih : EvenSpecK N) :
    OddSpecK (N + 1) := by
  refine Kraken.Executable.ProcSpecK.of_cfg_exists (p := odd_body) (β := Nat × (Mem 64 → Prop))
    (fun x ra t₀ => odd_table x.1 x.2 ra t₀)
    (fun x ra t₀ s => x.1 < 2 ^ 32 ∧ CallPostCells x.1 x.2 ra t₀ s ∧ RetU8 s (x.1 % 2))
    (fun ra K t₀ x => x.1 < N + 1 ∧ ∀ s', OddPost x.1 x.2 ra t₀ s' → K s')
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · rintro ⟨n, R⟩ ra K t₀ ⟨hN, -⟩
    dsimp only at hN ⊢
    cfg_cases [odd_body]
    · -- entry: prologue, spill, test
      vcgen
      all_goals call_simp
      all_goals grind_cells
    · -- the call: `even` at `n - 1` by its spec, with our cells as its caller's memory
      rcases n with _ | k
      · exact Triple.intro fun s h => absurd rfl h.1.1
      · vcgen [MachineWP.call_proc_specK_at "even" ih]
        all_goals call_simp
        all_goals try refine ⟨fun w => ⟨k, 1 ?@ (t₀.regs.get64 .rsp - 9) ⋆ Own (t₀.regs.get64 .rsp)
          (t₀.regs.get64 .rbp) ((t₀.regs.get64 .rdi).setWidth 32).toInt
          (RetCell ra (t₀.regs.get64 .rsp) ⋆ R), Nat.lt_of_succ_lt_succ hN, ?_,
          fun s' hpost => ?_⟩, ?_⟩
        all_goals try (vcgen; all_goals call_simp)
        all_goals grind_cells
    · -- the result and the epilogue
      vcgen
      all_goals call_simp
      all_goals grind_cells
  · rintro ra K t ⟨n, R, hN, ⟨hcall, harg⟩, hK⟩
    exact ⟨(n, R), ⟨hN, hK⟩, rfl, harg, CallPre.cells (ArgU32.lt harg) hcall⟩
  · rintro ra K t₀ ⟨n, R⟩ ⟨-, hK⟩ s ⟨hn, hcells, hal⟩
    exact hK s ⟨CallPost.of_cells hn hcells, hal⟩

end Kraken.Examples.EvenOddExistential
