/-
**`CorrectE` from obligations whose relation depends on the entry state** (AArch64):
`hello_correctE_R` fixes the relation `Q` across entry states, but hello's (`HelloAssemblyI.QH … E …`) is built at
each `E`. Its proof reads the obligations at one `E` only, so it splits into the pointwise `hello_correct_atR`
and `hello_correctE_RQ` at `Q : Entry → WakeRel`. The root then binds `E` and its `E.Ok Λ` here (the final
theorem's admissible entry states), and gives `E.clear Λ` (`hE.1`) to the assembly's `hE` and all of `E.Ok` to
the start segment's discharger (`RootUL.hst0_UH`, `StartH0U.hst0_ofHU_i0`); no separate entry premise.

- (`hello_correct_atR`, `Correct` at one entry state, is in `HelloObligR`.)
- `hello_correctE_RQ`: `CorrectE 2` from obligations at every admissible `E`, at `Q E`.
- `hello_correctE_clear`: the same with the obligations' builder asking only `E.clear Λ` of `E.Ok Λ` too
  (the form of `RootInv.hello_root_inv`'s `hE`), the rest of `E.Ok` handed along.
-/
import Spike.Lib.HelloObligR

namespace Spike.Lib.WakeA64

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.TwoSlot Spike.Lib.Handover Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.Inv2Read
open Spike.Lib.Inv2Start Spike.Lib.A64TwoSlot Spike.Lib.WakeT1

section MainRQ

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {p : CoreTerm.Prog}

/-- **`CorrectE 2` at an entry-dependent relation** (`hello_correct_atR` at each admissible `E`). -/
theorem hello_correctE_RQ (Q : Entry → WakeRel) (Ti : Entry → Cfg → List Ev → Prop)
    (O : ∀ E : Entry, E.Ok Λ → WakeObligationsR arch Λ B asm (Q E) E (Ti E) p) :
    CorrectE 2 (srcS p arch) Λ B asm :=
  fun E hE => hello_correct_atR (O E hE)

/-- **The assembly's `hE` from `E.Ok`** (5j-start): obligations built from `E.clear Λ` (the assembly's `hE`) and
the rest of `E.Ok Λ` (the start segment's) at every admissible `E` give `CorrectE 2`. -/
theorem hello_correctE_clear (Q : Entry → WakeRel) (Ti : Entry → Cfg → List Ev → Prop)
    (O : ∀ E : Entry, E.Ok Λ → E.clear Λ = true → WakeObligationsR arch Λ B asm (Q E) E (Ti E) p) :
    CorrectE 2 (srcS p arch) Λ B asm :=
  hello_correctE_RQ Q Ti fun E hE => O E hE hE.1

end MainRQ

/-- `hello_correctE_RQ` at a constant relation is `hello_correctE_R`'s statement. -/
example {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {Q : WakeRel}
    {p : CoreTerm.Prog} (Ti : Entry → Cfg → List Ev → Prop)
    (O : ∀ E : Entry, E.Ok Λ → WakeObligationsR arch Λ B asm Q E (Ti E) p) :
    CorrectE 2 (srcS p arch) Λ B asm :=
  hello_correctE_RQ (fun _ => Q) Ti O

end Spike.Lib.WakeA64

/-- info: 'Spike.Lib.WakeA64.hello_correctE_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeA64.hello_correctE_clear
