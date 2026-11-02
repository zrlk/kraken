/-
**`CorrectE` from obligations whose relation depends on the entry state** (x86-64; the twin of
`Spike/Lib/HelloCorrectEQ.lean`): hello's relation is built at each entry state `E`, and `hello_correct_atR`
(`X64HelloObligR`) reads the obligations at one `E` only, so `CorrectE 2` follows from obligations at
`Q : Entry → WakeRel` at every admissible `E`.

- `hello_correctE_RQ`: `CorrectE 2` from obligations at every admissible `E`, at `Q E`.
- `hello_correctE_clear`: the same with the obligations' builder also given `E.clear Λ`.

Unlike AArch64, the obligations are `X64WakeA64.WakeObligationsR` over x86-64's `asm : Scc.Sem.X64.Asm`, and the
conclusion is `Scc.Sem.X64.CorrectE`; the proofs are the AArch64 ones.
-/
import Spike.Lib.X64HelloObligR

namespace Spike.Lib.X64WakeA64

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel

section MainRQ

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {p : CoreTerm.Prog}

/-- **`CorrectE 2` at an entry-dependent relation** (`hello_correct_atR` at each admissible `E`). -/
theorem hello_correctE_RQ (Q : Entry → WakeRel) (Ti : Entry → Cfg → List Ev → Prop)
    (O : ∀ E : Entry, E.Ok Λ → WakeObligationsR arch Λ B asm (Q E) E (Ti E) p) :
    CorrectE 2 (srcS p arch) Λ B asm :=
  fun E hE => hello_correct_atR (O E hE)

/-- **The assembly's `hE` from `E.Ok`**: obligations built from `E.clear Λ` and the rest of `E.Ok Λ` at every
admissible `E` give `CorrectE 2`. -/
theorem hello_correctE_clear (Q : Entry → WakeRel) (Ti : Entry → Cfg → List Ev → Prop)
    (O : ∀ E : Entry, E.Ok Λ → E.clear Λ = true → WakeObligationsR arch Λ B asm (Q E) E (Ti E) p) :
    CorrectE 2 (srcS p arch) Λ B asm :=
  hello_correctE_RQ Q Ti fun E hE => O E hE hE.1

end MainRQ

/-- `hello_correctE_RQ` at a constant relation. -/
example {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {Q : WakeRel}
    {p : CoreTerm.Prog} (Ti : Entry → Cfg → List Ev → Prop)
    (O : ∀ E : Entry, E.Ok Λ → WakeObligationsR arch Λ B asm Q E (Ti E) p) :
    CorrectE 2 (srcS p arch) Λ B asm :=
  hello_correctE_RQ (fun _ => Q) Ti O

end Spike.Lib.X64WakeA64

/-- info: 'Spike.Lib.X64WakeA64.hello_correctE_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeA64.hello_correctE_clear
