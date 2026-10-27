/-
**`CorrectE` on x86-64 is monotone in the layout's immediate table**: the
x86-64 target's loader, label resolution (hence code marks) and
`Entry.Ok` read no `Layout.imms` (each equation below is `rfl`), so
`correct_imms_mono` (`Spike/Lib/ImmsMono.lean`) applies at every entry
state.

- `x64_correctE_imms_mono`: `CorrectE n S Λ B asm` and `ImmsSub Λ.imms i'`
  give `CorrectE n S {Λ with imms := i'} B asm`;
- `x64_correctE_imms_mono'`: the same from a layout `{Λ with imms := i}`.
-/
import Spike.Lib.ImmsMono
import Scc.Sem.CorrectEX64

namespace Spike.Lib.ImmsMono

open Scc.Sem

/-- **`CorrectE` on x86-64 is monotone in the immediate table.** -/
theorem x64_correctE_imms_mono {n : Nat} {S : SrcSem} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Scc.Sem.X64.Asm}
    (h : Scc.Sem.X64.CorrectE n S Λ B asm) {i' : CoreTerm.Expr → String → Nat → Option Nat}
    (hi : ImmsSub Λ.imms i') : Scc.Sem.X64.CorrectE n S { Λ with imms := i' } B asm :=
  fun E hE => correct_imms_mono (h E hE) hi rfl rfl

/-- **`CorrectE` on x86-64 at a table `i` gives it at a larger `i'`.** -/
theorem x64_correctE_imms_mono' {n : Nat} {S : SrcSem} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Scc.Sem.X64.Asm}
    {i i' : CoreTerm.Expr → String → Nat → Option Nat}
    (h : Scc.Sem.X64.CorrectE n S { Λ with imms := i } B asm) (hi : ImmsSub i i') :
    Scc.Sem.X64.CorrectE n S { Λ with imms := i' } B asm :=
  x64_correctE_imms_mono h hi

end Spike.Lib.ImmsMono
