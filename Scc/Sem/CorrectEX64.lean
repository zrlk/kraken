/-
**`CorrectE` on x64**: `Correct` at the x64 target with the kernel model's
`n` thread slots, for every admissible initial stack (`Entry.Ok`,
`Scc/Sem/CorrectE.lean`).
-/
import Scc.Sem.CorrectE
import Scc.Sem.TargetX64

namespace Scc.Sem.X64

/-- **`scc` correctness at every admissible initial stack** (x64): for every
entry state `E` that `Entry.Ok` admits for `Λ`, `Correct` at the target with
the kernel model's hooks (`n` slots) and entry state `E`. `asm` is x64's
text type `Asm`, the text with its sizes and label offsets. What `Correct`
promises and does not (a trace prefix, aborts only where justified, up to
the budget `B`, no termination) is in `Scc/Sem/Correct.lean`'s module
doc. -/
def CorrectE (n : Nat) (S : SrcSem) (Λ : Layout) (B : Budget) (asm : Asm) : Prop :=
  ∀ E : Entry, E.Ok Λ → Correct (target (kernel n) E) S Λ B asm

end Scc.Sem.X64
