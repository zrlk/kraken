/-
**`CorrectE` on AArch64**: `Correct` at the AArch64 target with the kernel
model's `n` thread slots, for every admissible initial stack
(`Entry.Ok`, `Scc/Sem/CorrectE.lean`).
-/
import Scc.Sem.CorrectE
import Scc.Sem.TargetA64

namespace Scc.Sem.A64

/-- **`scc` correctness at every admissible initial stack** (AArch64): for
every entry state `E` that `Entry.Ok` admits for `Λ`, `Correct` at the
target with the kernel model's hooks (`n` slots) and entry state `E`. What
`Correct` promises and does not (a trace prefix, aborts only where
justified, up to the budget `B`, no termination) is in
`Scc/Sem/Correct.lean`'s module doc. -/
def CorrectE (n : Nat) (S : SrcSem) (Λ : Layout) (B : Budget) (asm : String) : Prop :=
  ∀ E : Entry, E.Ok Λ → Correct (target (kernel n) E) S Λ B asm

end Scc.Sem.A64
