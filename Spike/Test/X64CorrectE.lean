import Scc.Sem.CorrectEX64
import Spike.Lib.X64Ret0Code

/-!
# `Entry.Ok` at `ret0.w`'s layout

`Entry.Ok` (`Scc/Sem/CorrectE.lean`) decided at `ret0.w`'s layout `ret0Λ`
(`Spike/Lib/X64Ret0Code.lean`): the witness stack at `2 ^ 32` (directly and
by `Entry.ok_witness`) and the oracle's `Entry.linux` are admissible; a
misaligned stack pointer, a stack below 64 KiB, a stack pointer above
`2 ^ 63` and a stack overlapping the text are not.
-/

namespace Spike.Test.X64CorrectE

open Scc.Sem SccCode

example : Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩ ret0Λ := by decide

example : Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩ ret0Λ := Entry.ok_witness (by decide)

example : Entry.linux.Ok ret0Λ := by decide

/-- The stack pointer `2 ^ 32 + 65544` is not 16-aligned. -/
example : ¬ Entry.Ok ⟨⟨2 ^ 32 + 8, 65536⟩⟩ ret0Λ := by decide

/-- 4 KiB of initial stack is too little. -/
example : ¬ Entry.Ok ⟨⟨2 ^ 32, 4096⟩⟩ ret0Λ := by decide

/-- A stack pointer at `2 ^ 63` is not a user address. -/
example : ¬ Entry.Ok ⟨⟨2 ^ 63 - 65536, 65536⟩⟩ ret0Λ := by decide

/-- A stack over the text is not clear of the layout. -/
example : ¬ Entry.Ok ⟨⟨ret0Λ.code.lo, 65536⟩⟩ ret0Λ := by decide

end Spike.Test.X64CorrectE
