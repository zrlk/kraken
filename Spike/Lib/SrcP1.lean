/-
**The single-thread source parameters** of the compiler theorems
(`Spike/Lib/LowerA64/Correct.lean`, `Spike/Lib/LowerX64/Correct.lean`):
`srcP1 arch`, the memory model `arch`, one thread (`cap := 1`), the start at
`main` (`init := mainInit 1`), no extern step (`hooks = none`).

They restrict the source semantics to one thread running `main` from its
start, with no spawn and no extern call: the programs `Accepted0` admits.
`ret0.w`'s parameters `ret0P` (`Spike/Lib/Ret0Src.lean`) are these
(`srcP1_eq_ret0P`); nothing in them is specific to `ret0`.
-/
import Spike.Lib.Ret0Src

namespace Spike.Lib

open Scc.Sem

/-- **The single-thread source parameters**: the memory model `arch`, one
thread, the `main` start, no extern step. -/
def srcP1 (arch : WeakMem.Arch) : SrcSem.SrcParams where
  arch := arch
  cap := 1
  init := SrcSem.mainInit 1

theorem srcP1_hooks (arch : WeakMem.Arch) : (srcP1 arch).hooks = SrcSem.SrcHooks.none := rfl

theorem srcP1_init (arch : WeakMem.Arch) :
    (srcP1 arch).init { SrcSem.mainStart with cap := (srcP1 arch).cap } :=
  rfl

/-- `ret0.w`'s source parameters are the single-thread ones. -/
theorem srcP1_eq_ret0P : srcP1 = Spike.Lib.Ret0Src.ret0P := rfl

end Spike.Lib
