/-
**What the consumer's `msOf` lacks for the hello1 setup** (AArch64): at
`msOf` as it stands (`MemSide.ofLabels`' defaults for the arena), the
setups' `hu : ms.units 2 τ8 = 3` and `rdQ_ok`'s `hcells` fail for every
layout, marks and labels, and its `hheap` (`(lab "scc_rt_heap").toNat =
ms.heap`) asks the arena's label at `0`. The setups' `hQ` and `hu` wait on
a memory side carrying the arena (`heap`, `ctr`, `units`, `cells`), not
only `heap`; these checks are to be updated when it lands.
-/
import Spike.Lib.A64Consumer
import Spike.Lib.Hello1RodataSrc

namespace Spike.Test.A64MsOfHello1Gap

open Spike.Lib.Hello1RodataSrc (τ8)

/-- `msOf`'s allocation of `2` lane words is one unit, not `3`. -/
theorem msOf_units {Λ μ rd G own lbl lsize bo} :
    (Spike.Lib.A64Consumer.msOf Λ μ rd G own lbl lsize bo).units 2 τ8 = 1 := rfl

/-- `msOf`'s arena has no cells. -/
theorem msOf_cells {Λ μ rd G own lbl lsize bo} :
    (Spike.Lib.A64Consumer.msOf Λ μ rd G own lbl lsize bo).cells = 0 := rfl

/-- `msOf`'s arena is at `0`. -/
theorem msOf_heap {Λ μ rd G own lbl lsize bo} :
    (Spike.Lib.A64Consumer.msOf Λ μ rd G own lbl lsize bo).heap = 0 := rfl

/-- `msOf`'s counter is at `0`. -/
theorem msOf_ctr {Λ μ rd G own lbl lsize bo} :
    (Spike.Lib.A64Consumer.msOf Λ μ rd G own lbl lsize bo).ctr = 0 := rfl

end Spike.Test.A64MsOfHello1Gap
