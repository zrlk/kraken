import Spike.Lib.Rt.A64ArenaOfPlaceOK
import Spike.Test.A64Hello1PlaceOK
import Spike.Test.A64ArenaHello1

/-!
# The arena from `PlaceOK` against `hello1.w`'s hand arena (AArch64)

`hello1.w`'s output gives the counter a zeroed word (`CtrZ`), and the arena
of its link (`arOf`) is the hand one's (`Spike.Test.A64ArenaHello1.ar`) in
its base, cells and counter.
-/

namespace Spike.Test.A64ArenaOfPlaceOK

open Spike.Lib.A64.Rt (arOf CtrZ)
open Scc.Cert.PlaceOK.A64.Test (hello1O)

/-- `hello1.w`'s `.bss`/`.data` give `scc_rt_heap_use` a zeroed word. -/
theorem hello1_ctrZ : CtrZ hello1O :=
  ⟨[.zero 8], by decide +kernel, rfl, by decide⟩

/-- The arena of `hello1.w`'s link is the hand one in its base, cells and counter. -/
theorem hello1_arOf :
    ((arOf (Scc.Cert.Link.A64.linkOf SccCode.hello1Prog SccCode.hello1Secs)).heap,
      (arOf (Scc.Cert.Link.A64.linkOf SccCode.hello1Prog SccCode.hello1Secs)).cells,
      (arOf (Scc.Cert.Link.A64.linkOf SccCode.hello1Prog SccCode.hello1Secs)).ctr) =
      (Spike.Test.A64ArenaHello1.ar.heap, Spike.Test.A64ArenaHello1.ar.cells, Spike.Test.A64ArenaHello1.ar.ctr) := by
  decide +kernel

end Spike.Test.A64ArenaOfPlaceOK
