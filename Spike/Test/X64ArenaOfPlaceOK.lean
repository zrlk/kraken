import Spike.Lib.Rt.X64ArenaOfPlaceOK
import Spike.Test.X64ArenaHello1
import Spike.Test.X64Hello1PlaceOK

/-!
# The placed arena against `hello1.w`'s hand one (x86-64)

`hello1.w`'s output meets `CtrZ` (its counter's item is `.zero 8`), and the
arena `arOf` of its static link is the hand arena of
`Spike/Test/X64ArenaHello1.lean` in its base, cells and counter.
-/

namespace Spike.Test.X64ArenaOfPlaceOK

open Spike.Lib.X64.Rt (arOf CtrZ)
open Scc.Cert.PlaceOK.X64.Test (hello1Out)

/-- `hello1.w`'s counter's item is a zero word. -/
theorem hello1_ctrZ : CtrZ hello1Out := ⟨[.zero 8], by decide +kernel, rfl, by decide⟩

/-- The placed arena is the hand one in its base, cells and counter. -/
theorem hello1_arOf :
    (arOf (Scc.Cert.Link.X64.linkOf SccCode.hello1Cells SccCode.hello1Secs)).heap =
        Spike.Test.X64ArenaHello1.ar.heap ∧
      (arOf (Scc.Cert.Link.X64.linkOf SccCode.hello1Cells SccCode.hello1Secs)).cells =
        Spike.Test.X64ArenaHello1.ar.cells ∧
      (arOf (Scc.Cert.Link.X64.linkOf SccCode.hello1Cells SccCode.hello1Secs)).ctr =
        Spike.Test.X64ArenaHello1.ar.ctr := by
  decide +kernel

/-- info: 'Spike.Lib.X64.Rt.arOf_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.arOf_init

/-- info: 'Spike.Lib.X64.Rt.arOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.arOf_ok

end Spike.Test.X64ArenaOfPlaceOK
