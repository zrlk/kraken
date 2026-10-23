import Scc.Cert.Link
import Scc.Cert.LinkA64

/-!
# Data symbols below the code: what the link and the loader accept

The loader lets a data symbol lie below the code (default `lld` puts `.rodata`
before `.text`): `Layout.WF` (`Link.wfB`) asks of each symbol only that it
is in a data region and not inside the code, and the canonical target
places it before the code (`Scc.Sem.placeBelow`, `TargetA64.lean`'s
`cellsAround`). The certification pipeline's loader check (`Link.A64.loadOk`,
the placement check's A2) still refuses one (`Rt.A64.symsOk`) until the
layout lemmas take a prefix. Checked by evaluation.
-/

namespace Scc.Test.LowSymsA64

open Scc.Sem Scc.Sem.A64 Scc.Cert

/-- `trivLayout` with its data region below the code. -/
private def Λdl : Scc.Sem.Layout :=
  { trivLayout with code := ⟨48, 16⟩, data := ⟨16, 16⟩ }

-- A symbol below the code in the data region is well formed; one below the
-- code in no region is not, nor is one inside the code.
#guard Link.wfB { Λdl with symbols := [("lo", 16)] } &&
  !Link.wfB { trivLayout with symbols := [("lo", 8)] } &&
  !Link.wfB { trivLayout with symbols := [("in", 20)] } &&
  !Link.wfB { Λdl with symbols := [("in", 48)] }

-- The target's check: no symbol inside the code `[48, 52)`; below it or at
-- its end is fine.
#guard symsAbove 48 52 [("a", 16), ("b", 52)] &&
  !symsAbove 48 52 [("a", 48)] && !symsAbove 48 52 [("a", 51)]

private def nop : Program :=
  match textProgram "nop" with
  | .ok p => p
  | .error _ => []

-- The loader check of the pipeline places only symbols above the code
-- (`Rt.A64.symsOk`): a symbol below it, or at its end (an empty padding
-- cell before `padTo`), is refused; one past the end is accepted.
#guard Rt.A64.symsOk 48 nop [("b", 56)] &&
  !Rt.A64.symsOk 48 nop [("a", 16)] && !Rt.A64.symsOk 48 nop [("e", 52)] &&
  !Rt.A64.symsOk 48 nop [("a", 16), ("b", 56)]

-- So `Link.A64.loadOk` (A2) refuses the layout with a symbol below the code,
-- and accepts it with the symbol above.
#guard Link.A64.loadOk { Λdl with symbols := [("hi", 56)] } nop {} &&
  !Link.A64.loadOk { Λdl with symbols := [("lo", 16)] } nop {}

end Scc.Test.LowSymsA64
