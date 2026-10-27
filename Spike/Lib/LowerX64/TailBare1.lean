/-
**A one-block `Accepted1` program's x86-64 output has a bare tail** (the
twin of `Spike/Lib/LowerA64/TailBare1.lean`; the `Accepted0` case is
`Spike/Lib/LowerX64/TailBare.lean`'s): its `main` takes `Unit` (no setup
block), so the placement data names `scc_rt_main` without one.

- `tail_bare_of_accepted1main`: the output of a successful lowering of a
  one-block `Accepted1` program has the tail `.bare`.
-/
import Spike.Lib.LowerX64.TailBare
import Scc.Lower.InvProg1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK.X64

/-- **The x86-64 output of a one-block `Accepted1` program has a bare
tail**: `main` takes `Unit`, so no setup block runs before it. -/
theorem tail_bare_of_accepted1main {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg [d] = .ok em) (sizes : List Nat)
    (labelOffs : List (String × Nat)) :
    (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs).place.tail = .bare :=
  tail_bare_of_checked (Scc.Lower.Inv.checkedOf_accepted1main hd) hlow sizes labelOffs

end Spike.Lib.LowerX64
