/-
**The setup block's result is not a bare locative** (`setup2`'s
`shapeOf s != .loc`): `hello1L.w` (`hello1.w` with the extern linked), `ret0.w`, `ifsub1.w` stay `Accepted2`; a
setup block returning a bare `Loc` is rejected.
-/
import Scc.Frontend
import Scc.Lower.Spec2
import Scc.Test.Src

namespace Spike.Test.SetupNoLoc

open Scc

/-- `Accepted2` of a `.w` source (false if it does not parse). -/
def acc2 (src : String) : Bool :=
  match Frontend.parse src with
  | .ok p => Lower.Accepted2 p
  | .error _ => false

/-- A setup block returning a bare locative; `main` drops it. -/
def locSetup : String := "
def rodata(u : Unit) : {Loc own Array[2] LanesU8 | ini >= 2} =
  let two = 2
  let m = nameI two
  let b = newBuf[LanesU8] m
  let w0 = asLanes U8 72
  let o0 = xchg b[0] w0
  let w1 = asLanes U8 73
  let o1 = xchg b[1] w1
  ret b

def main(a : {Loc own Array[2] LanesU8 | ini >= 2} * Ptr pub Void) : Int =
  let (b, me) = a
  ret 0
"

#guard acc2 (w_src% "Scc/Test/hello1L.w")
#guard acc2 (w_src% "Spike/Gen/ret0.w")
#guard acc2 (w_src% "Scc/Test/ifsub1.w")
#guard !acc2 locSetup

end Spike.Test.SetupNoLoc
