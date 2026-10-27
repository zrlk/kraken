import Spike.Lib.X64W0G
import Spike.Test.X64Hello1W0
import Spike.Test.X64Hello1W1

/-!
# `hello1.x`'s `W0`/`W1` are the generic ones (x86-64)

The hand fragments of `Spike/Test/X64Hello1W0.lean` and
`Spike/Test/X64Hello1W1.lean` are `Spike.Lib.X64.W0G`'s at `hello1Λ`, `μ0`,
`Inst.own`, `Inst.Tk`, `WriteAb.Ab labT` and the hand arena, by `rfl`.
-/

namespace Spike.Test.X64W0GHello1

open Kraken.Promising.X64 (State isa)
open Scc.Sem (Range)
open Spike.Lib (FragS)
open Spike.Lib.X64.Flow.Hello1.Inst (μ0 own Tk labT)
open Spike.Test.X64ArenaHello1 (ar)
open SccCode (hello1Λ)

theorem w0_eq (p : CoreTerm.Prog) (rS : Range) (Dt : State → Prop) (Ctx : FragS isa) :
    Spike.Test.X64Hello1W0.W0 p rS Dt Ctx =
      Spike.Lib.X64.W0G.W0 hello1Λ μ0 own Tk (Spike.Lib.X64.WriteAb.Ab labT) ar p rS Dt Ctx := rfl

theorem w1_eq (Dt : State → Prop) (l : WeakMem.AllocLabel) (b n : Nat) (p : CoreTerm.Prog) (rS : Range) :
    Spike.Test.X64Hello1W1.W1 Dt l b n p rS =
      Spike.Lib.X64.W0G.W1 hello1Λ μ0 own Tk (Spike.Lib.X64.WriteAb.Ab labT) ar Dt l b n p rS := rfl

end Spike.Test.X64W0GHello1
