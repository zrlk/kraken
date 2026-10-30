/-
**The heap relation along a consumer's steps** (any ISA): the steps that
need `Spike/Lib/SrcCalls.lean`. Everything else (heap use of the local
steps, calls, returns and the exchange, `AllocInvAt` along an allocation,
`land_step`) is in `Spike/Lib/HeapPresCore.lean`.

- `heapUse_outCfg`: a call of `print` (`outCfg`: the trace grows, the
  memory is kept) keeps the heap use.
-/
import Spike.Lib.HeapPresCore
import Spike.Lib.SrcCalls

namespace Spike.Lib.HeapPres

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising
open Scc.Sem (heapUse cellCount allocCount Fresh Inv1 ValRep wordLoc)

/-- **A call of `print`** (`outCfg`: the trace grows) keeps the heap use. -/
theorem heapUse_outCfg {s : Cfg} {th th' : TTh} (hi : s.ths[0]? = some th) (hn : th'.nalloc = th.nalloc)
    (ht : th'.tidLbl = th.tidLbl) (bs : List Nat) : heapUse (Spike.Lib.SrcCalls.outCfg s th' bs) = heapUse s :=
  heapUse_set hi rfl rfl hn ht

end Spike.Lib.HeapPres
