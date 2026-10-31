/-
**main's state predicate after the spawn** (x86-64): the x64
twin of `Spike/Lib/WakeInst.lean`'s `mainW`, split out so that the per-node
obligations (`Spike/Lib/X64WakeMainW.lean`) do not wait for the rest of the
instance (`X64WakeInst`: `mainWR`, `wakeMs`, `wakeM`, `wakeQI`, which import
this file and do not redefine `mainW`).

- `mainW lab exe Λ lbl`: off every abort exit and the transfer sites
  (`X64WakeOff.AbOffA lab`), the source off its return, the state wide on the
  loaded executable `exe` (`X64.WideKeep.WideX`), and the source's
  environment placed at the spawn's placement `lbl`
  (`X64Consumer.Placed`). The conjuncts are in `WakeInst.mainW`'s order, so
  the projections are the same.
-/
import Spike.Lib.X64WakeOffDef
import Spike.Lib.X64WideKeep
import Spike.Lib.X64Consumer
import Spike.Lib.WakeMLive

namespace Spike.Lib.X64WakeInst

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Spike.Lib.WakeMLive (wlRet)

/-- **main's state predicate after the spawn**: off every abort exit and the
transfer sites, the source off its return, the state wide on the loaded
executable `exe` (`WideX`), and the source's environment placed at the
spawn's placement `lbl` (`Placed`). Later conjuncts are appended at the end
so the projections stay stable. -/
def mainW (lab : String → Int64) (exe : _root_.Executable) (Λ : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) : Frag isa :=
  fun s c => Spike.Lib.X64WakeOff.AbOffA lab s c ∧ c.term ≠ wlRet ∧
    Spike.Lib.X64.WideKeep.WideX exe s ∧ Spike.Lib.X64Consumer.Placed Λ lbl s c

end Spike.Lib.X64WakeInst
