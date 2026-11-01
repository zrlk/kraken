/-
**Level 0's heap-abort control facts are satisfiable** (AArch64;
`5h-S-habctl-L1`): at level 0 the heap abort's control premise is
`hhabctlRd` (`HabCtlRd.HabCtlRdH` at `[frH c0S.env]`; level-0 twins `StartH0R0`/`StartH0U0` ask no
`HabCtlH`, which moved to level 1). Its control `rdCN` under the frame `frH c0S.env` reads only static words:
`rdCN`'s `m` (`2`, the immediate at `eB`) and the frame's `me` (main's `ThreadId` box at `tcb0`, the immediate at
`SrcCalls.setupCont`); both are entries of the root's table `ImmsMe.iRdM`, so the placement holds at EVERY state
with no premise but the placement witness `hp` (unlike level 1's `c0H`, whose `sl` word has a dynamic base).
-/
import Spike.Lib.A64HelloHabCtlRdM

namespace Spike.Lib.A64.HelloPh.HabCtlEx

/-- Level 0's placement at every state from `hp` alone (`HabCtlRdM.placedSE_rdCN_iRdM`). -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (s : Kraken.Promising.AArch64.State) :
    Spike.Lib.A64ConsumerS.PlacedSE (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (ImmsMe.iRdM Λ0)).Λ
      (Spike.Lib.WakeLoadT.L0T (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (ImmsMe.iRdM Λ0)).Λ) s
      Spike.Lib.HelloRodataSrc.rdCN [Spike.Lib.HelloRdCf.frH Spike.Lib.A64.HelloPh.C0S.c0S.env] :=
  HabCtlRdM.placedSE_rdCN_iRdM hp s

end Spike.Lib.A64.HelloPh.HabCtlEx
