/-
**Liveness of `treiber_pp.kl` for x64 with the runner's
declarations**, on the semantic machine (`Arch.tso`) under weak fairness and
memory fairness. The x64 twin of
`LiveTreiberPpA64Runner.lean`.

`x64_treiber_pp_live_runner`: `x64_treiber_pp_live_gen`
(`LiveTreiberPpX64.lean`) for strict sized declarations agreeing on `top`,
the node's data word and its `next` word (`pushS top n1`); the fault-freedom
side (`OkStepsPF` on every reachable configuration) comes from the semantic
twin `x64_treiber_pp_envG_runner_faultFree_sem` through
`NoStuck.okStepsPF_of_faultFreeSem`. `x64_treiber_pp_live_runner_concrete`
is the runner's exact configuration (`[treiberP0D, treiberP1D]`,
`treiberInitMemV`), with no hypotheses.
-/
import Kraken.Promising.LiveTreiberPpX64
import Kraken.Promising.SLR.ChainK.SemTwinsX64

namespace Kraken.Promising.Live.TreiberPpX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.X64.EnvG.TreiberAbs Kraken.Promising.X64.EnvG.TreiberX

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiberImageV)]

/-- **Liveness of `treiber_pp.kl` (x64) with the runner's declarations**:
from the start states of `x64_treiber_pp_envG_runner_faultFree` (strict
sized declarations agreeing on `top`, `n1`'s data word and `n1 + 8`; an
initial memory with `top` and `n1 + 8` at `0`), for `n1 ≠ 0` and
`top ≠ n1 + 8`, on every weakly fair and memory fair semantic trace the
pusher and the popper both reach their end addresses. -/
theorem x64_treiber_pp_live_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn (pushS (symT "top") (symT "n1"))) (htn : symT "top" ≠ symT "n1" + 8) (hn : symT "n1" ≠ 0)
    {sP sQ : isa.State} {initMem : List (Loc × Val)} (hP : StartPushVD ds sP) (hQ : StartPopVD ds sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "top", 8⟩ = 0)
    (hN0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "n1" + 8, 8⟩ = 0) :
    LiveFromSem Arch.tso fuel (Config.init [sP, sQ] initMem)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg) (fun tid _ => tid < 2) Done :=
  x64_treiber_pp_live_gen (hag (_, 8) (by simp)) (hag (_, 4) (by simp)) (hag (_ + 8, 8) (by simp)) htn hn hP hQ hT0
    fun _ hr => NoStuck.okStepsPF_of_faultFreeSem (Config.init_bnd _ _)
      (x64_treiber_pp_envG_runner_faultFree_sem hsz hag hP hQ hT0 hN0) hr

section
open Kraken.Promising.X64.EnvG.TreiberAbs.Concrete Kraken.Promising.SLR.EnvG

omit layout hv in
/-- **`treiber_pp.kl` (x64) is live from the runner's exact configuration**
(`[treiberP0D, treiberP1D]` with the runner's declarations, `treiberLayoutV`,
`treiberInitMemV`). -/
theorem x64_treiber_pp_live_runner_concrete (fuel : Nat) :
    LiveFromSem Arch.tso fuel (Config.init [treiberP0D, treiberP1D] treiberInitMemV)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg) (fun tid _ => tid < 2) Done :=
  have hag : treiberDeclsD.AgreesOn (pushS (symT (layout := treiberLayoutV) "top") (symT (layout := treiberLayoutV) "n1")) := by
    rw [symT_top, symT_n1]; decls_agrees_on
  x64_treiber_pp_live_gen (layout := treiberLayoutV) (hag (_, 8) (by simp)) (hag (_, 4) (by simp))
    (hag (_ + 8, 8) (by simp))
    (by rw [symT_top, symT_n1]; decide) (by rw [symT_n1]; decide) treiberP0D_start treiberP1D_start
    (by rw [symT_top]; simp only [Config.init_mem]; decide)
    fun _ hr => NoStuck.okStepsPF_of_faultFreeSem (Config.init_bnd _ _)
      x64_treiber_pp_envG_runner_faultFree_sem_concrete hr

end

end Kraken.Promising.Live.TreiberPpX64

#print axioms Kraken.Promising.Live.TreiberPpX64.x64_treiber_pp_live_runner
#print axioms Kraken.Promising.Live.TreiberPpX64.x64_treiber_pp_live_runner_concrete
