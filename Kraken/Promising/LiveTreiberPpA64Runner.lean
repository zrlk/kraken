/-
**Liveness of `treiber_pp.kl` for AArch64 with the
runner's declarations**, on the semantic machine under weak fairness and
memory fairness.

`treiber_pp_live_runner`: `treiber_pp_live_gen` (`LiveTreiberPpA64.lean`)
for strict sized declarations agreeing on `top`, the node's data word and its
`next` word; the fault-freedom side (`OkStepsPF` on every reachable
configuration) comes from the semantic twin
`treiber_pp_envG_runner_faultFree_sem`. `treiber_pp_live_runner_concrete`
is the runner's exact configuration (`[pusherWD0, popperWD1]`,
`treiberDeclsD`, `treiberInitMem`), with no hypotheses.
-/
import Kraken.Promising.LiveTreiberPpA64
import Kraken.Promising.SLR.ChainK.SemTwinsA64

namespace Kraken.Promising.Live.TreiberPpA64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.ConcreteTreiber

/-- **Liveness of `treiber_pp.kl` with the runner's declarations**: from
start states with strict sized declarations agreeing on `top`, `n`'s data
word and `n + 8`, a popper with no private `n + 8`, and an initial memory
with `top` and `n + 8` at `0`, on every weakly fair and memory fair semantic
trace the pusher and the popper both reach their end addresses. -/
theorem treiber_pp_live_runner {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)]
    {ds : Decls} (hsz : ds.StrictSized) (t n : BitVec 64) (hag : ds.AgreesOnA (treiberSA t n)) (htn : t ≠ n + 8)
    (hn : n ≠ 0) {sP sQ : isa.State} {initMem : List (Loc × Val)} (hP : StartPushWD (layout := l) ds t n sP)
    (hQ : StartPopWD (layout := l) ds t sQ) (hdnQ : Mem.loadInt sQ.st.1.dmem (n + 8) 8 = none)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨n + 8, 8⟩ = 0) :
    LiveFromSem Arch.armv8 fuel (Config.init [sP, sQ] initMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) (fun tid _ => tid < 2) Done :=
  treiber_pp_live_gen (layout := l) (hag (t, 8) (by simp)) (hag (n, 4) (by simp)) (hag (n + 8, 8) (by simp)) htn hn
    hP hQ hT0 fun _ hr => NoStuck.okStepsPF_of_faultFreeSem (Config.init_bnd _ _)
      (treiber_pp_envG_runner_faultFree_sem (layout := l) hsz t n hag hP hQ hdnQ hT0 hN0) hr

/-- **`treiber_pp.kl` is live on the runner's exact configuration**
(`[pusherWD0, popperWD1]` with the runner's declarations, `wLayoutT`,
`treiberInitMem`). -/
theorem treiber_pp_live_runner_concrete (fuel : Nat) :
    LiveFromSem Arch.armv8 fuel (Config.init [pusherWD0, popperWD1] treiberInitMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) (fun tid _ => tid < 2) Done :=
  have hag : treiberDeclsD.AgreesOnA (treiberSA topAddr n1Addr) := by decls_agrees_on_a
  treiber_pp_live_gen (layout := wLayoutT) (hag (topAddr, 8) (by simp)) (hag (n1Addr, 4) (by simp))
    (hag (n1Addr + 8, 8) (by simp)) (by decide) (by decide) pusherWD0_start popperWD1_start (by simp only [Config.init]; decide)
    fun _ hr => NoStuck.okStepsPF_of_faultFreeSem (Config.init_bnd _ _)
      treiber_pp_envG_runner_faultFree_sem_concrete hr

end Kraken.Promising.Live.TreiberPpA64

#print axioms Kraken.Promising.Live.TreiberPpA64.treiber_pp_live_runner
#print axioms Kraken.Promising.Live.TreiberPpA64.treiber_pp_live_runner_concrete
