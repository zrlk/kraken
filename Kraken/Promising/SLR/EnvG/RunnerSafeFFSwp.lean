/-
**Combined runner theorem for `spinlock_swp{2,3}.kl`: safety ∧
program-level fault freedom**. Convenience theorems only, in the pattern of
`RunnerSafeFFA64.lean` (the SWP family is not covered there).

`SwpEnvG.swp_counter_envG_runner_safe_faultFree` pairs the runner-exact
safety theorem `swp_counter_envG_runner` (`A64SwpRunner.lean`: the counter
ends at `N` in every final configuration reachable under `Arch.armv8`) with
`swp_counter_envG_runner_faultFree` (`A64SwpNoFault.lean`:
`Config.FaultFree`, any architecture, promises included), at the union of
the two theorems' hypotheses:

  `(∀ cfg : Config isa, Reachable Arch.armv8 fuel init cfg → cfg.final = true → Φ cfg) ∧
    Config.FaultFree A fuel init`.

`A64SwpRunner.swp_counter_envG_runner_safe_faultFree_concreteN` is the
companion at the runner's own threads (`swpWorkerD0`), declarations and
initial memory (`SwpConcrete.initMem2`). The fixed-`N` corollaries
(`*_concrete2/3`) get no combined twin; use `_concreteN`.
-/
import Kraken.Promising.SLR.EnvG.A64SwpRunner
import Kraken.Promising.SLR.EnvG.A64SwpNoFault

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD)

namespace Kraken.Promising.SLR.EnvG.SwpEnvG

open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.SwpPublic (StartState)
open Kraken.Promising.SLR.EnvG.CasSmoke (casS)

/-- **AArch64 SWP spinlock workers with the runner's declarations: the
counter ends at `N`, and no step faults.** -/
theorem swp_counter_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout swpWorker)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (N : Nat) (l c : BitVec 64) (hdisj : Decls.overlaps l 4 c 4 = false) (hN32 : N < 2 ^ 32)
    (hag : ds.AgreesOnA (casS l c)) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartState l c) s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init states initMem) cfg → cfg.final = true →
      cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree A fuel (Config.init states initMem) :=
  ⟨fun _ hc hf => swp_counter_envG_runner hsz N l c hdisj hN32 hst hN hC0 hLk0 hc hf,
    swp_counter_envG_runner_faultFree hsz l c hag hst⟩

end Kraken.Promising.SLR.EnvG.SwpEnvG

namespace Kraken.Promising.SLR.EnvG.A64SwpRunner

open Kraken.Promising.SLR.SwpConcrete (counterAddr initMem2)

/-- **`spinlock_swp2.kl` / `spinlock_swp3.kl`** from the runner's exact
configuration (`N` workers `swpWorkerD0`, initial memory
`SwpConcrete.initMem2`): safety and fault freedom. -/
theorem swp_counter_envG_runner_safe_faultFree_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {A : Arch}
    {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init (List.replicate N swpWorkerD0) initMem2) c →
      c.final = true → c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N swpWorkerD0) initMem2) :=
  ⟨fun _ hc hf => swp_counter_envG_runner_concreteN N hN32 hc hf,
    swp_counter_envG_runner_faultFree_concreteN N⟩

end Kraken.Promising.SLR.EnvG.A64SwpRunner
