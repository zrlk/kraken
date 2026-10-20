/-
The resource cells of the SWP spinlock worker assembled (`HardCellsX`,
`SLR/SwpRuleX.lean`) and `counter = N` for the AArch64 spinlock workers under
`Arch.armv8` with them discharged.

- `swpa` (position 3): `wp_swpa` (`SLR/SwpAcquire.lean`);
- `ldr`/`str` of the counter (positions 10, 12): `wp_ldr_c`, `wp_str_c`
  (`SLR/SwpStore.lean`);
- `stlr` (position 13): `swp_stlr` (`SLR/SwpStlr.lean`);
- the prepayment at position 13: `swp_prepay` (`SLR/SwpPrepay.lean`);
- the lift to the dead-branch erasure WP: `swp_lift` (`SLR/SwpLift.lean`).
-/
import Kraken.Promising.SLR.SwpAdequacy
import Kraken.Promising.SLR.SwpAcquire
import Kraken.Promising.SLR.SwpStlr
import Kraken.Promising.SLR.SwpLift
import Kraken.Promising.SLR.SwpPrepay

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-- **The resource cells of thread `tid < N`** under `Arch.armv8`
(`P.N < 2 ^ 32`: the counter's values fit the 32-bit store). -/
theorem hardCellsX {P : Params} (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN32 : P.N < 2 ^ 32) (hN0 : 0 < P.N)
    {tid : Nat} (htid : tid < P.N) : HardCellsX P Arch.armv8 tid :=
  ⟨wp_swpa htid hN0 hL.lk_c, wp_ldr_c,
    wp_str_c (fun h => hL.lk_c (by simp [Params.Lk, Params.C, h])) hN32 (by decide),
    swp_stlr hL, swp_prepay hL (by decide) (by decide), swp_lift P Arch.armv8 tid⟩

/-- **`counter = N` for the AArch64 spinlock workers** under `Arch.armv8`:
`N < 2 ^ 32` workers, started at the text with `X0 = l`, `X1 = c` (`Frame`),
from the initial state of `SLR/SpinInitRes.lean` (both words `0`), end with
the counter at `N` in every final configuration. Theorem 1′
(`theorem1IIPure`) and the resource cells (`hardCellsX`) are discharged. -/
theorem swp_counter_armv8 {fuel : Nat} (P : Params) (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    (hN32 : P.N < 2 ^ 32) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ (tid : Nat) (s : isa.State), states[tid]? = some s → Frame P s ∧ AtPos s 0)
    (hN : states.length = P.N) (hN0 : 0 < P.N)
    (hC0 : (Config.init states initMem).mem.initVal P.C = 0)
    (hLk0 : (Config.init states initMem).mem.initVal P.Lk = 0)
    {c : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) c) (hf : c.final = true) :
    c.mem.finalVal P.C = BitVec.ofNat 128 P.N :=
  swp_counter_armv8_of_cells P hL (fun _ htid => hardCellsX hL hN32 hN0 htid) hst hN hN0 hC0 hLk0 hc hf

end Kraken.Promising.SLR.SwpInv
