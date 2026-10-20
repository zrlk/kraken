/-
The resource cells of the x64 spinlock worker assembled (`HardCellsX`,
`SLR/X64SpinRule.lean`) and `counter = N` for the x64 spinlock workers under
`Arch.tso` with them. The x64 twin of `SLR/SwpFinal.lean`.

- `xchgl` (position 5): `wp_xchg` (`SLR/X64SpinXchg.lean`);
- the counter load (position 8): `wp_load_counter` (`SLR/X64SpinStore.lean`);
- the unlock (position 11): `x64_unlock` (`SLR/X64SpinUnlock.lean`);
- the counter store (position 10): `wp_store_counter`
  (`SLR/X64SpinStoreC.lean`);
- the prepayment at positions 5, 10 and 11: `x64_prepay`
  (`SLR/X64SpinPrepay.lean`);
- the lift to the dead-branch erasure WP: `x64_lift` (`SLR/X64SpinLift.lean`).
-/
import Kraken.Promising.SLR.X64SpinFinal
import Kraken.Promising.SLR.X64SpinXchg
import Kraken.Promising.SLR.X64SpinStore
import Kraken.Promising.SLR.X64SpinUnlock
import Kraken.Promising.SLR.X64SpinLift
import Kraken.Promising.SLR.X64SpinStoreC
import Kraken.Promising.SLR.X64SpinPrepay

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-- **The resource cells of thread `tid`** under `Arch.tso`
(`P.N < 2 ^ 32`: the counter's values fit the 32-bit store). -/
theorem x64_hardCellsX {P : Params} (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN32 : P.N < 2 ^ 32) {tid : Nat} :
    HardCellsX P Arch.tso tid :=
  ⟨wp_xchg hL.lk_c rfl, wp_load_counter,
    X64SpinInv.wp_store_counter (fun h => hL.lk_c (by simp [Params.Lk, Params.C, h])) hN32 (by decide),
    x64_unlock (by decide) hL, x64_prepay hL hN32, x64_lift P Arch.tso tid⟩

/-- **`counter = N` for the x64 spinlock workers** under `Arch.tso`:
`N < 2 ^ 32` workers, started at the text with `%rdi = l`, `%rsi = c`
(`Frame`), from the initial state of `SLR/SpinInitRes.lean` (both words `0`),
end with the counter at `N` in every final configuration. Theorem 1′
(`theorem1IIPure`) and the resource cells (`x64_hardCellsX`) are
discharged. -/
theorem x64_counter_spin {fuel : Nat} (P : Params) (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    (hN32 : P.N < 2 ^ 32) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ (tid : Nat) (s : isa.State), states[tid]? = some s → Frame P s ∧ AtPos s 0)
    (hN : states.length = P.N) (hN0 : 0 < P.N)
    (hC0 : (Config.init states initMem).mem.initVal P.C = 0)
    (hLk0 : (Config.init states initMem).mem.initVal P.Lk = 0)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true) :
    c.mem.finalVal P.C = BitVec.ofNat 128 P.N :=
  x64_counter_spin_of_cells P hL (fun _ _ => x64_hardCellsX hL hN32) hst hN hN0 hC0 hLk0 hc hf

end Kraken.Promising.SLR.X64SpinInv
