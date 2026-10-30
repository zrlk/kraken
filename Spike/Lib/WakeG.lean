/-
**wake's runtime value invariant**: the datum `G`
of `WakeRel` (`Spike/Lib/WakeA64.lean`), per ghost record `w` the
one-thread invariant `G0` (the consumer's `GOf Ly m0`,
`Spike/Lib/A64StartOfPlaceOK.lean`) with the flag's target word `cT` free.

- `wakeG G0 cT`: at `cT` any value, elsewhere `G0`.
- `wakeG_cT`: any value at `cT`, so the worker's flag store `1`
  (`WCompatX.Gc`) is immediate.
- `wakeG_of`, `memInv_wakeG`: weaker than `G0`, so the clone's `MemInv`
  (`post_start`'s `hG`) follows from the one-thread one.
- `wakeG_off`: off `cT`, `G0` (a load of the limit word reads its values).
- `wakeG_iff`: where `G0` already holds of any value at `cT` (a placed word
  is not a fixed one, `Scc.Sem.fixG_of_placed`), the two agree.
-/
import Kraken.Promising.PromiseSafe

namespace Spike.Lib.WakeG

open Kraken Kraken.Promising

/-- **wake's value invariant**: at the flag's target word `cT` any value,
elsewhere the one-thread invariant `G0`. -/
def wakeG (G0 : Loc → Val → Prop) (cT : Loc) (L : Loc) (v : Val) : Prop :=
  L = cT ∨ G0 L v

variable {G0 : Loc → Val → Prop} {cT : Loc}

/-- Any value at `cT` (`WCompatX.Gc`). -/
theorem wakeG_cT (v : Val) : wakeG G0 cT cT v := .inl rfl

/-- `G0` implies `wakeG`. -/
theorem wakeG_of {L : Loc} {v : Val} (h : G0 L v) : wakeG G0 cT L v := .inr h

/-- **The clone's `MemInv`** from the one-thread one. -/
theorem memInv_wakeG {m : Memory} (h : MemInv G0 m) : MemInv (wakeG G0 cT) m :=
  ⟨fun l => wakeG_of (h.1 l), fun w hw => wakeG_of (h.2 w hw)⟩

/-- Off `cT`, `wakeG` is `G0`. -/
theorem wakeG_off {L : Loc} {v : Val} (h : wakeG G0 cT L v) (hL : L ≠ cT) : G0 L v :=
  h.resolve_left hL

/-- **`wakeG` is `G0`** when `G0` holds of any value at `cT`. -/
theorem wakeG_iff (hc : ∀ v, G0 cT v) {L : Loc} {v : Val} : wakeG G0 cT L v ↔ G0 L v :=
  ⟨fun h => h.elim (fun e => e ▸ hc v) id, wakeG_of⟩

end Spike.Lib.WakeG
