/-
**`wake_start_wc_place`'s `har` at wake's arena** (AArch64):
`WakeOD.arW`'s heap, cells and counter are `Rt.arOf`'s.

- `har_arW`: the three fields, by `rfl`.
-/
import Spike.Lib.WakeOD

namespace Spike.Lib.WakeOD

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}

/-- **`har` at `arW`**: the arena's heap, cells and counter are the layout's. -/
theorem har_arW (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    (arW hp i).heap = (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i).Λ.heap.lo ∧
      (arW hp i).cells = Scc.Cert.PlaceOK.allocCells ∧
      (arW hp i).ctr = Scc.Cert.PlaceOK.heapUseOf (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i).Λ :=
  ⟨rfl, rfl, rfl⟩

end Spike.Lib.WakeOD

/-- info: 'Spike.Lib.WakeOD.har_arW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOD.har_arW
