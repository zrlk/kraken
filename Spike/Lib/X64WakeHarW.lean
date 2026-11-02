/-
**`wake_start_wc_place`'s `har` at wake's arena** (x86-64; twin of
`Spike/Lib/WakeHarW.lean`): `X64.WakeOD.arW`'s heap, cells and counter are
`Rt.arOf`'s.

- `har_arW`: the three fields, by `rfl`.

Where x86-64 differs from AArch64: the arena and layout are x86-64's
(`PlaceWX`, `RuntimeLayout.ofPlaceWX`); the statement is otherwise the same.
-/
import Spike.Lib.X64WakeOD

namespace Spike.Lib.X64.WakeOD

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}

/-- **`har` at `arW`**: the arena's heap, cells and counter are the layout's. -/
theorem har_arW (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    (arW hp i).heap = (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).Λ.heap.lo ∧
      (arW hp i).cells = Scc.Cert.PlaceOK.allocCells ∧
      (arW hp i).ctr = Scc.Cert.PlaceOK.heapUseOf (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).Λ :=
  ⟨rfl, rfl, rfl⟩

end Spike.Lib.X64.WakeOD

/-- info: 'Spike.Lib.X64.WakeOD.har_arW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOD.har_arW
