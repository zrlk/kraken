/-
**hello's root `hG`** (x86-64; the twin of `Spike/Lib/A64HelloRootHG.lean`; `hello_obligations_IM`'s `hG` at the
root): `MemInv` of the instance's guarantee `X64HelloGOf2H.gWH` at the dummy heap word `X64WakeHG.cTW` gives
`MemInv` of every record's value invariant `X64HelloAssemblyI.GH … (G0H …) w`.

- `gWH_le`: every value `gWH` allows at the heap word `cTW` is one `GOf2H` allows (`hGpl_ofPlaceW2H`, given the
  pinned region reaches `pinA + 200`), so it is one `wakeG (GOf2H …) cT'` allows at every flag word `cT'`.
- `hG_H`: the root's `hG`.

## Unlike AArch64

- Over `PlaceWX` and its layout `RuntimeLayout.ofPlaceWX`; the records' value invariant is
  `X64HelloAssemblyIM.G0H`, the guarantee `X64HelloGOf2H.gWH` (the same statement as on AArch64).
-/
import Spike.Lib.X64HelloAssemblyIM
import Spike.Lib.X64WakeHG

namespace Spike.Lib.X64.HelloPh.RootHG

open Kraken Kraken.Promising
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloGOf2H (gWH GOf2H hGpl_ofPlaceW2H)
open Spike.Lib.X64HelloAssemblyI (ιH GH)
open Spike.Lib.X64HelloAssemblyIM (G0H)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : Spike.Lib.PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`gWH` at the dummy heap word is below every flag word's `wakeG`** at `GOf2H`. -/
theorem gWH_le (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (cT' : Loc) :
    ∀ L v, gWH hp i (Spike.Lib.X64WakeHG.cTW hp i) L v →
      Spike.Lib.WakeG.wakeG (GOf2H (Ly) (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs)) cT' L v := by
  rintro L v (rfl | h)
  · exact .inr (hGpl_ofPlaceW2H hp i hpin2 _ v (.inl (Spike.Lib.X64WakeHG.cTW_heap hp i)))
  · exact .inr h

/-- **The root's `hG`** (`hello_obligations_IM`'s, at `Dd.G := gWH (cTW)`): `MemInv` of the instance's guarantee
gives `MemInv` of every record's value invariant. -/
theorem hG_H (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) :
    ∀ (w : ιH hp i) (m : Memory), MemInv (gWH hp i (Spike.Lib.X64WakeHG.cTW hp i)) m →
      MemInv (GH hp i (G0H hp i) w) m :=
  fun w _ h => ⟨fun l => gWH_le hp i hpin2 w.1.cT _ _ (h.1 l), fun x hx => gWH_le hp i hpin2 w.1.cT _ _ (h.2 x hx)⟩

end Spike.Lib.X64.HelloPh.RootHG

/-- info: 'Spike.Lib.X64.HelloPh.RootHG.hG_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootHG.hG_H
