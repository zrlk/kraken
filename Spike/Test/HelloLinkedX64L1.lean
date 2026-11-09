import Spike.Test.HelloLinkedX64L1A1
import Spike.Test.HelloLinkedX64L1A2
import Spike.Test.HelloLinkedX64L1A3
import Spike.Test.HelloLinkedX64L1A4
import Spike.Test.HelloLinkedX64L1A5
import Spike.Test.HelloLinkedX64L1A6
import Spike.Test.HelloLinkedX64L1A7
import Spike.Test.HelloLinkedX64L1A8
import Spike.Test.HelloLinkedX64L1A9
import Spike.Test.HelloLinkedX64L1A11
import Spike.Test.HelloLinkedX64L1A12c
import Spike.Test.HelloLinkedX64L1A12p
import Spike.Test.HelloLinkedX64L1A13
import Spike.Lib.X64HelloLayoutE

/-!
# `hello.w` on x86-64: the layout facts at `Λ1` (non-vacuity of `LayoutEX`)

`Λ1` (`Spike/Test/HelloLinkedX64.lean`) is the static link of hello's listing at GNU `ld`'s section bases.
Every field of `RootBaseInh.LayoutEX` is decided there (`placeOK2At` from its components, one module each),
so the root, stated at any `LayoutEX Λ0`, is not vacuous.

Unlike AArch64 (whose `LayoutE` is inhabited at the executable's layout only), the instance is at a layout
computed from the listing, independent of the executable; unlike x86-64 wake (`WakeLinkedX64Le`), the facts
are bundled into one structure.
-/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.HelloPh.RootLit (pcfgH oH)
open Spike.Lib.X64.HelloImms (iRdM)

/-- **`placeOK2At` of hello's output at `Λ1`**, from its components. -/
theorem hello1_placeOK2At : Scc.Cert.Spawn.X64.placeOK2At pcfgH Λ1 oH = true :=
  Scc.Cert.Spawn.X64.placeOK2At_of hello1_a1 hello1_a2 hello1_a3 hello1_a4 hello1_a5 hello1_a6 hello1_a7
    hello1_a8 hello1_a9 hello1_a11 hello1_a12c hello1_a12p hello1_a13

/-- `PlaceWX` at `Λ1`. -/
theorem placeWX_1 : PlaceWX pcfgH Λ1 oH := PlaceWX.of2 hello1_placeOK2At

/-- The placed runtime layout at `Λ1` and the root's table. -/
noncomputable abbrev L1 : RuntimeLayout := RuntimeLayout.ofPlaceWX placeWX_1 (iRdM Λ1)

theorem hlo_1 : Λ1.code.lo = Spike.Lib.X64.HelloPh.lo := by decide +kernel

theorem hstat_1 : Λ1.static = fun _ => none := rfl

theorem hnz_1 : Spike.Lib.X64WakeOInit.NtZ Λ1 oH = true := by decide +kernel

theorem hA13_1 : Scc.Cert.Spawn.X64.a13data L1.Λ oH.prog oH.secs = true := by decide +kernel

theorem hpin2_1 : L1.pinA.toNat + 200 ≤ L1.Λ.pinned.lo + L1.Λ.pinned.size := by decide +kernel

theorem hinit2_1 :
    (Spike.Lib.X64.PhRec.m0Of L1.Λ oH.prog oH.secs).initVal ⟨Spike.Lib.X64HelloGOf2H.lim2AH L1, 8⟩ = 0 := by
  decide +kernel

theorem hsub1_1 : (Spike.Lib.X64.Rt.PreChild.r1Of L1.lab).Sub L1.Λ.stackPool := by
  -- the kernel does not reduce the executable's label lookup: through `lab_stacks`
  have h := L1.lab_stacks
  unfold Scc.Sem.Range.Sub Spike.Lib.X64.Rt.PreChild.r1Of RuntimeLayout.lab
  rw [h]
  decide +kernel

/-- **`LayoutEX` at `Λ1`**: every field decided. -/
theorem layoutEX_1 : Spike.Lib.X64.HelloPh.RootBaseInh.LayoutEX Λ1 :=
  ⟨placeWX_1, hlo_1, hstat_1, hnz_1, hA13_1, hpin2_1, hinit2_1, hsub1_1⟩

end Spike.Test.HelloLinkedX64

/-- info: 'Spike.Test.HelloLinkedX64.layoutEX_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedX64.layoutEX_1
