import Spike.Test.HelloLinkedX64A1
import Spike.Test.HelloLinkedX64A2
import Spike.Test.HelloLinkedX64A3
import Spike.Test.HelloLinkedX64A4
import Spike.Test.HelloLinkedX64A5
import Spike.Test.HelloLinkedX64A6
import Spike.Test.HelloLinkedX64A7
import Spike.Test.HelloLinkedX64A8
import Spike.Test.HelloLinkedX64A9
import Spike.Test.HelloLinkedX64A11
import Spike.Test.HelloLinkedX64L1A12c
import Spike.Test.HelloLinkedX64A12p
import Spike.Test.HelloLinkedX64A13
import Spike.Lib.X64HelloLayoutE

/-!
# `hello.w` on x86-64: the layout facts at the executable's layout `Λe`

`Λe` (`Spike/Test/HelloLinkedX64Elf.lean`) is the layout of the checked-in executable. Every field of
`RootBaseInh.LayoutEX` is decided there (`placeOK2At` from its components, one module each; A12's code part
is layout-independent, `hello1_a12c`), as at `Λ1` (`HelloLinkedX64L1`): `layoutEX_e : LayoutEX Λe`, and the
root's table `iH := iRdM Λe` with the placed runtime layout `Le`. `linux_ok_e` is the Linux entry admissible at
`Le.Λ` (the root's `hE`), as AArch64's.

Unlike AArch64 (`HelloLinkedA64`, whose `LayoutE` is stated at the forced `.text` base `WakePh.lo`), `.text` is
at `ld`'s default `0x401000` (`X64.HelloPh.lo`); unlike x86-64 wake (`WakeLinkedX64Le`), the facts are bundled
into one structure, the one the root is stated at.
-/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.HelloPh.RootLit (pcfgH oH)
open Spike.Lib.X64.HelloImms (iRdM)

/-- **`placeOK2At` of hello's output at `Λe`**, from its components. -/
theorem hello_placeOK2At : Scc.Cert.Spawn.X64.placeOK2At pcfgH Λe oH = true :=
  Scc.Cert.Spawn.X64.placeOK2At_of hello_a1 hello_a2 hello_a3 hello_a4 hello_a5 hello_a6 hello_a7
    hello_a8 hello_a9 hello_a11 hello1_a12c hello_a12p hello_a13

/-- `PlaceWX` at `Λe`. -/
theorem placeWX_e : PlaceWX pcfgH Λe oH := PlaceWX.of2 hello_placeOK2At

/-- The root's immediate table at `Λe`. -/
noncomputable abbrev iH : CoreTerm.Expr → String → Nat → Option Nat := iRdM Λe

/-- The placed runtime layout at `Λe` and the root's table. -/
noncomputable abbrev Le : RuntimeLayout := RuntimeLayout.ofPlaceWX placeWX_e iH

theorem hlo_e : Λe.code.lo = Spike.Lib.X64.HelloPh.lo := by decide +kernel

theorem hstat_e : Λe.static = fun _ => none := rfl

theorem hnz_e : Spike.Lib.X64WakeOInit.NtZ Λe oH = true := by decide +kernel

theorem hA13_e : Scc.Cert.Spawn.X64.a13data Le.Λ oH.prog oH.secs = true := by decide +kernel

theorem hpin2_e : Le.pinA.toNat + 200 ≤ Le.Λ.pinned.lo + Le.Λ.pinned.size := by decide +kernel

theorem hinit2_e :
    (Spike.Lib.X64.PhRec.m0Of Le.Λ oH.prog oH.secs).initVal ⟨Spike.Lib.X64HelloGOf2H.lim2AH Le, 8⟩ = 0 := by
  decide +kernel

theorem hsub1_e : (Spike.Lib.X64.Rt.PreChild.r1Of Le.lab).Sub Le.Λ.stackPool := by
  -- the kernel does not reduce the executable's label lookup: through `lab_stacks`
  have h := Le.lab_stacks
  unfold Scc.Sem.Range.Sub Spike.Lib.X64.Rt.PreChild.r1Of RuntimeLayout.lab
  rw [h]
  decide +kernel

/-- **The Linux entry is admissible** at `Le.Λ`. -/
theorem linux_ok_e : Scc.Sem.Entry.linux.Ok Le.Λ := by decide +kernel

/-- **`LayoutEX` at `Λe`**: every field decided. -/
theorem layoutEX_e : Spike.Lib.X64.HelloPh.RootBaseInh.LayoutEX Λe :=
  ⟨placeWX_e, hlo_e, hstat_e, hnz_e, hA13_e, hpin2_e, hinit2_e, hsub1_e⟩

end Spike.Test.HelloLinkedX64

/-- info: 'Spike.Test.HelloLinkedX64.layoutEX_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedX64.layoutEX_e
/-- info: 'Spike.Test.HelloLinkedX64.linux_ok_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedX64.linux_ok_e
