import Spike.Test.HelloLinkedA64A1
import Spike.Test.HelloLinkedA64A2
import Spike.Test.HelloLinkedA64A4
import Spike.Test.HelloLinkedA64A6
import Spike.Test.HelloLinkedA64A8
import Spike.Lib.A64HelloImmsMe

/-!
# `hello.w` on AArch64: the layout facts at the linked executable's layout `Λe`

Decided at `Λe` (`HelloLinkedA64Elf`: path, SHA, `Λe`), each by `decide +kernel` or `rfl`:

* `placeW_e`: `PlaceW pcfgH Λe oH` from A1, A2, A4, A6, A8 (`HelloLinkedA64A1` … `A8`, one module each);
* `hlo` (`.text` at `WakePh.lo = 0x210550`), `hstat`, `hnz` (`NtZ`);
* at `Le := ofPlaceW placeW_e ie`, `ie := ImmsMe.iRdM Λe` (the root's immediate table): `hpin2`, `hinit2` (hello's
  second limit word, `lim2AH`), `hA13_e` (A13's data part), `linux_ok_e` (the Linux entry admissible at `Le.Λ`:
  `RootFinal.hello_correct`'s per-entry premise is not vacuous at `Λe`).
-/

namespace Spike.Test.HelloLinkedA64

open Spike.Lib.A64.HelloPh.RootLit (pcfgH oH)
open Spike.Lib.A64.Rt (RuntimeLayout)

/-- **`PlaceW` at the executable's layout** (A1, A2, A4, A6, A8). -/
theorem placeW_e : Spike.Lib.PlaceW pcfgH Λe oH := ⟨hello_a1, hello_a2, hello_a4, hello_a6, hello_a8⟩

/-- The root's immediate table at `Λe`. -/
noncomputable abbrev ie : CoreTerm.Expr → String → Nat → Option Nat := Spike.Lib.A64.HelloPh.ImmsMe.iRdM Λe

/-- The placed runtime layout at `Λe`. -/
noncomputable abbrev Le : RuntimeLayout := RuntimeLayout.ofPlaceW placeW_e ie

/-- `.text` at `WakePh.lo`. -/
theorem hlo : Λe.code.lo = Spike.Lib.A64.WakePh.lo := by decide +kernel

/-- No static words. -/
theorem hstat : Λe.static = fun _ => none := rfl

/-- `scc_rt_nthreads` starts at `0`. -/
theorem hnz : Spike.Lib.WakeOInit.NtZ Λe oH = true := by decide +kernel

/-- The first TCB's 168 bytes fit the pinned region. -/
theorem hpin2 : Le.pinA.toNat + 168 ≤ Le.Λ.pinned.lo + Le.Λ.pinned.size := by decide +kernel

/-- hello's second TCB's limit word starts at `0`. -/
theorem hinit2 : (Spike.Lib.A64.PhRec.m0Of Le.Λ oH.prog oH.secs).initVal
    ⟨Spike.Lib.HelloGOf2H.lim2AH Le, 8⟩ = 0 := by decide +kernel

/-- **The Linux entry is admissible** at `Le.Λ`. -/
theorem linux_ok_e : Scc.Sem.Entry.linux.Ok Le.Λ := by decide +kernel

/-- **A13's data part** at `Le` (`hA13`). -/
theorem hA13_e : Scc.Cert.Spawn.A64.a13data Le.Λ oH.prog oH.secs = true := by decide +kernel

end Spike.Test.HelloLinkedA64

/-- info: 'Spike.Test.HelloLinkedA64.placeW_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedA64.placeW_e

/-- info: 'Spike.Test.HelloLinkedA64.hlo' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedA64.hlo

/-- info: 'Spike.Test.HelloLinkedA64.hnz' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedA64.hnz

/-- info: 'Spike.Test.HelloLinkedA64.hpin2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedA64.hpin2

/-- info: 'Spike.Test.HelloLinkedA64.hinit2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedA64.hinit2

/-- info: 'Spike.Test.HelloLinkedA64.linux_ok_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedA64.linux_ok_e

/-- info: 'Spike.Test.HelloLinkedA64.hA13_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedA64.hA13_e
