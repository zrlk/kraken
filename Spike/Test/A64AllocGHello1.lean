/-
**Oracle: the generic `W0` and allocator obligations at `hello1.w`'s
instance** (AArch64): `Spike/Lib/A64W0G.lean`'s `W0` at `hello1Λ`, `μ0`,
`WriteAb.Ab labT` and the hand arena `ar` is `hello1.w`'s `W0`
(`hello1_W0`), and `Spike/Lib/A64AllocG.lean`'s `allocArena`, `allocCtr`
at `hello1_instOk` and `hello1Prog`'s `allocIn` give `hello1.w`'s
statements (`allocArena_hello1`, `allocCtr_hello1`); its allocator passes
`allocPhOk` (`hello1_allocPhOk`), so `allocPc`, `allocSt` give its `allocPc_hello1`,
`allocSt_hello1`.
-/
import Spike.Lib.A64AllocG
import Spike.Lib.A64AllocGSt
import Spike.Lib.A64AllocGAb
import Spike.Test.A64Hello1AllocAb
import Spike.Test.A64Hello1AllocW
import Spike.Test.A64Hello1AllocCtr

namespace Spike.Test.A64AllocGHello1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide FragS Frag)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerA (WrAt SFactsSt)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow (At)
open Spike.Lib.A64.Flow.Hello1.Inst
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End)
open Spike.Lib.A64.Alloc (Call AllocW N)
open Spike.Test.A64ArenaHello1 (ar)
open Spike.Test.A64Hello1RtW (hello1_instOk)
open SccCode (hello1Λ hello1Prog)

/-- `hello1Prog` holds the allocator's code. -/
theorem hello1_allocIn : Spike.Lib.A64.Flow.allocIn hello1Prog = true := by decide +kernel

/-- **`hello1.w`'s `W0` is the generic one** at its layout, marks, write
abort's phase and arena. -/
theorem hello1_W0 {p : Prog} {rS : Range} {Dt : State → Prop} {Ctx : FragS isaLSE2} :
    Spike.Test.A64Hello1W0.W0 p rS Dt Ctx =
      Spike.Lib.A64.W0G.W0 hello1Λ μ0 own Tk (Spike.Lib.A64.WriteAb.Ab labT) ar p rS Dt Ctx := rfl

/-- **`hello1.w`'s allocator passes the phase check** at its sites and
phases (the hand proofs' `blkPh` decisions). -/
theorem hello1_allocPhOk : Spike.Lib.A64.AllocG.allocPhOk okPc ph labT = true := by
  rw [Spike.Test.A64Hello1RtW.labT_eq_labX]; decide +kernel

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {q : Call}

/-- **`hello1.w`'s `allocArena`** from the generic one. -/
theorem allocArena_hello1 {p : Prog} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160)
    (hhi : 0 ≤ R.hi) (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ) :
    AllocW ms q (fun s c => ∀ fs, Spike.Test.A64Hello1W0.ArenaWr0 p s c fs) (fun _ _ => False)
      hello1Exe hello1End R F :=
  Spike.Lib.A64.AllocG.allocArena (hello1_instOk (rS := ⟨0, 0⟩)) hello1_allocIn hR hal hlo hhi
    (by rw [← hello1_labT]; exact hq) hmem hctr hheap hoff

/-- **`hello1.w`'s `allocCtr`** from the generic one. -/
theorem allocCtr_hello1 {Ctx : Frag isaLSE2} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160)
    (hhi : 0 ≤ R.hi) (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hmem : ∀ a : BitVec 64, (∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hheap : ms.heap = ar.heap)
    (hctx : ∀ s c, At hello1Exe hello1End R F (N (_root_.Executable.labels hello1Exe).label ms q .rmw) s c →
      Ctx s c) :
    AllocW ms q (fun s c => WrAt s ar.ctrLoc → Ctx s c) (fun _ _ => False) hello1Exe hello1End R F :=
  Spike.Lib.A64.AllocG.allocCtr (hello1_instOk (rS := ⟨0, 0⟩)) hello1_allocIn hR hal hlo hhi
    (by rw [← hello1_labT]; exact hq) hmem hheap (by decide) (by decide)
    (by rw [← hello1_labT]; exact hctx)

/-- **`hello1.w`'s `allocPc`** from the generic one. -/
theorem allocPc_hello1 :
    AllocW ms q (fun s _ => okPc (pcOf s) = true) (fun _ _ => False) hello1Exe hello1End R F :=
  Spike.Lib.A64.AllocG.allocPc (hello1_instOk (rS := ⟨0, 0⟩)) hello1_allocPhOk

/-- **`hello1.w`'s `allocSt`** from the generic one: the return address
`wc_rodata`'s `.sp0` in the allocator's phase. -/
theorem allocSt_hello1 {rS : Range} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub hello1Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hra : q.ra = (labT ".L18_wc_rodata.sp0").toBitVec)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 hello1Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    AllocW ms q (fun s _ => SFactsSt hello1Λ μ0 own rS Tk s) (Kr rS) hello1Exe hello1End R F :=
  Spike.Lib.A64.AllocG.allocSt hello1_instOk hello1_allocIn hello1_allocPhOk (fun _ => rfl) hR hal hlo hhi hl hh
    hsub hfit hFO (by rw [← hello1_labT]; exact hq)
    (by rw [hra, Spike.Test.A64Hello1RtW.labT_eq_labX]; decide +kernel) hmp hmem hno

/-- **`hello1.w`'s `allocAbOkR`**, its targets off the write abort's pcs. -/
theorem hello1_allocAbOk : Spike.Lib.A64.AllocG.allocAbOkR labT = true := by
  rw [Spike.Test.A64Hello1W0.labT_eq_labY]; decide +kernel

/-- **`hello1.w`'s `allocAb`** from the generic one: the return address
`wc_rodata`'s `.sp0`, in the allocator's phase and off the write abort's pcs. -/
theorem allocAb_hello1 (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hra : q.ra = (labT ".L18_wc_rodata.sp0").toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (fun s _ => Spike.Lib.A64ConsumerA.AbSt μ0 (Spike.Lib.A64.WriteAb.Ab labT) s) (fun _ _ => False)
      hello1Exe hello1End R F :=
  Spike.Lib.A64.AllocG.allocAb (hello1_instOk (rS := ⟨0, 0⟩)) hello1_allocIn hello1_allocPhOk hello1_allocAbOk
    hR hal hlo hhi (by rw [← hello1_labT]; exact hq)
    (by rw [hra, Spike.Test.A64Hello1RtW.labT_eq_labX]; decide +kernel)
    (by rw [hra, Spike.Test.A64Hello1W0.labT_eq_labY]; decide +kernel) hmem

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.A64AllocGHello1.allocArena_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocArena_hello1

/-- info: 'Spike.Test.A64AllocGHello1.allocCtr_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocCtr_hello1

/-- info: 'Spike.Test.A64AllocGHello1.allocSt_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocSt_hello1

/-- info: 'Spike.Test.A64AllocGHello1.allocAb_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAb_hello1

end Spike.Test.A64AllocGHello1
