/-
**Oracle: the generic allocator obligations at `hello1.x`'s instance**
(x86-64), the twin of `Spike/Test/A64AllocGHello1.lean`:
`Spike/Lib/X64AllocG.lean`'s `allocArena`, `allocCtr` at `hello1_instOk`
and `hello1Cells`' `allocIn` give `hello1.x`'s statements
(`allocArena_hello1`, `allocCtr_hello1`); its allocator passes `allocPhOk`
(`X64AllocPhHello1.hello1_allocPhOk`), so `allocPc`, `allocSt` give its
`allocPc_hello1`, `allocSt_hello1`; and `allocAbOk`
(`X64AllocAbOkHello1.hello1_allocAbOk`), so `allocAb` gives its
`allocAb_hello1`.
-/
import Spike.Lib.X64AllocGAb
import Spike.Test.X64AllocPhHello1
import Spike.Test.X64AllocAbOkHello1
import Spike.Test.X64Hello1AllocW
import Spike.Test.X64Hello1AllocCtr

namespace Spike.Test.X64AllocGHello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide FragS Frag)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerA (WrAt SFactsSt)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Hello1.Inst
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End)
open Spike.Lib.X64.Alloc (Call AllocW N)
open Spike.Test.X64ArenaHello1 (ar)
open Spike.Test.X64Hello1RtW (hello1_instOk)
open Spike.Test.X64AllocPhHello1 (hello1_allocPhOk)
open Spike.Test.X64AllocAbOkHello1 (hello1_allocAbOk)
open SccCode (hello1Λ hello1Cells)

/-- `hello1Cells` hold the allocator's code. -/
theorem hello1_allocIn : Spike.Lib.X64.Alloc.allocIn hello1Cells = true := by decide +kernel

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

/-- **`hello1.x`'s `allocArena`** from the generic one. -/
theorem allocArena_hello1 {p : Prog} (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ) :
    AllocW ms q (fun s c => ∀ fs, Spike.Test.X64Hello1W0.ArenaWr0 p s c fs) (fun _ _ => False)
      hello1Exe hello1End R F :=
  Spike.Lib.X64.AllocG.allocArena (hello1_instOk (rS := ⟨0, 0⟩)) hello1_allocIn hR hlo hhi
    (by rw [← hello1_labT]; exact hq) hmem hctr hheap hoff

/-- **`hello1.x`'s `allocCtr`** from the generic one. -/
theorem allocCtr_hello1 {Ctx : Frag isa} (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hmem : ∀ a : BitVec 64, (∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hheap : ms.heap = ar.heap)
    (hctx : ∀ s c, At hello1Exe hello1End R F (N (_root_.Executable.labels hello1Exe).label ms q .rmw) s c →
      Ctx s c) :
    AllocW ms q (fun s c => WrAt s ar.ctrLoc → Ctx s c) (fun _ _ => False) hello1Exe hello1End R F :=
  Spike.Lib.X64.AllocG.allocCtr (hello1_instOk (rS := ⟨0, 0⟩)) hello1_allocIn hR hlo hhi
    (by rw [← hello1_labT]; exact hq) hmem hheap (by decide) (by decide)
    (by rw [← hello1_labT]; exact hctx)

/-- **`hello1.x`'s `allocPc`** from the generic one. -/
theorem allocPc_hello1 :
    AllocW ms q (fun s _ => okPc (pcOf s) = true) (fun _ _ => False) hello1Exe hello1End R F :=
  Spike.Lib.X64.AllocG.allocPc (hello1_instOk (rS := ⟨0, 0⟩)) hello1_allocPhOk

/-- **`hello1.x`'s `allocSt`** from the generic one: the return address
`wc_rodata`'s `.x13` in the allocator's phase. -/
theorem allocSt_hello1 {rS : Range} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -160)
    (hhi : 8 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub hello1Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hra : q.ra = (labT ".Lwc_rodata.x13").toBitVec)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 hello1Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    AllocW ms q (fun s _ => SFactsSt hello1Λ μ0 own rS Tk s) (Kr rS) hello1Exe hello1End R F :=
  Spike.Lib.X64.AllocG.allocSt hello1_instOk hello1_allocIn hello1_allocPhOk (fun _ => rfl) hR hR8 hlo hhi hl hh
    hsub hfit hFO (by rw [← hello1_labT]; exact hq)
    (by rw [hra, Int64.ofBitVec_toBitVec, Spike.Test.X64Hello1RtW.labT_eq_labX]; decide +kernel) hmp hmem hno

/-- **`hello1.x`'s `allocAb`** from the generic one: the return address
`wc_rodata`'s `.x13`, in the allocator's phase and off the write abort's
pcs. -/
theorem allocAb_hello1 (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hra : q.ra = (labT ".Lwc_rodata.x13").toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (fun s _ => Spike.Lib.X64ConsumerA.AbSt μ0 (Spike.Lib.X64.WriteAb.Ab labT) s) (fun _ _ => False)
      hello1Exe hello1End R F :=
  Spike.Lib.X64.AllocG.allocAb (hello1_instOk (rS := ⟨0, 0⟩)) hello1_allocIn hello1_allocPhOk hello1_allocAbOk
    hR hlo hhi (by rw [← hello1_labT]; exact hq)
    (by rw [hra, Int64.ofBitVec_toBitVec, Spike.Test.X64Hello1RtW.labT_eq_labX]; decide +kernel)
    (by rw [hra, Int64.ofBitVec_toBitVec, Spike.Test.X64Hello1W0.labT_eq_labY]; decide +kernel) hmem

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.X64AllocGHello1.allocArena_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocArena_hello1

/-- info: 'Spike.Test.X64AllocGHello1.allocCtr_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocCtr_hello1

/-- info: 'Spike.Test.X64AllocGHello1.allocSt_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocSt_hello1

/-- info: 'Spike.Test.X64AllocGHello1.allocAb_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAb_hello1

end Spike.Test.X64AllocGHello1
