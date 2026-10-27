import Spike.Lib.X64RtAbortSeg
import Spike.Lib.X64AbortStubCode
import Spike.Lib.RtDepthX64

/-!
`print`'s and the allocator's calls with their abort paths on x64
(`Spike/Lib/X64RtAbortSeg.lean`): their axioms; the region premises
(`PrintFits`, `AllocFits`, `hTR`) hold for the caller's region below the
`call` reaching 88 and 200 bytes inside `R`, the form
`RtDepthX64.print_fits` / `alloc_fits` derive them in; at `hello1`'s
`wc_rodata` frame (40 bytes) the allocator's composition needs
`R.lo ≤ -240`, the bound of `hello1_rodata_setupGW`, whose heap abort it
composes by hand. The plugs: `RtDepthX64.print_fits` / `alloc_fits` give
`PrintFits` / `AllocFits` as stated.
-/

namespace Spike.Lib.X64.RtAbort.Test

open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.RtAbort CoreTerm

/--
info: 'Spike.Lib.X64.print_call_abort_segW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms print_call_abort_segW

/--
info: 'Spike.Lib.X64.newBuf_call_abortW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms newBuf_call_abortW

/--
info: 'Spike.Lib.X64.Abort.Disp.seg_jabort4W' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64.Abort.Disp.seg_jabort4W

/--
info: 'Spike.Lib.X64.StubW.stubHW_of_code' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64.StubW.stubHW_of_code

/--
info: 'Spike.Lib.X64.StubW.stubWW_of_code' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64.StubW.stubWW_of_code

/-- A callee of a callee is a callee at the sum of the offsets. -/
theorem callee2 (T : Region) (a lo hi b lo' hi' : Int) :
    (T.callee a lo hi).callee b lo' hi' = T.callee (a + b) lo' hi' := by
  simp only [Region.callee, Region.addr, BitVec.ofInt_add, BitVec.add_assoc]

/-- A callee region's facts: `OK`, inside `T`. -/
theorem callee_in {T : Region} {kc lo hi : Int} (hT : T.OK) (hlo : T.lo ≤ kc + lo) (hlo0 : lo ≤ 0)
    (hkc : kc < T.hi) (hhi : kc + hi ≤ T.hi) :
    (T.callee kc lo hi).OK ∧ (T.callee kc lo hi).lo ≤ lo ∧ hi ≤ (T.callee kc lo hi).hi ∧
      T.lo ≤ kc + (T.callee kc lo hi).lo ∧ kc + (T.callee kc lo hi).hi ≤ T.hi :=
  ⟨Region.callee_ok hT hlo hlo0 hkc hhi, Int.le_refl _, Int.le_refl _, hlo, hhi⟩

/-- `PrintFits` for a caller's region reaching 88 bytes below the `call`. -/
theorem printFits_of {T : Region} (hT : T.OK) (hlo : T.lo ≤ -88) (hhi : 0 ≤ T.hi) : PrintFits T := by
  intro lab c0 rbp0 ra
  have he : (Spike.Lib.X64.Print.E lab c0 rbp0 ra .abort).o.sp = -40 := rfl
  have h8 : Spike.Lib.X64.Print.oE.sp = 8 := rfl
  have h8' : Spike.Lib.X64.Abort.oE.sp = 8 := rfl
  simp only [he, h8, h8', callee2]
  exact ⟨callee_in hT (by omega) (by omega) (by omega) (by omega), rfl,
    callee_in hT (by omega) (by omega) (by omega) (by omega)⟩

/-- `AllocFits` for a caller's region reaching 200 bytes below the `call`. -/
theorem allocFits_of {T : Region} (hT : T.OK) (hlo : T.lo ≤ -200) (hhi : 0 ≤ T.hi) : AllocFits T := by
  intro lab ms q lbl
  have he : (Spike.Lib.X64.Alloc.E lab ms q lbl .abort).o.sp = -160 := rfl
  have h0 : (Spike.Lib.X64.Alloc.N lab ms q .e).o.sp = 0 := rfl
  have h8' : Spike.Lib.X64.Abort.oE.sp = 8 := rfl
  simp only [he, h0, h8', callee2]
  exact ⟨callee_in hT (by omega) (by omega) (by omega) (by omega), rfl,
    callee_in hT (by omega) (by omega) (by omega) (by omega)⟩

/-- The premises at the caller's region `R.callee kc (-88) 0` below a `call`
at `kc` inside `R`. -/
example {R : Region} {kc : Int} (hR : R.OK) (hd : R.lo ≤ kc - 88) (hkc : kc < R.hi) :
    PrintFits (R.callee kc (-88) 0) ∧ R.lo ≤ kc + (R.callee kc (-88) 0).lo :=
  ⟨printFits_of (Region.callee_ok hR (by omega) (by omega) hkc (by omega)) (by simp [Region.callee])
    (by simp [Region.callee]), by simp only [Region.callee]; omega⟩

/-- The premises at the caller's region `R.callee kc (-200) 0`. -/
example {R : Region} {kc : Int} (hR : R.OK) (hd : R.lo ≤ kc - 200) (hkc : kc < R.hi) :
    AllocFits (R.callee kc (-200) 0) ∧ R.lo ≤ kc + (R.callee kc (-200) 0).lo :=
  ⟨allocFits_of (Region.callee_ok hR (by omega) (by omega) hkc (by omega)) (by simp [Region.callee])
    (by simp [Region.callee]), by simp only [Region.callee]; omega⟩

/-- At `wc_rodata`'s frame of 40 bytes, the allocator's heap abort path
reaches 240 bytes below the frame's entry: `allocAbortDepth 40 + 32`. -/
example {T : Region} (h : AllocFits T) (ms : MemSide Kraken.Promising.X64.isa)
    (q : Spike.Lib.X64.Alloc.Call) (lbl : WeakMem.AllocLabel → Option Nat) {R : Region}
    (hTR : R.lo ≤ -40 + T.lo) : R.lo ≤ -Flow.NewBuf.allocAbortDepth 40 - 32 := by
  have := h.lo ms q lbl
  rw [Flow.NewBuf.allocAbortDepth_40]; omega

/-- **Plug**: `RtDepthX64.print_fits` gives `PrintFits` from the `rtDepth`
entry of `print`. -/
theorem printFits_of_depth {d : Nat} (hd : Scc.Cert.Code1X64.rtDepth.lookup Scc.Lower.Names.print = some d)
    {T : Region} (hT : T.OK) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int)) : PrintFits T :=
  fun lab c0 rbp0 ra => RtDepthX64.print_fits hd hT hhi hlo lab c0 rbp0 ra

/-- **Plug**: `RtDepthX64.alloc_fits` gives `AllocFits` from the `rtDepth`
entry of the allocator. -/
theorem allocFits_of_depth {d : Nat} (hd : Scc.Cert.Code1X64.rtDepth.lookup Scc.Lower.Names.alloc = some d)
    {T : Region} (hT : T.OK) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int)) : AllocFits T :=
  fun lab ms q lbl => RtDepthX64.alloc_fits hd hT hhi hlo lab ms q lbl

end Spike.Lib.X64.RtAbort.Test
