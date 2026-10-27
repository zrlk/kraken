import Spike.Lib.A64RtAbortSeg
import Spike.Lib.A64AbortStubCode
import Spike.Lib.RtDepthA64

/-!
`print`'s and the allocator's calls with their abort paths
(`Spike/Lib/A64RtAbortSeg.lean`): their axioms; the region premises
(`PrintFits`, `AllocFits`, `hTR`) hold for the caller's region below the
`bl` reaching the `rtDepth` entries (96, 208) inside a 16-aligned region
`R`, the form `RtDepthA64.print_fits` / `alloc_fits` derive them in; at
`hello1`'s `wc_rodata` frame (48 bytes) the allocator's composition needs
`R.lo ≤ -256`, the bound of `hello1_rodata_setupW`, whose heap abort it
composes by hand. The plugs: `RtDepthA64.print_fits` / `alloc_fits` give
`PrintFits` / `AllocFits` as stated.
-/

namespace Spike.Lib.A64.Flow.RtAbort.Test

open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.RtAbort CoreTerm

/--
info: 'Spike.Lib.A64.Flow.print_call_abort_segW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms print_call_abort_segW

/--
info: 'Spike.Lib.A64.Flow.newBuf_call_abortW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms newBuf_call_abortW

/--
info: 'Spike.Lib.A64.Abort.Disp.seg_jabort4W' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.A64.Abort.Disp.seg_jabort4W

/--
info: 'Spike.Lib.A64.StubW.stubHW_of_code' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.A64.StubW.stubHW_of_code

/--
info: 'Spike.Lib.A64.StubW.stubWW_of_code' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.A64.StubW.stubWW_of_code

/-- The region facts below a call at `kc` reaching `d ≥ 48 + 48` bytes. -/
theorem fits_at {R : Region} {kc d e : Int} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hk16 : kc % 16 = 0)
    (hd : R.lo ≤ kc - d) (hkc : kc < R.hi) (he : e < 0) (he16 : e % 16 = 0) (hed : e - 48 ≥ -d) :
    let T := R.callee kc (-d) 0
    T.OK ∧ (T.callee e (-48) 0).OK ∧ (T.callee e (-48) 0).base.toNat % 16 = 0 ∧
      (T.callee e (-48) 0).lo ≤ -48 ∧ 0 ≤ (T.callee e (-48) 0).hi ∧ T.lo ≤ e + (T.callee e (-48) 0).lo ∧
      e + (T.callee e (-48) 0).hi ≤ T.hi := by
  intro T
  have hT : T.OK := Region.callee_ok hR (by omega) (by omega) hkc (by omega)
  have hbT := Region.callee_base (hi' := 0) hR (kc := kc) (lo' := -d) (by omega) (by omega) hkc
  have hb := Region.callee_base (hi' := 0) hT (kc := e) (lo' := -48) (by simp [T, Region.callee]; omega)
    (by omega) (by simp [T, Region.callee]; omega)
  refine ⟨hT, Region.callee_ok hT (by simp [T, Region.callee]; omega) (by omega)
    (by simp [T, Region.callee]; omega) (by simp [T, Region.callee]; omega), ?_,
    Int.le_refl _, Int.le_refl _, by simp only [T, Region.callee]; omega, by simp only [T, Region.callee]; omega⟩
  simp only [T] at hbT hb ⊢
  omega

/-- `PrintFits` for the caller's region reaching `print`'s 96 bytes below the `bl`. -/
example {R : Region} {kc : Int} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hk16 : kc % 16 = 0)
    (hd : R.lo ≤ kc - 96) (hkc : kc < R.hi) :
    PrintFits (R.callee kc (-96) 0) ∧ R.lo ≤ kc + (R.callee kc (-96) 0).lo := by
  refine ⟨fun lab c0 x29 ra => ?_, by simp only [Region.callee]; omega⟩
  obtain ⟨-, h⟩ := fits_at (e := -48) hR hal hk16 hd hkc (by decide) (by decide) (by decide)
  exact ⟨by simp only [Region.callee]; omega, h⟩

/-- `AllocFits` for the caller's region reaching the allocator's 208 bytes below the `bl`. -/
example {R : Region} {kc : Int} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hk16 : kc % 16 = 0)
    (hd : R.lo ≤ kc - 208) (hkc : kc < R.hi) :
    AllocFits (R.callee kc (-208) 0) ∧ R.lo ≤ kc + (R.callee kc (-208) 0).lo := by
  refine ⟨fun lab ms q lbl => ?_, by simp only [Region.callee]; omega⟩
  obtain ⟨-, h⟩ := fits_at (e := -160) hR hal hk16 hd hkc (by decide) (by decide) (by decide)
  exact ⟨by simp only [Region.callee]; omega, h⟩

/-- At `wc_rodata`'s frame of 48 bytes, the allocator's heap abort path
reaches 256 bytes below the frame's entry: `allocAbortDepth 48 + 48`. -/
example {T : Region} (h : AllocFits T) (ms : MemSide Kraken.Promising.AArch64.isaLSE2)
    (q : Spike.Lib.A64.Alloc.Call) (lbl : WeakMem.AllocLabel → Option Nat) {R : Region}
    (hTR : R.lo ≤ -48 + T.lo) : R.lo ≤ -NewBuf.allocAbortDepth 48 - 48 := by
  have := h.lo ms q lbl
  rw [NewBuf.allocAbortDepth_48]; omega

/-- **Plug**: `RtDepthA64.print_fits` gives `PrintFits` from the `rtDepth`
entry of `print`. -/
theorem printFits_of_depth {d : Nat} (hd : Scc.Cert.Code1A64.rtDepth.lookup Scc.Lower.Names.print = some d)
    {T : Region} (hT : T.OK) (hal : T.base.toNat % 16 = 0) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int)) :
    PrintFits T :=
  fun lab c0 x29 ra => RtDepthA64.print_fits hd hT hal hhi hlo lab c0 x29 ra

/-- **Plug**: `RtDepthA64.alloc_fits` gives `AllocFits` from the `rtDepth`
entry of the allocator. -/
theorem allocFits_of_depth {d : Nat} (hd : Scc.Cert.Code1A64.rtDepth.lookup Scc.Lower.Names.alloc = some d)
    {T : Region} (hT : T.OK) (hal : T.base.toNat % 16 = 0) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int)) :
    AllocFits T :=
  fun lab ms q lbl => RtDepthA64.alloc_fits hd hT hal hhi hlo lab ms q lbl

end Spike.Lib.A64.Flow.RtAbort.Test
