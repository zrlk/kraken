/-
**wake.w on x86-64: main after the `clone` is at the parent's node** (the
twin of `Spike/Lib/A64WakeParentAt.lean`'s `parent_at`): the parent thread
the kernel returns to (`Kernel.retThread abi (parentPre …)`: `retRegs64`,
so `%rax` the child's id, `%rcx` the next pc, `%r11` the flags; the handed
range `r1` erased from its private memory: `Spike.Lib.X64Handover`) is in
the fragment `At … (pN … .ts)` of `Spike.Lib.X64.WakePh.Parent`, so
`seg_parent` runs it.

Main's frame survives the erase: no cell of the region meets `r1`
(`RegionDisj`, A64's, which is ISA-neutral). The frame condition is the
parent's memory outside the region (`DFrame`).

- `loadInt_eraseRange'`: an 8-byte load off the erased range is unchanged
  (A64's `loadInt_eraseRange`, restated: that one lives in an AArch64 module).
- `parent_at`: the parent after a `clone` whose stack range is handed is at
  `pN .ts`, from main at the clone's `syscall` with `JS` (the clone's
  register facts are not needed past it: `JS` is about the frame and
  `fsBase`, which the `syscall` keeps).
-/
import Spike.Lib.X64WakeParent
import Spike.Lib.X64Handover
import Scc.Sem.SysX64
import Scc.Sem.OwnDom

namespace Spike.Lib.X64.WakePh.Parent

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (oW x21L svcB)

/-- **An 8-byte load off the erased range is unchanged** (the range not
wrapping, the load's bytes `[a, a + 8)` off it). -/
theorem loadInt_eraseRange' {m : _root_.Mem 64} {rg : Range} {a : BitVec 64} (hr : rg.lo + rg.size ≤ 2 ^ 64)
    (ha : a.toNat + 8 ≤ 2 ^ 64) (hd : a.toNat + 8 ≤ rg.lo ∨ rg.lo + rg.size ≤ a.toNat) :
    Mem.loadInt (eraseRange m rg) a 8 = Mem.loadInt m a 8 := by
  simp only [Mem.loadInt, Mem.loadBytes]
  congr 2
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?, get_eraseRange,
    ite_eq_right_iff.mpr (fun h => absurd h ?_)]
  rw [mem_addrs_iff hr]
  have : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  unfold Range.contains
  omega

/-- **No cell of the region meets the range `rg`** (A64's `RegionDisj`). -/
def RegionDisj (R : Region) (rg : Range) : Prop :=
  (rg.lo + rg.size : Int) ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ rg.lo

/-- **A region inside a range `r0` disjoint from `rg`** meets no cell of `rg`. -/
theorem regionDisj_of_sub {R : Region} {r0 rg : Range} (hd : rg.Disjoint r0)
    (h0 : (r0.lo : Int) ≤ R.base.toNat + R.lo) (h1 : (R.base.toNat : Int) + R.hi ≤ r0.lo + r0.size)
    (_hlh : R.lo ≤ R.hi) : RegionDisj R rg := by
  unfold RegionDisj
  unfold Range.Disjoint at hd
  omega

/-- **The parent after the `clone` is at `pN .ts`**: main at the clone's
`syscall` (`.x21 + 46`, a 2-byte cell there: `hcode`) in region `R` at
offsets `oW` with `JS`, whose handed range `r1` (ending at the stack top
`stack`: `hh`) meets no cell of `R` (`hdisj`), is, once the kernel returns
the child's id `0 < r < pidMax`, in `At` of `pN .ts` for the frame
condition its memory outside the region. -/
theorem parent_at {exe : _root_.Executable} {endPc : Int64} {x : KState} {tid : Nat}
    {t : Thread isa} {r1 : Range} {stack : Nat} {r : BitVec 64} {R : Region} {F : MachineData → Prop}
    {cP : Ctl} {A fp ra tp : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label x21L + 46) svcB)
    (hat : At exe endPc R F ⟨(_root_.Executable.labels exe).label x21L + 46, oW, JS cP A fp ra tp⟩ t.st cP)
    (hh : handed x tid stack = some (tid, r1)) (hr1 : r1.lo + r1.size ≤ 2 ^ 64)
    (hR : R.OK) (hdisj : RegionDisj R r1)
    (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax) :
    At exe endPc R (DFrame R (Kernel.retThread abi (parentPre abi x tid t stack) r).st.st.1)
      (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts)
      (Kernel.retThread abi (parentPre abi x tid t stack) r).st cP := by
  obtain ⟨he, hn, hd, hpc, σ, hA, -, hJ⟩ := hat
  change t.st.st.2 = _ at hpc
  have hc : (Kernel.retThread abi (parentPre abi x tid t stack) r).st =
      { t.st with
        st := (({ t.st.st.1 with
                  regs := retRegs64 t.st r
                  dmem := eraseRange t.st.st.1.dmem r1 } : MachineData), nextPc t.st) } := by
    rw [Kernel.retThread_st]; unfold parentPre; rw [hh]; rfl
  have hcell : CellAt t.st (op64 .syscall) 2 := (hcode t.st he hn).cell0 rfl rfl hpc
  have hnext := nextPc_of_cellAt hcell
  rw [hc]
  refine ⟨he, hn, hd, ?_, ⟨syscallStep (nextPc t.st) r σ, ⟨?_, hA.zmms, hA.status, ?_, ?_⟩,
    DFrame.refl _ _, ?_⟩⟩
  · show nextPc t.st = _
    rw [hnext, hpc, Int64.add_assoc]; rfl
  · show retRegs64 t.st r = syscallRegs (nextPc t.st) (rflags σ.status) r σ.regs
    simp only [retRegs64, syscallRegs, hA.regs, hA.status]
  · have h := syscallSO_rel hA.so (nextPc t.st) (rflags σ.status) r
    rwa [show syscallSO oW = oW from rfl] at h
  · intro k hk
    obtain ⟨j, hj, hjv⟩ := hA.slot k hk
    have hak := Region.addr_toNat hR hk
    obtain ⟨-, hk1, hk2⟩ := hk
    refine ⟨j, ?_, hjv⟩
    show Mem.loadInt (eraseRange t.st.st.1.dmem r1) (R.addr k) 8 = some j
    rw [loadInt_eraseRange' hr1 (by have := hR.hi; omega) (by unfold RegionDisj at hdisj; omega)]
    exact hj
  · obtain ⟨h1, h16, h0, h8, htp⟩ := hJ
    have hX : (UInt64.ofNat r.toNat).toBitVec = r := by show BitVec.ofNat 64 r.toNat = r; simp
    refine ⟨⟨h1, h16, h0, h8, ?_⟩, ?_, ?_⟩
    · simpa [syscallStep, syscallRegs] using htp
    · show 0 < (UInt64.ofNat r.toNat).toBitVec.toNat; rw [hX]; exact hr0
    · show (UInt64.ofNat r.toNat).toBitVec.toNat < _; rw [hX]; exact hrm

/-- info: 'Spike.Lib.X64.WakePh.Parent.parent_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parent_at

end Spike.Lib.X64.WakePh.Parent
