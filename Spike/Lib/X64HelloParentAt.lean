/-
**hello.w on x86-64: main after the `clone` is at the parent's node** (the twin of
`Spike/Lib/A64HelloParentAt.lean`; wake's x86-64 version is `Spike/Lib/X64WakeParentAt.lean`): main at its
`clone` in a region `R` at offsets `oP` with `JS`, once the kernel erases the handed range `r1` from its private
memory and returns the child's id `0 < r < pidMax` (`retRegs64`: `%rax` the id, `%rcx` the next pc, `%r11` the
flags), is in `At` of `Hello.Parent.pN … .ts`, so `seg_parent` runs it to `wc_waitLoop`'s entry.

The handed range meets no cell of `R` (wake's `RegionDisj`, `regionDisj_of_sub`), so the erase leaves the
region's cells (`WakePh.Parent.loadInt_eraseRange'`).

- `parent_atH`: the above, at any pc `q` holding the `syscall` (`hcode`, `.x25 + 94`: `hq`).
- `parent_at_preH`: from main's state at its `clone` (`ClonePreH`: `r1` off main's range `r0`, which holds the
  frame) in a layout of `helloCells`, for a region based 128 above `%rsp` (`hRb`, `wc_main`'s `%rbp`) with
  offsets in `[-128, 96]` (`wc_main`'s frame below `%rbp`, the saved `%rbp`, the return address and
  `scc_rt_main`'s 80 bytes above it, the top of `r0`: `ClonePreH.spTop`).

## Differences from the AArch64 version

- As wake's x86-64 version: the parent's node past the `syscall` is `pN .ts` (the clone's result test; A64's
  `.cb`), at `q + 2` (A64's `q + 4`); the registers after the return are `retRegs64` (`syscallStep` on the
  abstract side; A64's `X0` only); no label prefix `pfx`.
- The region is based at `wc_main`'s `%rbp`, 128 above `%rsp` (`oP = ⟨-128, [(.rbp, 0)]⟩`), its offsets within
  `[-128, 96]` (A64's base 144 above `sp`, offsets within `[-144, 80]`).
- A64's `atJS_of_postH` is dead and not twinned.
-/
import Spike.Lib.X64HelloParent
import Spike.Lib.X64HelloChildAt
import Spike.Lib.X64WakeParentAt
import Spike.Lib.X64HelloClonePreH

namespace Spike.Lib.X64.Flow.Worker.Hello.Parent

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker.Hello.Child (x25L hello_svcIn)
open Spike.Lib.X64.WakePh.WcClone (svcB)
open Spike.Lib.X64.WakePh.Parent (loadInt_eraseRange' RegionDisj regionDisj_of_sub)
open Spike.Lib.X64HelloPreA (cloneAtH ClonePreH)
open Scc.Cert.Rt.X64 (Lays endOf codeAt_blockAt_lays)
open SccCode (helloCells)

/-- **The parent after the `clone` is at `pN .ts`**: main at the clone's `syscall` (pc `q`, a 2-byte cell
there: `hcode`; `.x25 + 94`: `hq`) in region `R` at offsets `oP` with `JS`, whose handed range `r1` (ending at
the stack top `stack`: `hh`) meets no cell of `R` (`hdisj`), is, once the kernel returns the child's id
`0 < r < pidMax`, in `At` of `pN .ts` for the frame condition its memory outside the region. -/
theorem parent_atH {exe : _root_.Executable} {endPc : Int64} {q : Int64} {x : KState}
    {tid : Nat} {t : Thread isa} {r1 : Range} {stack : Nat} {r : BitVec 64} {R : Region}
    {F : MachineData → Prop} {cP : Ctl} {A fp ra tp : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s q svcB)
    (hq : (_root_.Executable.labels exe).label x25L + 94 = q)
    (hat : At exe endPc R F ⟨q, oP, JS cP A fp ra tp⟩ t.st cP)
    (hh : handed x tid stack = some (tid, r1)) (hr1 : r1.lo + r1.size ≤ 2 ^ 64)
    (hR : R.OK) (hdisj : RegionDisj R r1)
    (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax) :
    At exe endPc R (DFrame R (Kernel.retThread abi (parentPre abi x tid t stack) r).st.st.1)
      (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts)
      (Kernel.retThread abi (parentPre abi x tid t stack) r).st cP := by
  obtain ⟨he, hn, hd, hpc, σ, hA, -, hJ⟩ := hat
  change t.st.st.2 = q at hpc
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
    rw [hnext, hpc, ← hq, Int64.add_assoc]; rfl
  · show retRegs64 t.st r = syscallRegs (nextPc t.st) (rflags σ.status) r σ.regs
    simp only [retRegs64, syscallRegs, hA.regs, hA.status]
  · have h := syscallSO_rel hA.so (nextPc t.st) (rflags σ.status) r
    rwa [show syscallSO oP = oP from rfl] at h
  · intro k hk
    obtain ⟨j, hj, hjv⟩ := hA.slot k hk
    have hak := Region.addr_toNat hR hk
    obtain ⟨-, hk1, hk2⟩ := hk
    refine ⟨j, ?_, hjv⟩
    show Mem.loadInt (eraseRange t.st.st.1.dmem r1) (R.addr k) 8 = some j
    rw [loadInt_eraseRange' hr1 (by have := hR.hi; omega) (by unfold RegionDisj at hdisj; omega)]
    exact hj
  · obtain ⟨h1, h48, h0, h8, htp⟩ := hJ
    have hX : (UInt64.ofNat r.toNat).toBitVec = r := by show BitVec.ofNat 64 r.toNat = r; simp
    refine ⟨⟨h1, h48, h0, h8, ?_⟩, ?_, ?_⟩
    · simpa [syscallStep, syscallRegs] using htp
    · show 0 < (UInt64.ofNat r.toNat).toBitVec.toNat; rw [hX]; exact hr0
    · show (UInt64.ofNat r.toNat).toBitVec.toNat < _; rw [hX]; exact hrm

/-- **The parent after main's `clone` is at `pN .ts`** (hello's layout `hp`): main's state at the clone
(`ClonePreH`) whose thread `th` is in `At` of the clone's node with `JS` (`hat`), for a region based 128 above
`%rsp` (`hRb`) with offsets within `[-128, 96]` (`hRlo`, `hRhi`). Once the clone hands `r1` and the kernel
returns the child's id `0 < r < pidMax`, `th` is in `At` of `pN .ts` with the frame condition its memory
outside the region. `r1` meets no cell of the region: `ClonePreH.disj`, `frame` and `spTop`. -/
theorem parent_at_preH {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePreH Λ r0 r1 X lbl t s)
    {R : Region} {F : MachineData → Prop} {cP : Ctl} {A fp ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F ⟨cloneAtH exe, oP, JS cP A fp ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isa, t.1.threads = #[th] →
      (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 128)
    (hRlo : -128 ≤ R.lo) (hRhi : R.hi ≤ 96) (hlh : R.lo ≤ R.hi) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧
      At exe endPc R (DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1)
        (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts)
        (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  have hd := h.disj
  obtain ⟨th, hth, hf0, -⟩ := h.frame
  obtain ⟨th', hth', htop0, -⟩ := h.spTop
  rw [hth] at hth'
  obtain rfl : th = th' := by simpa using hth'
  have hh : handed t.2 0 (r1.lo + r1.size) = some (0, r1) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hheld, -⟩ := h
    simp [handed, hheld]
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (cloneAtH exe) svcB :=
    fun s he hn => codeAt_blockAt_lays hp he (hn.trans hend) hello_svcIn
  have hb := hRb th hth
  exact ⟨th, hth, parent_atH hcode rfl (hat th hth) hh htop hR
    (regionDisj_of_sub hd (by omega) (by omega) hlh) hr0 hrm⟩

end Spike.Lib.X64.Flow.Worker.Hello.Parent

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Parent.parent_atH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Parent.parent_atH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Parent.parent_at_preH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Parent.parent_at_preH
