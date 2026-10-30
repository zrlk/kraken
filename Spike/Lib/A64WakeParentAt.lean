/-
**wake.w on AArch64: main after the `clone` is at the parent's node**
(the spawn's parent half): the parent thread the kernel
returns to (`Kernel.retThread abi (parentPre …)`, `x0` the child's id, the
handed range `r1` erased from its private memory:
`Spike.Lib.A64Handover.parent_st`) is in the fragment `At … (pN … .cb)` of
`Spike.Lib.A64.Flow.Worker.Wake.Parent`, so `seg_parent` runs it.

Main's frame survives the erase: no cell of the region meets `r1`
(`hdisj`; from wake's `ClonePre`, `r1` is disjoint from main's stack range
`r0`, which holds the region: `regionDisj_of_sub`). The frame condition is
the parent's memory outside the region (`DFrame`, stable: `FStable.dframe`).

- `loadInt_eraseRange`: an 8-byte load off the erased range is unchanged.
- `RegionDisj`: no cell of the region meets the range.
- `regionDisj_of_sub`: a region inside a range disjoint from `rg`.
- `parent_at`: the parent after a `clone` whose stack range is handed is at
  `pN .cb`, from main at the clone's `svc` with `JS`.
- `parent_at_preR`: from main's state at its `clone` for any region inside
  main's stack range `r0` (`hin`).
- `parent_at_pre`: the same from main's state at its `clone`
  (`Spike.Lib.WakePreA.ClonePre`: `r1` off main's range `r0`, which holds
  the frame) in a layout of `wakeProg`, for main's region at `sp`
  (offsets `[-80, 0)` from the frame's top, `hRb`/`hRlo`/`hRhi`).
-/
import Spike.Lib.A64WakeParent
import Spike.Lib.A64WakeChildAt

namespace Spike.Lib.A64.Flow.Worker.Wake.Parent

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Child (svcB pfxM)
open Spike.Lib.WakePreA (cloneAt)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.WakeLabels (wakeProg)

/-- **An 8-byte load off the erased range is unchanged** (the range not
wrapping, the load's bytes `[a, a + 8)` off it). -/
theorem loadInt_eraseRange {m : _root_.Mem 64} {rg : Range} {a : BitVec 64} (hr : rg.lo + rg.size ≤ 2 ^ 64)
    (ha : a.toNat + 8 ≤ 2 ^ 64) (hd : a.toNat + 8 ≤ rg.lo ∨ rg.lo + rg.size ≤ a.toNat) :
    Mem.loadInt (eraseRange m rg) a 8 = Mem.loadInt m a 8 := by
  simp only [Mem.loadInt, Mem.loadBytes]
  congr 2
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?, get_eraseRange, ite_eq_right_iff.mpr (fun h => absurd h ?_)]
  rw [mem_addrs_iff hr]
  have : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  unfold Range.contains
  omega

/-- **No cell of the region meets the range `rg`.** -/
def RegionDisj (R : Spike.Lib.Region) (rg : Range) : Prop :=
  (rg.lo + rg.size : Int) ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ rg.lo

/-- **A region inside a range `r0` disjoint from `rg`** meets no cell of
`rg`. -/
theorem regionDisj_of_sub {R : Spike.Lib.Region} {r0 rg : Range} (hd : rg.Disjoint r0)
    (h0 : (r0.lo : Int) ≤ R.base.toNat + R.lo) (h1 : (R.base.toNat : Int) + R.hi ≤ r0.lo + r0.size)
    (_hlh : R.lo ≤ R.hi) : RegionDisj R rg := by
  unfold RegionDisj
  unfold Range.Disjoint at hd
  omega

/-- **The parent after the `clone` is at `pN .cb`**: main at the clone's
`svc` (`cloneAt pfxM exe`, a 4-byte cell there: `hcode`) in region `R` at
offsets `oP` with `JS`, whose handed range `r1` (ending at the stack top
`stack`: `hh`) meets no cell of `R` (`hdisj`), is, once the kernel returns
the child's id `0 < r < pidMax`, in `At` of `pN .cb` for the frame
condition its memory outside the region. -/
theorem parent_at {exe : _root_.Executable} {endPc : Int64} {x : KState} {tid : Nat}
    {t : Thread isaLSE2} {r1 : Range} {stack : Nat} {r : BitVec 64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (cloneAt pfxM exe) svcB)
    (hat : At exe endPc R F ⟨cloneAt pfxM exe, oP, JS cP A x29 ra tp⟩ t.st cP)
    (hh : handed x tid stack = some (tid, r1)) (hr1 : r1.lo + r1.size ≤ 2 ^ 64)
    (hR : R.OK) (hdisj : RegionDisj R r1)
    (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax) :
    At exe endPc R (DFrame R (Kernel.retThread abi (parentPre abi x tid t stack) r).st.st.1)
      (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cb)
      (Kernel.retThread abi (parentPre abi x tid t stack) r).st cP := by
  obtain ⟨he, hn, hd, hpc, σ, hA, -, hJ⟩ := hat
  change t.st.st.2 = cloneAt pfxM exe at hpc
  have hc : (Kernel.retThread abi (parentPre abi x tid t stack) r).st =
      { t.st with st := ({ t.st.st.1 with
          regs := { t.st.st.1.regs with X0 := UInt64.ofNat r.toNat },
          dmem := eraseRange t.st.st.1.dmem r1 }, nextPc t.st) } := by
    rw [Kernel.retThread_st]; unfold parentPre; rw [hh]; rfl
  obtain ⟨d0, hd0⟩ : ∃ d, svcB[0]? = some d := ⟨_, rfl⟩
  have hcell : CellAt t.st d0 4 := by
    have := hcode t.st he hn 0 d0 hd0
    rw [ofNat4_zero, ← hpc] at this
    exact this
  have hnext := nextPc_of_cellAt hcell
  have hX0 : (UInt64.ofNat r.toNat).toBitVec = r := by
    show BitVec.ofNat 64 r.toNat = r
    simp
  rw [hc]
  refine ⟨he, hn, hd, ?_, ⟨{ σ with regs := { σ.regs with X0 := UInt64.ofNat r.toNat } }, ⟨?_, hA.status, ?_, ?_⟩,
    DFrame.refl _ _, ?_⟩⟩
  · show nextPc t.st = _
    rw [hnext, hpc]; rfl
  · show { t.st.st.1.regs with X0 := UInt64.ofNat r.toNat } = { σ.regs with X0 := UInt64.ofNat r.toNat }
    rw [hA.regs]
  · intro rr k hk
    cases rr with
    | SP => exact hA.so .SP k hk
    | reg xr => simp [SO.get, pN, oP, lk] at hk
  · intro k hk
    have hak := Spike.Lib.Region.addr_toNat hR hk
    obtain ⟨j, hj, hjv⟩ := hA.slot k hk
    obtain ⟨-, hk1, hk2⟩ := hk
    refine ⟨j, ?_, hjv⟩
    show Mem.loadInt (eraseRange t.st.st.1.dmem r1) (R.addr k) 8 = some j
    rw [loadInt_eraseRange hr1 (by have := hR.hi; omega) (by unfold RegionDisj at hdisj; omega)]
    exact hj
  · obtain ⟨h1, h72, h16, h8, htp⟩ := hJ
    refine ⟨⟨h1, h72, h16, h8, htp⟩, ?_, ?_⟩ <;> simp only [hX0] <;> assumption

/-- **The parent after main's `clone` is at `pN .cb`**, for any region
inside main's stack range `r0` (`hin`; `r1` is off `r0`: `ClonePre.disj`). -/
theorem parent_at_preR {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : Spike.Lib.WakePreA.ClonePre pfxM Λ r0 r1 X lbl t s)
    {R : Spike.Lib.Region} {F : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F ⟨cloneAt pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP)
    (hin : (r0.lo : Int) ≤ R.base.toNat + R.lo ∧ (R.base.toNat : Int) + R.hi ≤ r0.lo + r0.size)
    (hlh : R.lo ≤ R.hi) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧
      At exe endPc R (DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1)
        (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cb)
        (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  have hd := h.disj
  obtain ⟨th, hth, -, -⟩ := h.frame
  have hh : handed t.2 0 (r1.lo + r1.size) = some (0, r1) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hh, -⟩ := h
    simp [handed, hh]
  have hcode := code_of hp hend Spike.Lib.A64.Flow.Worker.Wake.Child.wake_svcIn (q := cloneAt pfxM exe) rfl
  exact ⟨th, hth, parent_at hcode (hat th hth) hh htop hR (regionDisj_of_sub hd hin.1 hin.2 hlh) hr0 hrm⟩

/-- **The parent after main's `clone` is at `pN .cb`** (wake's layout `hp`):
main's state at the clone (`ClonePre`) whose thread `th` is in `At` of the
clone's node with `JS` (`hat`), for a region of main's frame: base `sp + 80`
(`hRb`), offsets within `[-80, 0]` (`hRlo`, `hRhi`). Once the clone hands
`r1` and the kernel returns the child's id `0 < r < pidMax`, `th` is in `At`
of `pN .cb` with the frame condition its memory outside the region. `r1`
meets no cell of the region: `ClonePre.disj` and `ClonePre.frame`. -/
theorem parent_at_pre {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : Spike.Lib.WakePreA.ClonePre pfxM Λ r0 r1 X lbl t s)
    {R : Spike.Lib.Region} {F : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F ⟨cloneAt pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 80)
    (hRlo : -80 ≤ R.lo) (hRhi : R.hi ≤ 0) (hlh : R.lo ≤ R.hi) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧
      At exe endPc R (DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1)
        (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cb)
        (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  have hd := h.disj
  obtain ⟨th, hth, hf0, hf1⟩ := h.frame
  have hheld := h.held
  have hh : handed t.2 0 (r1.lo + r1.size) = some (0, r1) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hh, -⟩ := h
    simp [handed, hh]
  have hcode := code_of hp hend Spike.Lib.A64.Flow.Worker.Wake.Child.wake_svcIn (q := cloneAt pfxM exe) rfl
  have hb := hRb th hth
  refine ⟨th, hth, parent_at hcode (hat th hth) hh htop hR
    (regionDisj_of_sub hd (by omega) (by omega) hlh) hr0 hrm⟩

end Spike.Lib.A64.Flow.Worker.Wake.Parent
