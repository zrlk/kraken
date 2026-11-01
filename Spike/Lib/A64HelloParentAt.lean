/-
**hello.w on AArch64: the parent after the `clone` is at `pN .cb`** (hello
plan B4, the spawn's parent half; wake's `A64WakeParentAt`): main at its
`clone` in a region `R` at offsets `oP` with `JS`, once the kernel erases
the handed range `r1` from its private memory and returns the child's id
`0 < r < pidMax`, is in `At` of `Hello.Parent.pN … .cb`, so `seg_parent`
runs it to `wc_waitLoop`'s entry.

The handed range meets no cell of `R` (wake's `RegionDisj`,
`regionDisj_of_sub`), so the erase leaves the region's cells
(`Wake.Parent.loadInt_eraseRange`); `x0` becomes the child's id.

- `parent_atH`: the above, at any pc `q` holding the `svc` (`hcode`) and
  `pN .cb`'s pc `q + 4` (`hq`).
- `parent_at_preH`: from main's state at its `clone` (`ClonePreH`: `r1` off
  main's range `r0`, which holds the frame) in a layout of `helloProg`, for
  a region based 144 above `sp` (`hRb`) with offsets in `[-144, 80]`
  (`wc_main`'s frame and `scc_rt_main`'s 80 bytes above it, the top of
  `r0`: `ClonePreH.spTop`).
- `atJS_of_postH`: `ClonePostH` (B3's state at the clone, `wcNSH`) gives the
  `At` of the clone's node with `JS` that `parent_atH` takes: the cell `cA`
  at `-104`, the caller's pair at `-16`/`-8`, the thread pointer `t`.

Deferred (B4c): main's invariant after the clone (wake's `A64WakeMainAfter`)
needs B5's main-post segment.
-/
import Spike.Lib.A64HelloParent
import Spike.Lib.A64HelloChildAt
import Spike.Lib.A64WakeParentAt
import Spike.Lib.A64HelloClonePreHOf

namespace Spike.Lib.A64.Flow.Worker.Hello.Parent

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM hello_svcIn)
open Spike.Lib.A64.Flow.Worker.Wake.Child (svcB)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (loadInt_eraseRange RegionDisj regionDisj_of_sub)
open Spike.Lib.HelloPreA (cloneAtH ClonePreH ClonePostH)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

/-- **The parent after the `clone` is at `pN .cb`**: main at the clone's
`svc` (pc `q`, a 4-byte cell there: `hcode`; `pN .cb`'s pc `q + 4`: `hq`)
in region `R` at offsets `oP` with `JS`, whose handed range `r1` (ending at
the stack top `stack`: `hh`) meets no cell of `R` (`hdisj`), is, once the
kernel returns the child's id `0 < r < pidMax`, in `At` of `pN .cb` for the
frame condition its memory outside the region. -/
theorem parent_atH {pfx : String} {exe : _root_.Executable} {endPc : Int64} {q : Int64} {x : KState}
    {tid : Nat} {t : Thread isaLSE2} {r1 : Range} {stack : Nat} {r : BitVec 64} {R : Spike.Lib.Region}
    {F : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s q svcB)
    (hq : (_root_.Executable.labels exe).label (pfx ++ ".sp6") + Int64.ofNat (4 * 25) = q)
    (hat : At exe endPc R F ⟨q, oP, JS cP A x29 ra tp⟩ t.st cP)
    (hh : handed x tid stack = some (tid, r1)) (hr1 : r1.lo + r1.size ≤ 2 ^ 64)
    (hR : R.OK) (hdisj : RegionDisj R r1)
    (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax) :
    At exe endPc R (DFrame R (Kernel.retThread abi (parentPre abi x tid t stack) r).st.st.1)
      (pN pfx (_root_.Executable.labels exe).label cP A x29 ra tp .cb)
      (Kernel.retThread abi (parentPre abi x tid t stack) r).st cP := by
  obtain ⟨he, hn, hd, hpc, σ, hA, -, hJ⟩ := hat
  change t.st.st.2 = q at hpc
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
    rw [hnext, hpc, ← hq]; rfl
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
  · obtain ⟨h1, h104, h16, h8, htp⟩ := hJ
    refine ⟨⟨h1, h104, h16, h8, htp⟩, ?_, ?_⟩ <;> simp only [hX0] <;> assumption

/-- **The parent after main's `clone` is at `pN .cb`** (hello's layout
`hp`): main's state at the clone (`ClonePreH`) whose thread `th` is in `At`
of the clone's node with `JS` (`hat`), for a region based 144 above `sp`
(`hRb`) with offsets within `[-144, 80]` (`hRlo`, `hRhi`). Once the clone
hands `r1` and the kernel returns the child's id `0 < r < pidMax`, `th` is
in `At` of `pN .cb` with the frame condition its memory outside the region.
`r1` meets no cell of the region: `ClonePreH.disj`, `frame` and `spTop`. -/
theorem parent_at_preH {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePreH pfxM Λ r0 r1 X lbl t s)
    {R : Spike.Lib.Region} {F : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F ⟨cloneAtH pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 144)
    (hRlo : -144 ≤ R.lo) (hRhi : R.hi ≤ 80) (hlh : R.lo ≤ R.hi) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧
      At exe endPc R (DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1)
        (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cb)
        (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  have hd := h.disj
  obtain ⟨th, hth, hf0, -⟩ := h.frame
  obtain ⟨th', hth', htop0, -⟩ := h.spTop
  rw [hth] at hth'
  obtain rfl : th = th' := by simpa using hth'
  have hh : handed t.2 0 (r1.lo + r1.size) = some (0, r1) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hheld, -⟩ := h
    simp [handed, hheld]
  have hcode := code_of hp hend hello_svcIn (q := cloneAtH pfxM exe) rfl
  have hb := hRb th hth
  exact ⟨th, hth, parent_atH hcode rfl (hat th hth) hh htop hR
    (regionDisj_of_sub hd (by omega) (by omega) hlh) hr0 hrm⟩

/-- **B3's state at the clone gives `JS` at the clone's node**: `ClonePostH`
(`wcNSH` in `wc_main`'s region `R`, its base 144 above `sp`, the thread
pointer `t`) gives, for some region `R` based 144 above `sp` and some frame
condition, `At` of the clone's node at offsets `oP` with `JS c cA fr.1 fr.2
t`: the cell at `-104`, the caller's pair at `-16`/`-8`. -/
theorem atJS_of_postH {L : Spike.Lib.A64.Rt.RuntimeLayout} {endPc : Int64} {t : UInt64} {s : State} {c : Ctl}
    (h : ClonePostH L endPc t s c) :
    ∃ (R : Spike.Lib.Region) (F₂ : MachineData → Prop) (cA : BitVec 64) (fr : BitVec 64 × BitVec 64),
      R.base.toNat % 16 = 0 ∧ (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 144 ∧
      At L.exe endPc R F₂ ⟨cloneAtH pfxM L.exe, oP, JS c cA fr.1 fr.2 t.toBitVec⟩ s c := by
  obtain ⟨R, F₂, tc, k, sl, me, cA, fr, hal, ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩, hb, -, htp, -⟩ := h
  obtain ⟨hc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h104, h16, h8⟩ := hJ
  refine ⟨R, F₂, cA, fr, hal, hb, he, hn, hd, hpc, σ, hA, hF, hc, h104, h16, h8, ?_⟩
  rw [← htp, hA.regs]

end Spike.Lib.A64.Flow.Worker.Hello.Parent

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Parent.parent_at_preH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.Parent.parent_at_preH

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Parent.atJS_of_postH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.Parent.atJS_of_postH
