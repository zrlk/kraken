/-
**`WcPreW` and `WcResW` inside `SFactsSt2` at `ownG`** (AArch64): the
`SFactsSt2` component of the pre-spawn chain's `W` for `wc_main` up to the
allocator's return (`WcPreW`) and from the fence to `.sp3` (`WcResW`),
assembled from the per-node lemmas of `A64WakeWcPreWI`, `A64WakeWcResWI`
and `A64WakeWcAllocWI` at the callees' regions (`wAR R`, `rAR R`).

- `wAR_ok`, `rAR_ok`: the callees' regions are regions, 16-aligned, their
  bounds multiples of 8.
- `wcPreW_wcG`: `WcPreW` from the prologue's premises (`htp`, `hmr`,
  `hun`) and the allocator's (`hpool`, `hmp`, `hmem`, `hno`) at every box
  allocation (`Call.OKB`).
- `wcResW_wcG`: `WcResW` at the owned word the counter `scc_rt_nthreads`
  from the reserve's premises (`hsep`, `hmN`, `hunN`).
-/
import Spike.Lib.A64WakeWcAllocWI

namespace Spike.Lib.A64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Range)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64.Flow.WakeWc
open Spike.Lib.A64.Alloc (Call)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-! ## The callees' regions -/

/-- **The allocator's region at the call** is a region, 16-aligned, its
bounds `-160` and `0`. -/
theorem wAR_ok (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi) :
    (wAR R).OK ∧ (wAR R).base.toNat % 16 = 0 := by
  have hb := Spike.Lib.Region.callee_base (hi' := 0) hR (show R.lo ≤ -80 + -160 by omega) (by decide)
    (show (-80 : Int) < R.hi by omega)
  refine ⟨Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_⟩
  have : (((wAR R).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **The reserve's region at the call** is a region, 16-aligned, its
bounds `-48` and `0`. -/
theorem rAR_ok (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) :
    (rAR R).OK ∧ (rAR R).base.toNat % 16 = 0 := by
  have hb := Spike.Lib.Region.callee_base (hi' := 0) hR (show R.lo ≤ -80 + -48 by omega) (by decide)
    (show (-80 : Int) < R.hi by omega)
  refine ⟨Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_⟩
  have : (((rAR R).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

section Inst

variable (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`WcPreW` inside `SFactsSt2` at `ownG`** (owned word `a`), none moved by
the take: `proW_wcG` (the thread pointer `tp` at every entry state, `htp`;
its limit word mapped and unmapped, `hmr`, `hun`), `eW_wcG`, and
`allocW_wcG` at the allocator's region for every box allocation returning
to `.sp0` (the stack pool's base fits, `hpool`; the memory side's writable
words mapped, `hmp`; the counter and the headers unmapped under `F`, `hmem`,
and off the owned words, `hno`). -/
theorem wcPreW_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -240)
    (hhi : 0 ≤ R.hi) (hpool : Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 Jc : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true l = true)
    (hmem : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownW L a j) :
    WcPreW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 Jc := by
  obtain ⟨hR', hal'⟩ := wAR_ok hR hal hRlo hhi
  refine ⟨proW_wcG hp hlo hΛ hlab hsite a hR hal (by omega) hhi htp hmr hun,
    eW_wcG hp hlo hΛ hlab hsite a hR hal hRlo hhi, fun q hq hra => ?_⟩
  exact allocW_wcG hp hlo hΛ hlab hsite a hR' hal' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee])
    hpool hra (fun _ _ => hq.toS) hmp (fun w hw m hm => hmem q hq w hw m hm.1) (hno q hq)

/-- **`WcResW` inside `SFactsSt2` at `ownG`** (the owned word the counter
`scc_rt_nthreads`), none moved by the take: `fenceW_wcG`, `resBlW_wcG`, and
`reserveW_wcG` at the reserve's region for every frame ghost returning to
`.sp3` (the counter apart from the runtime's words, `hsep`; mapped, `hmN`;
unmapped under `F`, `hunN`). -/
theorem wcResW_wcG (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop}
    (hsep : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    WcResW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L (ntA L.lab)) s)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ms J0 S Q := by
  obtain ⟨hR', hal'⟩ := rAR_ok hR hal hRlo hhi
  refine ⟨fenceW_wcG hp hlo hΛ hlab hsite (ntA L.lab),
    resBlW_wcG hp hlo hΛ hlab hsite (ntA L.lab) hR hal (by omega) hhi, fun g hra => ?_⟩
  exact reserveW_wcG hp hlo hΛ hlab hsite hsep hR' hal' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) g hra hmN (fun m hm => hunN m hm.1)

end Inst

end Spike.Lib.A64.WakePh.WcW

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.WakePh.WcW.wcPreW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.wcPreW_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcW.wcResW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.wcResW_wcG
