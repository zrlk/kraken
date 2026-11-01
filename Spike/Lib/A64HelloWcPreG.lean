/-
**hello.w's `WcPreWH` and `WcResWH` inside `SFactsSt2` at `ownGH`** (AArch64,
hTop; the twin of `Spike/Lib/A64WakeWcPreG.lean` at helloProg,
frame 144): the `SFactsSt2` component of the pre-spawn chain's `W` for
`wc_main` up to the allocator's return (`WcPreWH`) and from the fence to
`.sp3` (`WcResWH`), assembled from the per-node lemmas of `A64HelloWcPreWI`
and `A64HelloWcResWI` at the callees' regions (`wARH R`, `rARH R`).

`scc_rt_alloc`'s obligations at `ownGH` are `A64HelloAllocWI.allocW_wcGH`
(wake's `WcW.allocW_wcG`) at the return label `.L22_wc_main.sp0`.

- `wARH_ok`, `rARH_ok`: the callees' regions are regions, 16-aligned.
- `wcPreW_wcGH`: `WcPreWH` from the prologue's premises (`htp`, `hmr`, `hun`)
  and the allocator's (`hpool`, `hmp`, `hmem`, `hno`).
- `wcResW_wcGH`: `WcResWH` at the owned word the counter `scc_rt_nthreads`
  from the reserve's premises (`hsep`, `hmN`, `hunN`).
-/
import Spike.Lib.A64HelloWcResWI
import Spike.Lib.A64HelloAllocWI
import Spike.Lib.A64WakeWcPreG

namespace Spike.Lib.A64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Range)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64.Flow.HelloWc
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-! ## The callees' regions -/

/-- **The allocator's region at the call** is a region, 16-aligned, its
bounds `-160` and `0`. -/
theorem wARH_ok (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) :
    (wARH R).OK ∧ (wARH R).base.toNat % 16 = 0 := by
  have hb := Spike.Lib.Region.callee_base (hi' := 0) hR (show R.lo ≤ -144 + -160 by omega) (by decide)
    (show (-144 : Int) < R.hi by omega)
  refine ⟨Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_⟩
  have : (((wARH R).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **The reserve's region at the call** is a region, 16-aligned, its
bounds `-48` and `0`. -/
theorem rARH_ok (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) :
    (rARH R).OK ∧ (rARH R).base.toNat % 16 = 0 := by
  have hb := Spike.Lib.Region.callee_base (hi' := 0) hR (show R.lo ≤ -144 + -48 by omega) (by decide)
    (show (-144 : Int) < R.hi by omega)
  refine ⟨Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_⟩
  have : (((rARH R).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

section Inst

variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`WcPreWH` inside `SFactsSt2` at `ownGH`** (owned word `a`), none moved
by the take: `proW_wcGH` (the thread pointer `tp` at every entry state,
`htp`; its limit word mapped and unmapped, `hmr`, `hun`), `eW_wcGH`, and
`allocW_wcGH` at the allocator's region for every box allocation returning
to `.sp0` (the stack pool's base fits, `hpool`; the memory side's writable
words mapped, `hmp`; the counter and the headers unmapped under `F`, `hmem`,
and off the owned words, `hno`). -/
theorem wcPreW_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hpool : Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true l = true)
    (hmem : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j) :
    WcPreWH (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 J1 := by
  obtain ⟨hR', hal'⟩ := wARH_ok hR hal hRlo hhi
  refine ⟨proW_wcGH hp hlo hΛ hlab hsite a hR hal (by omega) hhi htp hmr hun,
    eW_wcGH hp hlo hΛ hlab hsite a hR hal hRlo hhi, fun q hq hra => ?_⟩
  exact allocW_wcGH hp hlo hΛ hlab hsite a hR' hal' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee])
    hpool (Or.inr rfl) hra (fun _ _ => hq.toS) hmp (fun w hw m hm => hmem q hq w hw m hm.1) (hno q hq)

/-- **`WcResWH` inside `SFactsSt2` at `ownGH`** (the owned word the counter
`scc_rt_nthreads`), none moved by the take: `fenceW_wcGH`, `resBlW_wcGH`, and
`reserveW_wcGH` at the reserve's region for every frame ghost returning to
`.sp3` (the counter apart from the runtime's words, `hsep`; mapped, `hmN`;
unmapped under `F`, `hunN`). -/
theorem wcResW_wcGH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop}
    (hsep : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    WcResWH (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ms J0 S Q := by
  obtain ⟨hR', hal'⟩ := rARH_ok hR hal hRlo hhi
  refine ⟨fenceW_wcGH hp hlo hΛ hlab hsite (ntA L.lab),
    resBlW_wcGH hp hlo hΛ hlab hsite (ntA L.lab) hR hal (by omega) hhi, fun g hra => ?_⟩
  exact reserveW_wcGH hp hlo hΛ hlab hsite hsep hR' hal' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) g hra hmN (fun m hm => hunN m hm.1)

end Inst

end Spike.Lib.A64.HelloPh.WcW

/-- info: 'Spike.Lib.A64.HelloPh.WcW.rARH_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.rARH_ok

/-- info: 'Spike.Lib.A64.HelloPh.WcW.wcPreW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.wcPreW_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.wcResW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.wcResW_wcGH
