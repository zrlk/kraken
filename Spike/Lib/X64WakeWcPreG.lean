/-
**`WcPreW` and `WcResW` inside `SFactsSt2` at `ownG`** (x86-64; twin of
`Spike/Lib/A64WakeWcPreG.lean`): the `SFactsSt2` component of the
pre-spawn chain's `W` for `wc_main` up to the allocator's return (`WcPreW`)
and from the reserve's call block to `.x19` (`WcResW`), assembled from the
per-node lemmas of `X64WakeWcPreWI`, `X64WakeWcResWI` and
`X64WakeWcAllocWI` at the callees' regions (`wAR R`, `rAR R`).

- `wAR_ok`, `rAR_ok`: the callees' regions are regions, their bases
  8-aligned, their bounds multiples of 8.
- `wcPreW_wcG`: `WcPreW` from the prologue's premises (`htp`, `hmr`,
  `hun`) and the allocator's (`hpool`, `hmp`, `hmem`, `hno`) at every box
  allocation (`Call.OKB`).
- `wcResW_wcG`: `WcResW` at the owned word the counter `scc_rt_nthreads`
  from the reserve's premises (`hsep`, `hmN`, `hunN`).

**Unlike AArch64**: the regions' bases are 8-aligned (`hR8`), not
16-aligned (`hal`); the callees' regions are x86-64's (`wAR R =
R.callee (-80) (-160) 8`, `rAR R = R.callee (-72) (-40) 8`: the return
address cell above, A64's `hi = 0`), so `8 ≤ R.hi` at the entry block and
`16 ≤ R.hi` at the reserve's call block (`eW_wcG`, `resBlW_wcG`); the
thread pointer is `fsBase` (`htp`); `WcResW` has no fence node (x86-64's
`WcResW` is the call block and the reserve; the publication's `mfence` is
later, `X64WakeWcPub`).
-/
import Spike.Lib.X64WakeWcAllocWI

namespace Spike.Lib.X64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64.Flow.WakeWc
open Spike.Lib.X64.Alloc (Call)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-! ## The callees' regions -/

/-- **The allocator's region at the call** is a region, its base 8-aligned,
its bounds `-160` and `8`. -/
theorem wAR_ok (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi) :
    (wAR R).OK ∧ (wAR R).base.toNat % 8 = 0 := by
  have hb := Spike.Lib.Region.callee_base (hi' := 8) hR (show R.lo ≤ -80 + -160 by omega) (by decide)
    (show (-80 : Int) < R.hi by omega)
  refine ⟨Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_⟩
  have : (((wAR R).base.toNat : Int)) % 8 = 0 := by rw [hb]; omega
  omega

/-- **The reserve's region at the call** is a region, its base 8-aligned,
its bounds `-40` and `8`. -/
theorem rAR_ok (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -112) (hhi : 8 ≤ R.hi) :
    (rAR R).OK ∧ (rAR R).base.toNat % 8 = 0 := by
  have hb := Spike.Lib.Region.callee_base (hi' := 8) hR (show R.lo ≤ -72 + -40 by omega) (by decide)
    (show (-72 : Int) < R.hi by omega)
  refine ⟨Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_⟩
  have : (((rAR R).base.toNat : Int)) % 8 = 0 := by rw [hb]; omega
  omega

section Inst

variable (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`WcPreW` inside `SFactsSt2` at `ownG`** (owned word `a`), none moved by
the take: `proW_wcG` (the thread pointer `tp` at every entry state, `htp`;
its limit word mapped and unmapped, `hmr`, `hun`), `eW_wcG`, and
`allocW_wcG` at the allocator's region for every box allocation returning
to `.x18` (the stack pool's base fits, `hpool`; the memory side's writable
words mapped, `hmp`; the counter and the headers unmapped under `F`, `hmem`,
and off the owned words, `hno`). -/
theorem wcPreW_wcG (a : BitVec 64) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -240)
    (hhi : 8 ≤ R.hi) (hpool : Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa}
    {J0 Jc : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true l = true)
    (hmem : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownW L a j) :
    WcPreW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 Jc := by
  obtain ⟨hR', hR8'⟩ := wAR_ok hR hR8 hRlo hhi
  refine ⟨proW_wcG hp hlo hΛ hlab hsite a hR (by omega) (by omega) htp hmr hun,
    eW_wcG hp hlo hΛ hlab hsite a hR hRlo hhi, fun q hq hra => ?_⟩
  exact allocW_wcG hp hlo hΛ hlab hsite a hR' hR8' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee])
    hpool hra (fun _ _ => hq.toS) hmp (fun w hw m hm => hmem q hq w hw m hm.1) (hno q hq)

/-- **`WcResW` inside `SFactsSt2` at `ownG`** (the owned word the counter
`scc_rt_nthreads`), none moved by the take: `resBlW_wcG` and
`reserveW_wcG` at the reserve's region for every frame ghost returning to
`.x19` (the counter apart from the runtime's words, `hsep`; mapped, `hmN`;
unmapped under `F`, `hunN`). -/
theorem wcResW_wcG (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -112) (hhi : 16 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop}
    (hsep : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    WcResW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L (ntA L.lab)) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ms J0 Q := by
  obtain ⟨hR', -⟩ := rAR_ok hR hR8 hRlo (by omega)
  refine ⟨resBlW_wcG hp hlo hΛ hlab hsite (ntA L.lab) hR (by omega) hhi, fun g hra i => ?_⟩
  exact reserveW_wcG hp hlo hΛ hlab hsite hsep hR' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) g hra hmN (fun m hm => hunN m hm.1) i

end Inst

end Spike.Lib.X64.WakePh.WcW

/-- info: 'Spike.Lib.X64.WakePh.WcW.wcPreW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.wcPreW_wcG

/-- info: 'Spike.Lib.X64.WakePh.WcW.wcResW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.wcResW_wcG
