/-
**hello.w's `WcPreWH` and `WcResWH` inside `SFactsSt2` at `ownGH`** (x86-64;
twin of `Spike/Lib/A64HelloWcPreG.lean`, the hello twin of `X64WakeWcPreG`
at `helloCells`, frame 128): the `SFactsSt2` component of the pre-spawn
chain's `W` for `wc_main` up to the allocator's return (`WcPreWH`) and from
the reserve's call block to `.x23` (`WcResWH`), assembled from the per-node
lemmas of `X64HelloWcPreWI` and `X64HelloWcResWI` at the callees' regions
(`wARH R`, `rARH R`).

`scc_rt_alloc`'s obligations at `ownGH` are `X64HelloAllocWI.allocW_wcGH`
at the return label `.Lwc_main.x0`.

- `wARH_ok`, `rARH_ok`: the callees' regions are regions, 8-aligned.
- `wcPreW_wcGH`: `WcPreWH` from the prologue's premises (`htp`, `hmr`,
  `hun`) and the allocator's (`hpool`, `hmp`, `hmem`, `hno`).
- `wcResW_wcGH`: `WcResWH` at the owned word the counter `scc_rt_nthreads`
  from the reserve's premises (`hsep`, `hmN`, `hunN`).

## Differences from the AArch64 version

As `X64WakeWcPreG` against AArch64 wake: no 16-alignment (the regions'
bases are 8-aligned, `hR8`); `call` pushes the return address, so the
callees' regions reach the cell above (`hi' = 8`: `wARH R = R.callee (-144)
(-160) 8`, `rARH R = R.callee (-136) (-40) 8`; AArch64's `hi' = 0`), and
`8 ≤ R.hi` at the entry block, `16 ≤ R.hi` at the reserve's call block
(`eW_wcGH`, `resBlW_wcGH`). The thread pointer is `fsBase` (`htp`). x86-64's
`WcResWH` has no fence node (scc's `# fence st` emits no code under TSO),
so there is no `fenceW_wcGH` and no `S`; the bounds are x86-64's frame
(`R.lo ≤ -304` for `WcPreWH`, `-176` for `WcResWH`).
-/
import Spike.Lib.X64HelloWcResWI
import Spike.Lib.X64HelloAllocWI
import Spike.Lib.X64HelloWcPreWI

namespace Spike.Lib.X64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64.Flow.HelloWc
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.HelloPh (lo)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-! ## The callees' regions -/

/-- **The allocator's region at the call** is a region, its base 8-aligned,
its bounds `-160` and `8`. -/
theorem wARH_ok (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi) :
    (wARH R).OK ∧ (wARH R).base.toNat % 8 = 0 := by
  have hb := Spike.Lib.Region.callee_base (hi' := 8) hR (show R.lo ≤ -144 + -160 by omega) (by decide)
    (show (-144 : Int) < R.hi by omega)
  refine ⟨Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_⟩
  have : (((wARH R).base.toNat : Int)) % 8 = 0 := by rw [hb]; omega
  omega

/-- **The reserve's region at the call** is a region, its base 8-aligned,
its bounds `-40` and `8`. -/
theorem rARH_ok (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -176) (hhi : 8 ≤ R.hi) :
    (rARH R).OK ∧ (rARH R).base.toNat % 8 = 0 := by
  have hb := Spike.Lib.Region.callee_base (hi' := 8) hR (show R.lo ≤ -136 + -40 by omega) (by decide)
    (show (-136 : Int) < R.hi by omega)
  refine ⟨Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_⟩
  have : (((rARH R).base.toNat : Int)) % 8 = 0 := by rw [hb]; omega
  omega

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`WcPreWH` inside `SFactsSt2` at `ownGH`** (owned word `a`), none moved
by the take: `proW_wcGH` (the thread pointer `tp` at every entry state,
`htp`; its limit word mapped and unmapped, `hmr`, `hun`), `eW_wcGH`, and
`allocW_wcGH` at the allocator's region for every box allocation returning
to `.x22` (the stack pool's base fits, `hpool`; the memory side's writable
words mapped, `hmp`; the counter and the headers unmapped under `F`, `hmem`,
and off the owned words, `hno`). -/
theorem wcPreW_wcGH (a : BitVec 64) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -304)
    (hhi : 8 ≤ R.hi) (hpool : Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa}
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true l = true)
    (hmem : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j) :
    WcPreWH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 J1 := by
  obtain ⟨hR', hR8'⟩ := wARH_ok hR hR8 hRlo hhi
  refine ⟨proW_wcGH hp hlo hΛ hlab hsite a hR (by omega) (by omega) htp hmr hun,
    eW_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi, fun q hq hra => ?_⟩
  exact allocW_wcGH hp hlo hΛ hlab hsite a hR' hR8' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee])
    hpool (Or.inr rfl) hra (fun _ _ => hq.toS) hmp (fun w hw m hm => hmem q hq w hw m hm.1) (hno q hq)

/-- **`WcResWH` inside `SFactsSt2` at `ownGH`** (the owned word the counter
`scc_rt_nthreads`), none moved by the take: `resBlW_wcGH` and
`reserveW_wcGH` at the reserve's region for every frame ghost returning to
`.x23` (the counter apart from the runtime's words, `hsep`; mapped, `hmN`;
unmapped under `F`, `hunN`). -/
theorem wcResW_wcGH (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -176) (hhi : 16 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop}
    (hsep : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    WcResWH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L (ntA L.lab)) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ms J0 Q := by
  obtain ⟨hR', -⟩ := rARH_ok hR hR8 hRlo (by omega)
  refine ⟨resBlW_wcGH hp hlo hΛ hlab hsite (ntA L.lab) hR (by omega) hhi, fun g hra i => ?_⟩
  exact reserveW_wcGH hp hlo hΛ hlab hsite hsep hR' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) g hra hmN (fun m hm => hunN m hm.1) i

end Inst

end Spike.Lib.X64.HelloPh.WcW

/-- info: 'Spike.Lib.X64.HelloPh.WcW.rARH_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.rARH_ok

/-- info: 'Spike.Lib.X64.HelloPh.WcW.wcPreW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.wcPreW_wcGH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.wcResW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.wcResW_wcGH
