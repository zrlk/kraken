/-
**hello.w's `wc_main` from the box's store to its `clone`'s `syscall` inside `SFactsSt2` at `ownGHXW`** (x86-64
only; the hello counterpart of `X64WakeOwnWcMidX`): `X64HelloWcMidWG`'s `WcMidWH` at `ownGHXW L (ntA L.lab)`, from
the `ownGHXW` producers:

- the reserve's call block and body (`OwnWc.resBlW_wcGHX`, `OwnRes.reserveW_wcGHX`; `rARH R`'s band from main's);
- `.x23`'s call and `scc_rt_alloc_tcb` (`OwnTcb2.tcb2Call_ownGXH`, `OwnTcb2.tcb2W_ownGXH`, at `X64Consumer.c0` and
  moved to any source control, `WcMidWG.tcbWG_c0H`; main's range the empty one, `stackM_nil`);
- `.x24` to the call (`OwnSp4.wcSp4W_wcGHX`) and `.x25` to the `syscall` (`OwnSp4.wcSp6W_wcGHX`), published at the
  `mfence`: the nodes up to the fence at `c0`, past it at `boxPubCtlH c0 ty l` (the state predicate is
  control-blind, so two instances of the same producer).

One band premise covers every frame: `hb : BandOnP L R (-320) 8`, main's frame `[-144, 8]`, the reserve's region
`rARH R = R.callee (-136) (-40) 8` (`[-176, -128]`), `scc_rt_alloc_tcb`'s `R.callee (-136) (-184) 8`
(`[-320, -128]`, `BandSp3H`) and `scc_rt_thread_init`'s entry (`BandTiH`).

- `bandResH`, `bandSp3H_of`: the bands from `hb`; `tidH_ne_tcbM`: the tid word off `tcbM`.
- `wcResW_wcGHX`, `wcSp3W_wcGHX`, `wcSp6PW_wcGHX`: the fields.
- `wcMidW_wcGHX`: the result.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. Against x86-64 wake's `OwnMid`: hello's frame is 128
bytes, so the band is `[-320, 8]` (wake `[-256, 8]`) and the reserve's region is `[-176, -128]` (wake
`[-112, -64]`); the reserve's field asks the base's 8-alignment `hR8` (as `WcW.wcResW_wcGH`); `.x24`'s and
`.x25`'s fields are separate (`WcMidWH.sp4`, `.sp6`; wake's single `WcSp4PW`); the header word is `pinned + 104`;
`wcSp3W_wcGHX` keeps `X64HelloWcMidWG`'s range premises (`hFS`, `hsub`, `hSM`, `hSMc`) and band `BandSp3H`; the
pnA separation is `hsepP` (`X64HelloWcMidWG`'s `hsep`), `hsep` being `PhRec.TcbSep`; the producers take `hW`
about the worker's word `tcbWH L` (`pinA + 144`).
-/
import Spike.Lib.X64HelloOwnWcSp4X
import Spike.Lib.X64HelloOwnWcPreX
import Spike.Lib.X64HelloOwnResX
import Spike.Lib.X64HelloOwnTcb2X
import Spike.Lib.X64HelloWcMidWG
import Spike.Lib.X64WakeOwnWcMidX

namespace Spike.Lib.X64.HelloPh.OwnMid

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64.Flow.Ret0 (StackM)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64.WakePh (tcbM BandOnP)
open Spike.Lib.X64.WakePh.OwnMid (bandOnP_mono)
open Spike.Lib.X64.WakePh.WcW (blkW_mapC)
open Spike.Lib.X64.WakePh.WcMidWG (stackM_nil)
open Spike.Lib.X64.Flow.WakeWc (tcbWG_mono)
open Spike.Lib.X64.Flow.HelloWc (tcb2QH tcb2QH_hdrA wcN3H tH WcMidWH WcResWH WcSp3WH WcSp4WH rARH)
open Spike.Lib.X64.HelloPh.WcSp6 (WcSp6PW)
open Spike.Lib.X64.HelloPh.Tcb2CallW (BandSp3H)
open Spike.Lib.X64.HelloPh.WcSp4W (BandTiH)
open Spike.Lib.X64.HelloPh.WcMidWG (tcbWG_c0H)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib (Region Ctl)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {R : Region} {F : MachineData → Prop} {rS : Range}

/-! ## The bands -/

/-- **The reserve's region on the pool**: `rARH R`'s `[-40, 8]` is `R`'s `[-176, -128]`. -/
theorem bandResH (hb : BandOnP L R (-176) (-128)) : BandOnP L (rARH R) (-40) 8 := fun k k1 k2 => by
  have := hb (-136 + k) (by omega) (by omega)
  rwa [Region.callee_addr]

/-- **`scc_rt_alloc_tcb`'s region on the pool** (`BandSp3H`): its `[-184, 8]` is `R`'s `[-320, -128]`. -/
theorem bandSp3H_of (hb : BandOnP L R (-320) (-128)) : BandSp3H L R := fun k k1 k2 => by
  have := hb (-136 + k) (by omega) (by omega)
  rwa [Region.callee_addr]

/-- **The second TCB's tid word is not `tcbM`**: `tH + 56 = pinA + 168`, `tcbM = pinA + 8`. -/
theorem tidH_ne_tcbM (L : RuntimeLayout) : tH L.lab + 56#64 ≠ tcbM L := by
  show Spike.Lib.X64.Flow.Ret0.pinA L.lab + 144#64 + 56#64 ≠ L.pinA + 8#64
  rw [L.lab_pin]
  bv_omega

/-! ## The fields -/

section Gen

variable {a : BitVec 64} (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlo hΛ hlab hsite hsep ha hW

/-- **`.x23` to `.x24` inside `SFactsSt2` at `ownGHXW`**, for any source control `c0` and frame words, at the
outside move of any range `rK`: `WcMidWG.wcSp3W_wcGH`'s premises (main's range `rS`, `hFS`, `hsub`, `hSM`,
`hSMc`; the band `hb`; the counter and header words `hsepP`, `hhdr`, `hmP`, `hmH`, `hunP`, `hunH`). -/
theorem wcSp3W_wcGHX (hR : R.OK) (hRlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi) {rS : Range}
    (rK : Range) (hFS : ∀ m, F m → StackM rS m)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hSMc : Spike.Lib.X64.FStable (R.callee (-136) (-184) 8) (StackM rS)) (hb : BandSp3H L R)
    (hsepP : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 112#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pinA + 136#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 136#64) 8 = none)
    (c0 : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64)
    (fr : BitVec 64 × BitVec 64) :
    WcSp3WH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rK)
      L.exe L.endPc R F c0 sl me cA fr := by
  have hFF : ∀ m, F m → F m ∧ StackM rS m := fun m h => ⟨h, hFS m h⟩
  have eH : ∀ g c, Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c) = L.pinA + 136#64 := fun g c => by
    rw [tcb2QH_hdrA, L.lab_pin]
  have hRc : (R.callee (-136) (-184) 8).OK :=
    Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  refine ⟨?_, fun g hg i => ?_⟩
  · have h := OwnTcb2.tcb2Call_ownGXH hp hlab hsite hsep ha hW hlo hΛ (lbl := fun _ => none)
      (c0 := Spike.Lib.X64Consumer.c0) Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 (sl := sl) (me := me) (cA := cA)
      (fr := fr) hR (by omega) hhi hb (F := F) rK hsub hSM
    exact blkW_mapC (n' := wcN3H L.lab Spike.Lib.X64Consumer.c0 sl me cA fr) rfl rfl
      (Spike.Lib.X64.Flow.Ret0.blkW_mono h hFF) fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  · have h := OwnTcb2.tcb2W_ownGXH hp hlab hsite hsep ha hW hlo rK hΛ hsepP hhdr (lbl := fun _ => none)
      (c0 := Spike.Lib.X64Consumer.c0) Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hRc (Int.le_refl _)
      (Int.le_refl _) hb g hg (F := F) hmP (by rw [eH]; exact hmH) hunP (fun m h => by rw [eH]; exact hunH m h)
      hsub hSMc i
    exact tcbWG_c0H (fun _ _ _ h => h) (tcbWG_mono h fun m h => hFF m h.1)

/-- **`.x25` to the `syscall` inside `SFactsSt2` at `ownGHXW`, publishing at the `mfence`**:
`OwnSp4.wcSp6W_wcGHX` at `c0` up to the fence and at the published control `c1` past it. -/
theorem wcSp6PW_wcGHX (hb : BandOnP L R (-144) 8) (hR : R.OK) (hRlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi)
    {c0 c1 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} :
    WcSp6PW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F c0 c1 t k sl me cA fr :=
  have h := OwnSp4.wcSp6W_wcGHX hp hlo hΛ hlab hsite hsep ha hW hb (rS := rS) (F := F) (c0 := c0) (t := t)
    (k := k) (sl := sl) (me := me) (cA := cA) (fr := fr) hR hRlo hhi
  have h' := OwnSp4.wcSp6W_wcGHX hp hlo hΛ hlab hsite hsep ha hW hb (rS := rS) (F := F) (c0 := c1) (t := t)
    (k := k) (sl := sl) (me := me) (cA := cA) (fr := fr) hR hRlo hhi
  ⟨h.n6, h.n6f, h'.n6a, h'.nd, h'.n10, h'.nr⟩

end Gen

section Nt

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ ntA L.lab)
  (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
include hp hlo hΛ hlab hsite hsep ha hW

/-- **The reserve's call and body inside `SFactsSt2` at `ownGHXW L (ntA L.lab)`** (the owned word the counter
`scc_rt_nthreads`): main's frame and the reserve's on the pool (`hb`); the counter apart from the runtime's words
(`hsepN`), mapped (`hmN`) and unmapped under `F` (`hunN`). -/
theorem wcResW_wcGHX (hb : BandOnP L R (-176) 8) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -176)
    (hhi : 16 ≤ R.hi) {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    WcResWH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L (ntA L.lab)) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ms J0 Q := by
  obtain ⟨hR', -⟩ := WcW.rARH_ok hR hR8 hRlo (by omega)
  refine ⟨OwnWc.resBlW_wcGHX hp hlo hΛ hlab hsite hsep ha hW (bandOnP_mono hb (by decide) (Int.le_refl _)) hR
    (by omega) hhi, fun g hra i => ?_⟩
  exact OwnRes.reserveW_wcGHX hp hlo hΛ hlab hsite hsep ha hW hsepN
    (bandResH (bandOnP_mono hb (Int.le_refl _) (by decide))) hR' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) g hra hmN (fun m hm => hunN m hm.1) i

/-- **`wc_main` from the box's store to the `syscall` inside `SFactsSt2` at `ownGHXW L (ntA L.lab)`**, at the
outside move of any range `rK`: `wcResW_wcGHX`, `wcSp3W_wcGHX`, `OwnSp4.wcSp4W_wcGHX` and `wcSp6PW_wcGHX`. The
premises are theirs: every frame on the pool (`hb`), `wcSp3W_wcGHX`'s range `rS` the empty range at the pool's
base (`stackM_nil`), the counters' and header's words (`hsepN`, `hmN`, `hunN`, `hsepP`, `hhdr`, `hmP`, `hmH`,
`hunP`, `hunH`), the second TCB's tid word (`htidW`; off `tcbM` by `tidH_ne_tcbM`). -/
theorem wcMidW_wcGHX (hb : BandOnP L R (-320) 8) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -320)
    (hhi : 16 ≤ R.hi) (rK : Range) {F₂ : MachineData → Prop} {ms : Spike.Lib.MemSide isa}
    {J1 : Spike.Lib.X64.AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hsepP : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ ntA L.lab)
    (hhdr : L.pinA + 112#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pinA + 136#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 136#64) 8 = none)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨tH L.lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none) ∧
      ∀ w, (⟨tH L.lab + 56#64, 8⟩, w) ∉ own2aH L (ntA L.lab) 0) :
    WcMidWH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L (ntA L.lab)) s)
      (Spike.Lib.X64.PhRec.K L rK) L.exe L.endPc R F F₂ ms J1 Q :=
  have hb1 : BandOnP L R (-144) 8 := bandOnP_mono hb (by decide) (Int.le_refl _)
  ⟨wcResW_wcGHX hp hlo hΛ hlab hsite hsep ha hW (bandOnP_mono hb (by decide) (Int.le_refl _)) hR hR8 (by omega)
      hhi hsepN hmN hunN,
    fun c0 sl me cA fr _ => wcSp3W_wcGHX hp hlo hΛ hlab hsite hsep ha hW hR hRlo hhi
      (rS := ⟨Λ.stackPool.lo, 0⟩) rK (fun m _ => stackM_nil _ m) (by simp only [Range.Sub]; omega)
      (fun _ m' _ _ => stackM_nil _ m') (fun _ m' _ _ => stackM_nil _ m')
      (bandSp3H_of (bandOnP_mono hb (Int.le_refl _) (by decide))) hsepP hhdr hmP hmH hunP hunH c0 sl me cA fr,
    fun _ _ _ _ _ _ => OwnSp4.wcSp4W_wcGHX hp hlo hΛ hlab hsite hsep ha hW hb1 (rS := rK) hR (by omega) hhi htidW
      (tidH_ne_tcbM L),
    fun _ _ _ _ _ _ _ _ => wcSp6PW_wcGHX hp hlo hΛ hlab hsite hsep ha hW hb1 hR (by omega) hhi⟩

end Nt

end Spike.Lib.X64.HelloPh.OwnMid

/-- info: 'Spike.Lib.X64.HelloPh.OwnMid.tidH_ne_tcbM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnMid.tidH_ne_tcbM

/-- info: 'Spike.Lib.X64.HelloPh.OwnMid.wcSp3W_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnMid.wcSp3W_wcGHX

/-- info: 'Spike.Lib.X64.HelloPh.OwnMid.wcSp6PW_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnMid.wcSp6PW_wcGHX

/-- info: 'Spike.Lib.X64.HelloPh.OwnMid.wcResW_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnMid.wcResW_wcGHX

/-- info: 'Spike.Lib.X64.HelloPh.OwnMid.wcMidW_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnMid.wcMidW_wcGHX
