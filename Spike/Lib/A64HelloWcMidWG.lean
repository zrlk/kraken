/-
**hello.w's `wc_main` obligations past the box's store inside `SFactsSt2` at `ownGH`** (AArch64,
5c): the twin of the `WcMidWG` part of `Spike/Lib/A64WakeWcMidW.lean` (`wcSp3W_wcG`, `wcResW_wcG`,
`wcMidW_wcG`) at hello's `WcMidWH` (`A64HelloWcMid`), from pieces:

- `.res`: `fenceW_wcGH`, `resBlW_wcGH`, `reserveW_wcGH` (`A64HelloWcPreWI`, `A64HelloWcResWI`);
- `.sp3`: `tcb2Call_ownGH`, `tcb2W_ownGKH` (`A64HelloTcb2CallW`) at the control `Consumer.c0`, moved to any `c0` by
  wake's `blkW_mapC` and `tcbWG_c0` (control-blind: `tcb2QH` agrees with `tcb2Q` up to the header);
- `.sp4`, `.sp6`: `wcSp4W_wcGH`, `wcSp6W_wcGH` (`A64HelloWcSp4W`).

Main's range `rS` of `tcb2Call_ownGH` and `tcb2W_ownGKH` is the empty range at the pool's base (wake's `stackM_nil`).
Hello's frame is 144 bytes, so the second TCB's callee region `R.callee (-144) (-192) 0` asks `R.lo ≤ -336`
(wake's: `-272`) and the reserve's `R.callee (-144) (-48) 0` asks `R.lo ≤ -192`.

- `tcbWG_c0H`: wake's `tcbWG_c0` at `tcb2QH`;
- `wcSp3W_wcGH`, `wcResW_wcGH`, `wcMidW_wcGH`.
-/
import Spike.Lib.A64HelloWcMidW
import Spike.Lib.A64HelloTcb2CallW
import Spike.Lib.A64HelloWcResWI
import Spike.Lib.A64HelloWcSp4W

namespace Spike.Lib.A64.HelloPh.WcMidWG

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Range)
open Spike.Lib.A64.Rt (RuntimeLayout TcbWG)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64.Flow.Ret0 (StackM)
open Spike.Lib (Ctl)
open Spike.Lib.A64.HelloPh
open Spike.Lib.A64.WakePh.WcW (blkW_mapC nodeW_mapC)
open Spike.Lib.A64.WakePh.WcMidWG (stackM_nil)
open Spike.Lib.A64.Flow.HelloWc (tcb2QH tcb2QH_hdrA wcN3H tH WcMidWH WcResWH WcSp3WH)
open Spike.Lib.A64.HelloPh.Tcb2CallW (BandSp3H tcb2Call_ownGH tcb2W_ownGKH)
open Spike.Lib.A64.HelloPh.WcSp4W (BandTiH wcSp4W_wcGH wcSp6W_wcGH)

/-- **A control-blind obligation of `scc_rt_alloc_tcb` at one source control
is one at any other** (`tcb2QH g c0'` to `tcb2QH g c0`): wake's `tcbWG_c0`
at hello's header. -/
theorem tcbWG_c0H {W : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop} (hW : ∀ s c c', W s c → W s c')
    {g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G} {c0 c0' : Ctl} {i : Spike.Lib.A64.Flow.Ret0.TN}
    (h : TcbWG W K exe endPc R F (tcb2QH g c0') i) : TcbWG W K exe endPc R F (tcb2QH g c0) i := by
  cases i <;> dsimp only [TcbWG] at h ⊢ <;>
    first
    | (refine blkW_mapC (n' := Spike.Lib.A64.Rt.tcbNG _ (tcb2QH g c0') _) rfl rfl h ?_
       rintro σ c ⟨-, hJ⟩
       exact ⟨c0', ⟨rfl, hJ⟩, fun s h => hW s _ _ h⟩)
    | (refine nodeW_mapC (n' := Spike.Lib.A64.Rt.tcbNG _ (tcb2QH g c0') _) rfl rfl h ?_
       rintro σ c ⟨-, hJ⟩
       exact ⟨c0', ⟨rfl, hJ⟩, fun s h => hW s _ _ h⟩)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {R : Spike.Lib.Region} {F : MachineData → Prop}

section Inst

variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`.sp3` to `.sp4` inside `SFactsSt2` at `ownGH`**, for any source
control `c0` and frame words, at the outside move of any range `rK`. The
frame condition `F` keeps main's range `rS` mapped (`hFS`, after the take;
`rS` in the pool, `hsub`), the region's writes keep it (`hSM`, `hSMc`);
main's frame at `.sp3` is on a pool stack (`hb`); the counter
`scc_rt_pinned_next` and the header word `pinned + 104` are mapped and
unmapped under `F` (`hmP`, `hmH`, `hunP`, `hunH`), apart from the runtime's
words (`hsep`, `hhdr`). -/
theorem wcSp3W_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -336)
    (hhi : 0 ≤ R.hi) {rS : Range} (rK : Range) (hFS : ∀ m, F m → StackM rS m)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS))
    (hSMc : Spike.Lib.A64.Flow.FStable (R.callee (-144) (-192) 0) (StackM rS)) (hb : BandSp3H L R)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 80#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pinA + 104#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 104#64) 8 = none)
    (c0 : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64)
    (fr : BitVec 64 × BitVec 64) :
    WcSp3WH (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rK)
      L.exe L.endPc R F c0 sl me cA fr := by
  have hFF : ∀ m, F m → F m ∧ StackM rS m := fun m h => ⟨h, hFS m h⟩
  have eH : ∀ g c, Spike.Lib.A64.Rt.hdrA L.lab (tcb2QH g c) = L.pinA + 104#64 := fun g c => by
    rw [tcb2QH_hdrA, L.lab_pin]
  obtain ⟨hRc, halc⟩ := Spike.Lib.A64.Flow.Ret0.Inst.callee_facts hR hal (kc := -144) (lo' := -192)
    (by omega) (by decide) (by omega) (by decide)
  refine ⟨?_, fun g hg i => ?_⟩
  · have h := tcb2Call_ownGH hp hlo a hsite hΛ hlab (lbl := fun _ => none) (c0 := Spike.Lib.A64Consumer.c0)
      Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 (sl := sl) (me := me) (cA := cA) (fr := fr) hR hal (by omega) hhi hb
      (F := F) rK hsub hSM
    exact blkW_mapC (n' := wcN3H L.lab Spike.Lib.A64Consumer.c0 sl me cA fr) rfl rfl
      (Spike.Lib.A64.Flow.Ret0.blkW_mono h hFF) fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  · have h := tcb2W_ownGKH hp hlo a rK hsite hΛ hlab hsep hhdr (lbl := fun _ => none)
      (c0 := Spike.Lib.A64Consumer.c0) Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hRc halc (Int.le_refl _)
      (Int.le_refl _) hb g hg (F := F) hmP (by rw [eH]; exact hmH) hunP (fun m h => by rw [eH]; exact hunH m h)
      hsub hSMc i
    exact tcbWG_c0H (fun _ _ _ h => h) (Spike.Lib.A64.Flow.WakeWc.tcbWG_mono h fun m h => hFF m h.1)

/-- **From the fence to `.sp3` inside `SFactsSt2` at `ownGH`** (the owned
word `scc_rt_nthreads`), at the outside move of any range `rK`: the counter
apart from the runtime's words (`hsep`), mapped (`hmN`) and unmapped under
`F` (`hunN`). -/
theorem wcResW_wcGH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (rK : Range) {ms : Spike.Lib.MemSide isaLSE2} {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hsep : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    WcResWH (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s)
      (Spike.Lib.A64.PhRec.K L rK) L.exe L.endPc R F ms J1 S Q := by
  obtain ⟨hRc, halc⟩ := Spike.Lib.A64.Flow.Ret0.Inst.callee_facts hR hal (kc := -144) (lo' := -48)
    (by omega) (by decide) (by omega) (by decide)
  exact ⟨Spike.Lib.A64.HelloPh.WcW.fenceW_wcGH hp hlo hΛ hlab hsite (rS := rK) (ntA L.lab),
    Spike.Lib.A64.HelloPh.WcW.resBlW_wcGH hp hlo hΛ hlab hsite (rS := rK) (ntA L.lab) hR hal (by omega) hhi,
    fun g hg => Spike.Lib.A64.HelloPh.WcW.reserveW_wcGH hp hlo hΛ hlab hsite (rS := rK) hsep hRc halc
      (Int.le_refl _) (Int.le_refl _) g hg hmN fun m h => hunN m h.1⟩

/-- **`wc_main` from the box's store to the `svc` inside `SFactsSt2` at
`ownGH L (ntA L.lab)`** (the owned word the counter `scc_rt_nthreads`), at
the outside move of any range `rK`: `wcResW_wcGH`, `wcSp3W_wcGH`,
`wcSp4W_wcGH` and `wcSp6W_wcGH`. The premises are theirs, `wcSp3W_wcGH`'s
range `rS` the empty range at the pool's base (`stackM_nil`: its `StackM`
premises hold of every memory, so none is asked): main's frame on a pool
stack at both calls (`hb`, `hband`), the counters' and header's words
(`hsepN`, `hmN`, `hunN`, `hsep`, `hhdr`, `hmP`, `hmH`, `hunP`, `hunH`) and
the second TCB's tid word (`htidW`). -/
theorem wcMidW_wcGH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (rK : Range) {F₂ : MachineData → Prop} {ms : Spike.Lib.MemSide isaLSE2}
    {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hb : BandSp3H L R)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ ntA L.lab)
    (hhdr : L.pinA + 80#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pinA + 104#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 104#64) 8 = none)
    (hband : BandTiH L R)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨tH L.lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none) ∧
      ∀ w, (⟨tH L.lab + 56#64, 8⟩, w) ∉ own2aH L (ntA L.lab) 0) :
    WcMidWH (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s)
      (Spike.Lib.A64.PhRec.K L rK) L.exe L.endPc R F F₂ ms J1 S Q :=
  ⟨wcResW_wcGH hp hlo hΛ hlab hsite hR hal (by omega) hhi rK hsepN hmN hunN,
    fun c0 sl me cA fr _ => wcSp3W_wcGH hp hlo hΛ hlab hsite (ntA L.lab) hR hal hRlo hhi
      (rS := ⟨Λ.stackPool.lo, 0⟩) rK (fun m _ => stackM_nil _ m) (by simp only [Range.Sub]; omega)
      (fun _ m' _ _ => stackM_nil _ m') (fun _ m' _ _ => stackM_nil _ m') hb hsep hhdr hmP hmH hunP hunH
      c0 sl me cA fr,
    fun _ _ _ _ _ _ => wcSp4W_wcGH hp hlo hΛ hlab hsite (rS := rK) (ntA L.lab) hR hal (by omega) hhi hband htidW,
    fun _ _ _ _ _ _ => wcSp6W_wcGH hp hlo hΛ hlab hsite (rS := rK) (ntA L.lab) hR hal (by omega) hhi⟩

end Inst

end Spike.Lib.A64.HelloPh.WcMidWG

/-- info: 'Spike.Lib.A64.HelloPh.WcMidWG.tcbWG_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcMidWG.tcbWG_c0H

/-- info: 'Spike.Lib.A64.HelloPh.WcMidWG.wcSp3W_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcMidWG.wcSp3W_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcMidWG.wcResW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcMidWG.wcResW_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcMidWG.wcMidW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcMidWG.wcMidW_wcGH
