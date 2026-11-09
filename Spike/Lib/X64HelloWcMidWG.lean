/-
**hello.w's `wc_main` obligations past the box's store inside `SFactsSt2` at `ownGH` on x86-64** (the twin of
`Spike/Lib/A64HelloWcMidWG.lean`): hello's `WcMidWH` (`X64HelloWcMid`) at `ownGH L (ntA L.lab)`, from the pieces

- `.x22+18 .. .x23`: `WcW.wcResW_wcGH` (`X64HelloWcPreG`: the reserve's call block and body);
- `.x23`: `tcb2Call_ownGH`, `tcb2W_ownGKH` (`X64HelloTcb2CallW`) at the control `X64Consumer.c0`, moved to any
  `c0` by wake's `blkW_mapC` and `tcbWG_c0H` (control-blind: the obligations at `tcb2QH g c0'` are ones at
  `tcb2QH g c0`);
- `.x24`, `.x25`: `wcSp4W_wcGH`, `wcSp6W_wcGH` (`X64HelloWcSp4W`), `.x25`'s at the source `c0` up to the
  `mfence` and at the published `boxPubCtlH c0 ty l` past it.

Main's range `rS` of `tcb2Call_ownGH` and `tcb2W_ownGKH` is the empty range at the pool's base (wake's
`stackM_nil`). `scc_rt_alloc_tcb`'s region `R.callee (-136) (-184) 8` asks `R.lo ≤ -320`.

- `tcbWG_c0H`: wake's `tcbWG_c0` at `tcb2QH`;
- `wcSp3W_wcGH`: `.x23` to `.x24` (`WcSp3WH`);
- `wcSp6PW_wcGH`: `.x25` to the `syscall`, published at the `mfence` (`WcSp6PW`);
- `wcMidW_wcGH`: the result.

## Unlike AArch64

- No `hal`: x86-64's regions need no 16-byte alignment; the reserve's piece (`WcW.wcResW_wcGH`) takes the base's
  8-alignment `hR8` instead, and the depth is `R.lo ≤ -320` (A64's `-336`), the bounds `16 ≤ R.hi` (A64's `0`).
- There is no `WcMidWG.wcResW_wcGH`: x86-64's `WcResWH` has no fence node, so `X64HelloWcPreG`'s
  `WcW.wcResW_wcGH` is the reserve's field as it is.
- `.x25`'s field is `WcSp6PW` (the publication at the `mfence`), assembled by `wcSp6PW_wcGH` from two instances of
  `wcSp6W_wcGH` (A64: `WcSp6W` at `c0`, `wcSp6W_wcGH` directly); its frame condition is `F₂`.
- The header word is `pinned + 104` (`tcb2QH_hdrA`), the second call's block at `.Lwc_main.x1`.
-/
import Spike.Lib.X64HelloWcMidW
import Spike.Lib.X64HelloTcb2CallW
import Spike.Lib.X64HelloWcPreG
import Spike.Lib.X64HelloWcSp4W

namespace Spike.Lib.X64.HelloPh.WcMidWG

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout TcbWG)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64.Flow.Ret0 (StackM)
open Spike.Lib (Ctl)
open Spike.Lib.X64.HelloPh
open Spike.Lib.X64.WakePh.WcW (blkW_mapC nodeW_mapC)
open Spike.Lib.X64.WakePh.WcMidWG (stackM_nil)
open Spike.Lib.X64.Flow.WakeWc (tcbWG_mono)
open Spike.Lib.X64.Flow.HelloWc (tcb2QH tcb2QH_hdrA wcN3H tH WcMidWH WcResWH WcSp3WH)
open Spike.Lib.X64.HelloPh.WcSp6 (WcSp6PW)
open Spike.Lib.X64HelloMainPreSrc (boxPubCtlH)
open Spike.Lib.X64.HelloPh.Tcb2CallW (BandSp3H tcb2Call_ownGH tcb2W_ownGKH)
open Spike.Lib.X64.HelloPh.WcSp4W (BandTiH wcSp4W_wcGH wcSp6W_wcGH)

/-- **A control-blind obligation of `scc_rt_alloc_tcb` at one source control
is one at any other** (`tcb2QH g c0'` to `tcb2QH g c0`): wake's `tcbWG_c0`
at hello's header. -/
theorem tcbWG_c0H {W : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop} (hW : ∀ s c c', W s c → W s c')
    {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G} {c0 c0' : Ctl} {i : Spike.Lib.X64.Flow.Ret0.TN}
    (h : TcbWG W K exe endPc R F (tcb2QH g c0') i) : TcbWG W K exe endPc R F (tcb2QH g c0) i := by
  cases i <;> dsimp only [TcbWG] at h ⊢ <;>
    first
    | (refine blkW_mapC (n' := Spike.Lib.X64.Rt.tcbNG _ (tcb2QH g c0') _) rfl rfl h ?_
       rintro σ c ⟨-, hJ⟩
       exact ⟨c0', ⟨rfl, hJ⟩, fun s h => hW s _ _ h⟩)
    | (refine nodeW_mapC (n' := Spike.Lib.X64.Rt.tcbNG _ (tcb2QH g c0') _) rfl rfl h ?_
       rintro σ c ⟨-, hJ⟩
       exact ⟨c0', ⟨rfl, hJ⟩, fun s h => hW s _ _ h⟩)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {R : Spike.Lib.Region} {F : MachineData → Prop}

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`.x23` to `.x24` inside `SFactsSt2` at `ownGH`**, for any source
control `c0` and frame words, at the outside move of any range `rK`. The
frame condition `F` keeps main's range `rS` mapped (`hFS`, after the take;
`rS` in the pool, `hsub`), the region's writes keep it (`hSM`, `hSMc`);
main's frame at `.x23` is on a pool stack (`hb`); the counter
`scc_rt_pinned_next` and the header word `pinned + 104` are mapped and
unmapped under `F` (`hmP`, `hmH`, `hunP`, `hunH`), apart from the runtime's
words (`hsep`, `hhdr`). -/
theorem wcSp3W_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi) {rS : Range}
    (rK : Range) (hFS : ∀ m, F m → StackM rS m)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hSMc : Spike.Lib.X64.FStable (R.callee (-136) (-184) 8) (StackM rS)) (hb : BandSp3H L R)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 112#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pinA + 136#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 136#64) 8 = none)
    (c0 : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64)
    (fr : BitVec 64 × BitVec 64) :
    WcSp3WH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rK)
      L.exe L.endPc R F c0 sl me cA fr := by
  have hFF : ∀ m, F m → F m ∧ StackM rS m := fun m h => ⟨h, hFS m h⟩
  have eH : ∀ g c, Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c) = L.pinA + 136#64 := fun g c => by
    rw [tcb2QH_hdrA, L.lab_pin]
  have hRc : (R.callee (-136) (-184) 8).OK :=
    Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  refine ⟨?_, fun g hg i => ?_⟩
  · have h := tcb2Call_ownGH hp hlo a hsite hΛ hlab (lbl := fun _ => none) (c0 := Spike.Lib.X64Consumer.c0)
      Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 (sl := sl) (me := me) (cA := cA) (fr := fr) hR (by omega) hhi hb
      (F := F) rK hsub hSM
    exact blkW_mapC (n' := wcN3H L.lab Spike.Lib.X64Consumer.c0 sl me cA fr) rfl rfl
      (Spike.Lib.X64.Flow.Ret0.blkW_mono h hFF) fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  · have h := tcb2W_ownGKH hp hlo a rK hsite hΛ hlab hsep hhdr (lbl := fun _ => none)
      (c0 := Spike.Lib.X64Consumer.c0) Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hRc (Int.le_refl _)
      (Int.le_refl _) hb g hg (F := F) hmP (by rw [eH]; exact hmH) hunP (fun m h => by rw [eH]; exact hunH m h)
      hsub hSMc i
    exact tcbWG_c0H (fun _ _ _ h => h) (tcbWG_mono h fun m h => hFF m h.1)

/-- **`.x25` to the `syscall` inside `SFactsSt2` at `ownGH`, publishing at
the `mfence`**: `wcSp6W_wcGH` at `c0` up to the fence and at the published
control `c1` past it (the state predicate is control-blind, so two instances
of the same producer). -/
theorem wcSp6PW_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) {rS : Range}
    {c0 c1 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} :
    WcSp6PW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F c0 c1 t k sl me cA fr :=
  have h := wcSp6W_wcGH hp hlo hΛ hlab hsite (rS := rS) (F := F) (c0 := c0) (t := t) (k := k) (sl := sl)
    (me := me) (cA := cA) (fr := fr) a hR hRlo hhi
  have h' := wcSp6W_wcGH hp hlo hΛ hlab hsite (rS := rS) (F := F) (c0 := c1) (t := t) (k := k) (sl := sl)
    (me := me) (cA := cA) (fr := fr) a hR hRlo hhi
  ⟨h.n6, h.n6f, h'.n6a, h'.nd, h'.n10, h'.nr⟩

/-- **`wc_main` from the box's store to the `syscall` inside `SFactsSt2` at
`ownGH L (ntA L.lab)`** (the owned word the counter `scc_rt_nthreads`), at
the outside move of any range `rK`: `WcW.wcResW_wcGH`, `wcSp3W_wcGH`,
`wcSp4W_wcGH` and `wcSp6PW_wcGH`. The premises are theirs, `wcSp3W_wcGH`'s
range `rS` the empty range at the pool's base (`stackM_nil`: its `StackM`
premises hold of every memory, so none is asked): main's frame on a pool
stack at both calls (`hb`, `hband`), the counters' and header's words
(`hsepN`, `hmN`, `hunN`, `hsep`, `hhdr`, `hmP`, `hmH`, `hunP`, `hunH`) and
the second TCB's tid word (`htidW`). -/
theorem wcMidW_wcGH (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (rK : Range) {F₂ : MachineData → Prop} {ms : Spike.Lib.MemSide isa}
    {J1 : Spike.Lib.X64.AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hb : BandSp3H L R)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ ntA L.lab)
    (hhdr : L.pinA + 112#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pinA + 136#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 136#64) 8 = none)
    (hband : BandTiH L R)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨tH L.lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none) ∧
      ∀ w, (⟨tH L.lab + 56#64, 8⟩, w) ∉ own2aH L (ntA L.lab) 0) :
    WcMidWH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L (ntA L.lab)) s)
      (Spike.Lib.X64.PhRec.K L rK) L.exe L.endPc R F F₂ ms J1 Q :=
  ⟨WcW.wcResW_wcGH hp hlo hΛ hlab hsite (rS := rK) hR hR8 (by omega) hhi hsepN hmN hunN,
    fun c0 sl me cA fr _ => wcSp3W_wcGH hp hlo hΛ hlab hsite (ntA L.lab) hR hRlo hhi
      (rS := ⟨Λ.stackPool.lo, 0⟩) rK (fun m _ => stackM_nil _ m) (by simp only [Range.Sub]; omega)
      (fun _ m' _ _ => stackM_nil _ m') (fun _ m' _ _ => stackM_nil _ m') hb hsep hhdr hmP hmH hunP hunH
      c0 sl me cA fr,
    fun _ _ _ _ _ _ => wcSp4W_wcGH hp hlo hΛ hlab hsite (rS := rK) (ntA L.lab) hR (by omega) hhi hband htidW,
    fun _ _ _ _ _ _ _ _ => wcSp6PW_wcGH hp hlo hΛ hlab hsite (ntA L.lab) hR (by omega) hhi⟩

end Inst

end Spike.Lib.X64.HelloPh.WcMidWG

/-- info: 'Spike.Lib.X64.HelloPh.WcMidWG.tcbWG_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcMidWG.tcbWG_c0H

/-- info: 'Spike.Lib.X64.HelloPh.WcMidWG.wcSp3W_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcMidWG.wcSp3W_wcGH

/-- info: 'Spike.Lib.X64.HelloPh.WcMidWG.wcSp6PW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcMidWG.wcSp6PW_wcGH

/-- info: 'Spike.Lib.X64.HelloPh.WcMidWG.wcMidW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcMidWG.wcMidW_wcGH
