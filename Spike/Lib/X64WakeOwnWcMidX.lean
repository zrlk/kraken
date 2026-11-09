/-
**`wc_main` from the box's store to its `clone`'s `syscall` inside
`SFactsSt2` at `ownGXW`** (x86-64; X64-OwnW Wc group): the
pre-spawn chain's `WcMidW` (`X64WakeWcMid`) at `ownGXW L (ntA L.lab)`, the
twin of AArch64's `WcMidWG.wcMidW_wcG` (`Spike/Lib/A64WakeWcMidW.lean`) at
the take-aware map, from the `ownGXW` producers:

- the reserve's call block and body (`OwnWc.resBlW_wcGX`,
  `OwnRes.reserveW_wcGX`; `rAR R`'s band from main's);
- `.x19`'s call and `scc_rt_alloc_tcb` (`OwnTcb2.tcb2Call_ownGX`,
  `OwnTcb2.tcb2W_ownGX`, at `X64Consumer.c0` and moved to any source control,
  `tcbWG_c0`; the private range the empty one, `stackM_nil`);
- `.x20` to the `syscall` (`OwnSp4.wcSp4W_wcGX`), published at the `mfence`:
  the nodes up to the fence at `c0`, past it at `boxPubCtl c0 ty l` (the
  state predicate is control-blind, so two instances of the same producer).

One band premise covers every frame: `hb : BandOnP L R (-256) 8`, main's
frame `[-80, 8]`, the reserve's region `rAR R = R.callee (-72) (-40) 8`
(`[-112, -64]`), `scc_rt_alloc_tcb`'s `R.callee (-72) (-184) 8`
(`[-256, -64]`, `BandSp3`) and `scc_rt_thread_init`'s entry (`BandTi`).
The depth `R.lo ≤ -256` is met by `wc_main`'s `wcD = 328`
(`X64WakeStartFacts`).

- `bandOnP_mono`, `bandRes`, `bandSp3`: the bands from `hb`.
- `wcResW_wcGX`, `wcSp3W_wcGX`, `wcSp4PW_wcGX`: the three fields.
- `wcMidW_wcGX`: the result.

**Deviations.** None: new lemmas. Besides `wcMidW_wcG`'s premises (AArch64's
`hband`, `hal` dropped: the band is `hb`'s, x86-64 needs no alignment), the
result takes `ownGXW`'s separation premises (`hsep`, `ha`, `hW`) and the
carried `htM : t2 + 56 ≠ tcbM L` (`wcSp4W_wcGX`'s).
-/
import Spike.Lib.X64WakeOwnWcSp4X
import Spike.Lib.X64WakeOwnWcPreX
import Spike.Lib.X64WakeOwnResX
import Spike.Lib.X64WakeOwnTcb2X
import Spike.Lib.X64WakeWcMidW

namespace Spike.Lib.X64.WakePh.OwnMid

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout hdrA)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64.Flow.WakeWc (WcMidW WcResW WcSp3W WcSp4PW rAR t2 j3 tcbWG_mono)
open Spike.Lib.X64.Flow.Ret0 (StackM)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64.WakePh.Tcb2Call (tcb2Q tcb2Q_hdrA wcN3)
open Spike.Lib.X64.WakePh.Tcb2CallW (BandSp3)
open Spike.Lib.X64.WakePh.WcW (blkW_mapC)
open Spike.Lib.X64.WakePh.WcMidWG (tcbWG_c0 stackM_nil)
open Spike.Lib.X64WakeBoxDefs (boxPubCtl)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {R : Region} {F : MachineData → Prop} {rS : Range}

/-! ## The bands -/

/-- A band at a wider range is one at a narrower. -/
theorem bandOnP_mono {lo hi lo' hi' : Int} (hb : BandOnP L R lo hi) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    BandOnP L R lo' hi' := fun k k1 k2 => hb k (by omega) (by omega)

/-- **The reserve's region on the pool**: `rAR R`'s `[-40, 8]` is `R`'s
`[-112, -64]`. -/
theorem bandRes (hb : BandOnP L R (-112) (-64)) : BandOnP L (rAR R) (-40) 8 := fun k k1 k2 => by
  have := hb (-72 + k) (by omega) (by omega)
  rwa [Region.callee_addr]

/-- **`scc_rt_alloc_tcb`'s region on the pool** (`BandSp3`): its `[-184, 8]`
is `R`'s `[-256, -64]`. -/
theorem bandSp3 (hb : BandOnP L R (-256) (-64)) : BandSp3 L R := fun k k1 k2 => by
  have := hb (-72 + k) (by omega) (by omega)
  rwa [Region.callee_addr]

/-! ## The fields -/

section Gen

variable {a : BitVec 64} (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlo hΛ hlab hsite hsep ha hW

/-- **`.x19` to `.x20` inside `SFactsSt2` at `ownGXW`**, for any source
control `c0` and frame words, at the outside move of any range `rK`: main's
frame and `scc_rt_alloc_tcb`'s on the pool (`hb`); the counter
`scc_rt_pinned_next` and the header word `pinned + 96` mapped and unmapped
under `F` (`hmP`, `hmH`, `hunP`, `hunH`), apart from the runtime's words
(`hsepP`, `hhdr`). -/
theorem wcSp3W_wcGX (hb : BandOnP L R (-256) 8) (hR : R.OK) (hRlo : R.lo ≤ -256) (hhi : 16 ≤ R.hi)
    (rK : Range)
    (hsepP : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 112#64 + 16#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pinA + 128#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 128#64) 8 = none)
    (c0 : Spike.Lib.Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) :
    WcSp3W (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L a) s) (Spike.Lib.X64.PhRec.K L rK)
      L.exe L.endPc R F c0 cA m fr := by
  have hFF : ∀ m, F m → F m ∧ StackM ⟨Λ.stackPool.lo, 0⟩ m := fun m h => ⟨h, stackM_nil _ m⟩
  have hsub : (⟨Λ.stackPool.lo, 0⟩ : Range).Sub Λ.stackPool := by simp only [Range.Sub]; omega
  have hSM : ∀ R' : Region, Spike.Lib.X64.FStable R' (StackM ⟨Λ.stackPool.lo, 0⟩) :=
    fun _ _ m' _ _ => stackM_nil _ m'
  have eH : ∀ g c, hdrA L.lab (tcb2Q g c) = L.pinA + 128#64 := fun g c => by
    rw [tcb2Q_hdrA, L.lab_pin]
  have hb3 := bandSp3 (bandOnP_mono hb (Int.le_refl _) (by decide))
  have hRc : (R.callee (-72) (-184) 8).OK :=
    Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  refine ⟨?_, fun g hg i => ?_⟩
  · have h := OwnTcb2.tcb2Call_ownGX hp hlab hsite hsep ha hW hlo hΛ (lbl := fun _ => none) (c0 := Spike.Lib.X64Consumer.c0)
      Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 (J := j3 cA m fr) hR (by omega) hhi hb3 (F := F) rK hsub (hSM R)
    exact blkW_mapC (n' := wcN3 L.lab (j3 cA m fr) Spike.Lib.X64Consumer.c0) rfl rfl
      (Spike.Lib.X64.Flow.Ret0.blkW_mono h hFF) fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  · have h := OwnTcb2.tcb2W_ownGX hp hlab hsite hsep ha hW hlo rK hΛ hsepP hhdr
      (lbl := fun _ => none) (c0 := Spike.Lib.X64Consumer.c0) Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hRc (Int.le_refl _)
      (Int.le_refl _) hb3 g hg (F := F) hmP (by rw [eH]; exact hmH) hunP
      (fun m h => by rw [eH]; exact hunH m h) hsub (hSM _) i
    exact tcbWG_c0 (fun _ _ _ h => h) (tcbWG_mono h fun m h => hFF m h.1)

/-- **`.x20` to the `syscall` inside `SFactsSt2` at `ownGXW`, publishing at
the `mfence`**: `OwnSp4.wcSp4W_wcGX` at `c0` up to the fence and at
`boxPubCtl c0 ty l` past it. -/
theorem wcSp4PW_wcGX (hb : BandOnP L R (-80) 8) (hR : R.OK) (hRlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi)
    {F₂ : MachineData → Prop} {c0 : Spike.Lib.Ctl} {ty : Ty} {l : WeakMem.AllocLabel} {t cA m : BitVec 64}
    {fr : BitVec 64 × BitVec 64}
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2a L a 0)
    (htM : t + 56#64 ≠ tcbM L) :
    WcSp4PW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F F₂ c0 ty l t cA m fr :=
  have h := OwnSp4.wcSp4W_wcGX hp hlo hΛ hlab hsite hsep ha hW hb hR hRlo hhi (rS := rS) (F₂ := F₂)
    (c0 := c0) (cA := cA) (m := m) (fr := fr) htidW htM
  have h' := OwnSp4.wcSp4W_wcGX hp hlo hΛ hlab hsite hsep ha hW hb hR hRlo hhi (rS := rS) (F₂ := F₂)
    (c0 := boxPubCtl c0 ty l) (cA := cA) (m := m) (fr := fr) htidW htM
  { toWcSp4PreW := h.toWcSp4PreW
    clone := ⟨h.clone.n21, h.clone.nf, h'.clone.na, h'.clone.nd, h'.clone.n10, h'.clone.nr⟩ }

end Gen

section Nt

variable (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ ntA L.lab)
  (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
include hp hlo hΛ hlab hsite hsep ha hW

/-- **The reserve's call to `.x19` inside `SFactsSt2` at `ownGXW L (ntA
L.lab)`** (the owned word the counter `scc_rt_nthreads`): main's frame and
the reserve's on the pool (`hb`); the counter apart from the runtime's
words (`hsepN`), mapped (`hmN`) and unmapped under `F` (`hunN`). -/
theorem wcResW_wcGX (hb : BandOnP L R (-112) 8) (hR : R.OK) (hRlo : R.lo ≤ -112) (hhi : 16 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop}
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    WcResW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L (ntA L.lab)) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ms J0 Q :=
  ⟨OwnWc.resBlW_wcGX hp hlo hΛ hlab hsite hsep ha hW (bandOnP_mono hb (by decide) (Int.le_refl _)) hR
      (by omega) hhi,
    fun g hg => OwnRes.reserveW_wcGX hp hlo hΛ hlab hsite hsep ha hW hsepN
      (bandRes (bandOnP_mono hb (Int.le_refl _) (by decide)))
      (Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)) (Int.le_refl _) (Int.le_refl _) g hg
      hmN fun m h => hunN m h.1⟩

/-- **`wc_main` from the box's store to the `syscall` inside `SFactsSt2` at
`ownGXW L (ntA L.lab)`**, at the outside move of any range `rK`:
`wcResW_wcGX`, `wcSp3W_wcGX` and `wcSp4PW_wcGX`. The premises are theirs:
every frame on the pool (`hb`), the counters' and header's words (`hsepN`,
`hmN`, `hunN`, `hsepP`, `hhdr`, `hmP`, `hmH`, `hunP`, `hunH`), the second
TCB's tid word (`htidW`, off `tcbM`: `htM`). -/
theorem wcMidW_wcGX (hb : BandOnP L R (-256) 8) (hR : R.OK) (hRlo : R.lo ≤ -256) (hhi : 16 ≤ R.hi)
    (rK : Range) {F₂ : MachineData → Prop} {ms : Spike.Lib.MemSide isa}
    {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop}
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hsepP : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ ntA L.lab)
    (hhdr : L.pinA + 112#64 + 16#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pinA + 128#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 128#64) 8 = none)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨t2 L.lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t2 L.lab + 56#64) 8 = none) ∧
      ∀ w, (⟨t2 L.lab + 56#64, 8⟩, w) ∉ own2a L (ntA L.lab) 0)
    (htM : t2 L.lab + 56#64 ≠ tcbM L) :
    WcMidW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L (ntA L.lab)) s)
      (Spike.Lib.X64.PhRec.K L rK) L.exe L.endPc R F F₂ ms J0 Q :=
  ⟨wcResW_wcGX hp hlo hΛ hlab hsite hsep ha hW (bandOnP_mono hb (by decide) (Int.le_refl _)) hR (by omega) hhi
      hsepN hmN hunN,
    fun c0 cA m fr _ => wcSp3W_wcGX hp hlo hΛ hlab hsite hsep ha hW hb hR hRlo hhi rK hsepP hhdr hmP hmH hunP
      hunH c0 cA m fr,
    fun _ _ _ _ _ _ _ => wcSp4PW_wcGX hp hlo hΛ hlab hsite hsep ha hW
      (bandOnP_mono hb (by decide) (Int.le_refl _)) hR (by omega) hhi htidW htM⟩

end Nt

end Spike.Lib.X64.WakePh.OwnMid

/-- info: 'Spike.Lib.X64.WakePh.OwnMid.wcSp3W_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnMid.wcSp3W_wcGX

/-- info: 'Spike.Lib.X64.WakePh.OwnMid.wcSp4PW_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnMid.wcSp4PW_wcGX

/-- info: 'Spike.Lib.X64.WakePh.OwnMid.wcResW_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnMid.wcResW_wcGX

/-- info: 'Spike.Lib.X64.WakePh.OwnMid.wcMidW_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnMid.wcMidW_wcGX
