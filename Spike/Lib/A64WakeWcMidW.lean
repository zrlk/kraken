/-
**`wc_main`'s obligations past the box's store inside `SFactsSt2` at
`ownG`, their conjunction, and the clone's pc** (AArch64, the pre-spawn
consumer): the machine side of `A64WakeWcHat.wake_wc_mid_hatW`'s `hW`.

- `nodeW_and`, `blkW_and`, `reserveW_and`, `tcbWG_and`, `WcResW.and`,
  `WcSp3W.and`, `WcSp4W.and`, `WcMidW.and`: two node obligations combine (the
  conjunction of the two predicates) at the first's outside move `K`.
- `wcNS_cloneAt`, `wcNS_clonePc`: a state at the clone's `svc` (`wcNS`) is
  at `cloneAt pfxM exe`, i.e. `pcOf s = clonePc L`.
- `tcbWG_c0`, `wcSp3W_wcG`: the second TCB's call inside `SFactsSt2` at
  `ownG` (`Tcb2CallW.tcb2Call_ownG`, `tcb2W_ownGK` at the consumer's control,
  moved to any `c0`; the frame condition implies main's stack mapped).
- `wcResW_wcG`: the fence, the call block and the reserve
  (`fenceW_wcG`, `resBlW_wcG`, `reserveW_wcG`).
- `stackM_nil`, `wcMidW_wcG`: `WcMidW` at
  `SFactsSt2 Λ (PhRec.μ L) (ownG L (ntA L.lab))`, with `WcSp4W.wcSp4W_wcG` for
  `.sp4`, `wcSp3W_wcG`'s main's range the empty one (its `StackM` facts hold
  of every memory).

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeWcSp4W
import Spike.Lib.A64WakeWcResWI
import Spike.Lib.A64WakeTcb2CallW
import Spike.Lib.A64WakeWcMid
import Spike.Lib.A64WakeWcInv

namespace Spike.Lib.A64.Flow.WakeWc

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib
open Spike.Lib.A64.Flow (ND BlkW NodeW At AS)
open Spike.Lib.A64.WakePh.WcSp4 (wcNS)
open Spike.Lib.A64.Rt (TcbGG TcbWG)
open Spike.Lib.A64.Rt.Reserve (ResG ReserveW)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.WakePreA (cloneAt)

/-! ## Conjunction -/

section And

variable {W₁ W₂ : Frag isaLSE2} {K K₂ : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- Two facts at a node's states combine (the first's outside move). -/
theorem nodeW_and {n : ND} (h₁ : NodeW W₁ K exe endPc R F n) (h₂ : NodeW W₂ K₂ exe endPc R F n) :
    NodeW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F n :=
  fun s c hs => ⟨⟨(h₁ s c hs).1, (h₂ s c hs).1⟩, (h₁ s c hs).2⟩

/-- Two facts at a block node's states combine (the first's outside move). -/
theorem blkW_and {n : ND} {blk : List Directive} (h₁ : BlkW W₁ K exe endPc R F n blk)
    (h₂ : BlkW W₂ K₂ exe endPc R F n blk) : BlkW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F n blk :=
  fun s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
    ⟨⟨(h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1, (h₂ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1⟩,
      (h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).2⟩

/-- The reserve's node obligations combine. -/
theorem reserveW_and {q : ResG} {i : Spike.Lib.A64.Rt.Reserve.RN} (h₁ : ReserveW W₁ K exe endPc R F q i)
    (h₂ : ReserveW W₂ K₂ exe endPc R F q i) : ReserveW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F q i := by
  cases i <;> dsimp only [ReserveW] at h₁ h₂ ⊢ <;> first | exact blkW_and h₁ h₂ | exact nodeW_and h₁ h₂

/-- `scc_rt_alloc_tcb`'s node obligations combine. -/
theorem tcbWG_and {q : TcbGG} {i : Ret0.TN} (h₁ : TcbWG W₁ K exe endPc R F q i)
    (h₂ : TcbWG W₂ K₂ exe endPc R F q i) : TcbWG (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F q i := by
  cases i <;> dsimp only [TcbWG] at h₁ h₂ ⊢ <;> first | exact blkW_and h₁ h₂ | exact nodeW_and h₁ h₂

/-- **From the fence to `.sp3`**: two facts combine. -/
theorem WcResW.and {ms : MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h₁ : WcResW W₁ K exe endPc R F ms J0 S Q) (h₂ : WcResW W₂ K₂ exe endPc R F ms J0 S Q) :
    WcResW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F ms J0 S Q :=
  ⟨nodeW_and h₁.f h₂.f, blkW_and h₁.bl h₂.bl, fun g hg i => reserveW_and (h₁.res g hg i) (h₂.res g hg i)⟩

/-- **From `.sp3` to `.sp4`**: two facts combine. -/
theorem WcSp3W.and {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp3W W₁ K exe endPc R F c0 cA m fr) (h₂ : WcSp3W W₂ K₂ exe endPc R F c0 cA m fr) :
    WcSp3W (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 cA m fr :=
  ⟨blkW_and h₁.blk h₂.blk, fun g hg i => tcbWG_and (h₁.tcb g hg i) (h₂.tcb g hg i)⟩

/-- **From `.sp4` to the `svc`**: two facts combine. -/
theorem WcSp4W.and {F₂ : MachineData → Prop} {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp4W W₁ K exe endPc R F F₂ c0 t cA m fr) (h₂ : WcSp4W W₂ K₂ exe endPc R F F₂ c0 t cA m fr) :
    WcSp4W (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F F₂ c0 t cA m fr :=
  ⟨blkW_and h₁.n4 h₂.n4, nodeW_and h₁.n4s h₂.n4s, blkW_and h₁.n5 h₂.n5, nodeW_and h₁.nI h₂.nI,
    blkW_and h₁.n6 h₂.n6, nodeW_and h₁.n6f h₂.n6f, blkW_and h₁.n6a h₂.n6a⟩

/-- **From the box's store to the `svc`**: two facts combine at the first's
outside move (e.g. `wcMidW_wcG`'s `SFactsSt2` and the source side's). -/
theorem WcMidW.and {F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h₁ : WcMidW W₁ K exe endPc R F F₂ ms J0 S Q) (h₂ : WcMidW W₂ K₂ exe endPc R F F₂ ms J0 S Q) :
    WcMidW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F F₂ ms J0 S Q :=
  ⟨WcResW.and h₁.res h₂.res, fun c0 cA m fr hM => WcSp3W.and (h₁.sp3 c0 cA m fr hM) (h₂.sp3 c0 cA m fr hM),
    fun c0 cA m fr hM => WcSp4W.and (h₁.sp4 c0 cA m fr hM) (h₂.sp4 c0 cA m fr hM)⟩

end And

/-! ## The clone's pc -/

/-- **A state at the clone's `svc` is at `cloneAt pfxM exe`.** -/
theorem wcNS_cloneAt {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (h : At exe endPc R F (wcNS (_root_.Executable.labels exe).label c0 t k cA m fr) s c) :
    s.st.2 = cloneAt pfxM exe :=
  h.2.2.2.1

/-- **A state at the clone's `svc` has `pcOf s = clonePc L`** (`WakeOD.ClW`'s
first conjunct), in `L`'s executable. -/
theorem wcNS_clonePc {L : Spike.Lib.A64.Rt.RuntimeLayout} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (h : At L.exe endPc R F (wcNS L.lab c0 t k cA m fr) s c) : Scc.Sem.A64.pcOf s = clonePc L := by
  unfold Scc.Sem.A64.pcOf clonePc
  rw [wcNS_cloneAt h]

end Spike.Lib.A64.Flow.WakeWc

namespace Spike.Lib.A64.WakePh.WcMidWG

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Range)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout TcbGG TcbWG)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.Flow.Ret0 (StackM)
open Spike.Lib (Ctl)
open Spike.Lib.A64.WakePh.WcW (blkW_mapC nodeW_mapC)
open Spike.Lib.A64.WakePh.Tcb2Call (tcb2Q wcN3 tcb2Q_hdrA)
open Spike.Lib.A64.WakePh.Tcb2CallW (BandSp3 tcb2Call_ownG tcb2W_ownGK)
open Spike.Lib.A64.WakePh.WcSp4W (BandTi wcSp4W_wcG)
open Spike.Lib.A64.Flow.WakeWc (WcMidW WcResW WcSp3W WcSp4W rAR j3 t2)

/-- **A control-blind obligation of `scc_rt_alloc_tcb` at one source control
is one at any other** (`tcb2Q g c0'` to `tcb2Q g c0`). -/
theorem tcbWG_c0 {W : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop} (hW : ∀ s c c', W s c → W s c')
    {g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G} {c0 c0' : Ctl} {i : Spike.Lib.A64.Flow.Ret0.TN}
    (h : TcbWG W K exe endPc R F (tcb2Q g c0') i) : TcbWG W K exe endPc R F (tcb2Q g c0) i := by
  cases i <;> dsimp only [TcbWG] at h ⊢ <;>
    first
    | (refine blkW_mapC (n' := Spike.Lib.A64.Rt.tcbNG _ (tcb2Q g c0') _) rfl rfl h ?_
       rintro σ c ⟨-, hJ⟩
       exact ⟨c0', ⟨rfl, hJ⟩, fun s h => hW s _ _ h⟩)
    | (refine nodeW_mapC (n' := Spike.Lib.A64.Rt.tcbNG _ (tcb2Q g c0') _) rfl rfl h ?_
       rintro σ c ⟨-, hJ⟩
       exact ⟨c0', ⟨rfl, hJ⟩, fun s h => hW s _ _ h⟩)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The empty range is in private memory**: `StackM` at a range of size
`0` holds of every memory. -/
theorem stackM_nil (lo : Nat) (m : MachineData) : StackM ⟨lo, 0⟩ m :=
  fun _ _ h _ => absurd h (by simp [Range.contains])

section Inst

variable (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = Spike.Lib.A64.WakePh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`.sp3` to `.sp4` inside `SFactsSt2` at `ownG`**, for any source control
`c0` and frame words, at the outside move of any range `rK`. The frame
condition `F` keeps main's range `rS` mapped (`hFS`, after the take; `rS`
in the pool, `hsub`), the region's writes keep it (`hSM`, `hSMc`); main's
frame at `.sp3` is on a pool stack (`hb`); the counter `scc_rt_pinned_next`
and the header word `pinned + 96` are mapped and unmapped under `F`
(`hmP`, `hmH`, `hunP`, `hunH`), apart from the runtime's words (`hsep`,
`hhdr`). -/
theorem wcSp3W_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -272)
    (hhi : 0 ≤ R.hi) {rS : Range} (rK : Range) (hFS : ∀ m, F m → StackM rS m)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS))
    (hSMc : Spike.Lib.A64.Flow.FStable (R.callee (-80) (-192) 0) (StackM rS)) (hb : BandSp3 L R)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 80#64 + 16#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pinA + 96#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 96#64) 8 = none)
    (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) :
    WcSp3W (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rK)
      L.exe L.endPc R F c0 cA m fr := by
  have hFF : ∀ m, F m → F m ∧ StackM rS m := fun m h => ⟨h, hFS m h⟩
  have eH : ∀ g c, Spike.Lib.A64.Rt.hdrA L.lab (tcb2Q g c) = L.pinA + 96#64 := fun g c => by
    rw [tcb2Q_hdrA, L.lab_pin]
  obtain ⟨hRc, halc⟩ := Spike.Lib.A64.Flow.Ret0.Inst.callee_facts hR hal (kc := -80) (lo' := -192)
    (by omega) (by decide) (by omega) (by decide)
  refine ⟨?_, fun g hg i => ?_⟩
  · have h := tcb2Call_ownG hp hlo a hsite hΛ hlab (lbl := fun _ => none) (c0 := Spike.Lib.A64Consumer.c0)
      Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 (J := j3 cA m fr) hR hal (by omega) hhi hb (F := F) rK hsub hSM
    exact blkW_mapC (n' := wcN3 L.lab (j3 cA m fr) Spike.Lib.A64Consumer.c0) rfl rfl
      (Spike.Lib.A64.Flow.Ret0.blkW_mono h hFF) fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  · have h := tcb2W_ownGK hp hlo a rK hsite hΛ hlab hsep hhdr (lbl := fun _ => none)
      (c0 := Spike.Lib.A64Consumer.c0) Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hRc halc (Int.le_refl _)
      (Int.le_refl _) hb g hg (F := F) hmP (by rw [eH]; exact hmH) hunP (fun m h => by rw [eH]; exact hunH m h)
      hsub hSMc i
    exact tcbWG_c0 (fun _ _ _ h => h) (Spike.Lib.A64.Flow.WakeWc.tcbWG_mono h fun m h => hFF m h.1)

/-- **From the fence to `.sp3` inside `SFactsSt2` at `ownG`** (the owned
word `scc_rt_nthreads`), at the outside move of any range `rK`: the counter
apart from the runtime's words (`hsep`), mapped (`hmN`) and unmapped under
`F` (`hunN`). -/
theorem wcResW_wcG (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (rK : Range) {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hsep : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    WcResW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L (ntA L.lab)) s)
      (Spike.Lib.A64.PhRec.K L rK) L.exe L.endPc R F ms J0 S Q := by
  obtain ⟨hRc, halc⟩ := Spike.Lib.A64.Flow.Ret0.Inst.callee_facts hR hal (kc := -80) (lo' := -48)
    (by omega) (by decide) (by omega) (by decide)
  exact ⟨Spike.Lib.A64.WakePh.WcW.fenceW_wcG hp hlo hΛ hlab hsite (ntA L.lab),
    Spike.Lib.A64.WakePh.WcW.resBlW_wcG hp hlo hΛ hlab hsite (ntA L.lab) hR hal (by omega) hhi,
    fun g hg => Spike.Lib.A64.WakePh.WcW.reserveW_wcG hp hlo hΛ hlab hsite hsep hRc halc (Int.le_refl _)
      (Int.le_refl _) g hg hmN fun m h => hunN m h.1⟩

/-- **`wc_main` from the box's store to the `svc` inside `SFactsSt2` at
`ownG L (ntA L.lab)`** (the owned word the counter `scc_rt_nthreads`), at
the outside move of any range `rK`: `wcResW_wcG`, `wcSp3W_wcG` and
`WcSp4W.wcSp4W_wcG`. The premises are theirs, `wcSp3W_wcG`'s range `rS` the
empty range at the pool's base (`stackM_nil`: its `StackM` premises hold of
every memory, so none is asked): main's frame on a pool stack at both calls
(`hb`, `hband`), the counters' and header's words (`hsepN`,
`hmN`, `hunN`, `hsep`, `hhdr`, `hmP`, `hmH`, `hunP`, `hunH`) and the
second TCB's tid word (`htidW`). -/
theorem wcMidW_wcG (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (rK : Range) {F₂ : MachineData → Prop} {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hb : BandSp3 L R)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ ntA L.lab)
    (hhdr : L.pinA + 80#64 + 16#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pinA + 96#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 96#64) 8 = none)
    (hband : BandTi L R)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨t2 L.lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t2 L.lab + 56#64) 8 = none) ∧
      ∀ w, (⟨t2 L.lab + 56#64, 8⟩, w) ∉ Spike.Lib.A64.WakePh.own2a L (ntA L.lab) 0) :
    WcMidW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L (ntA L.lab)) s)
      (Spike.Lib.A64.PhRec.K L rK) L.exe L.endPc R F F₂ ms J0 S Q :=
  ⟨wcResW_wcG hp hlo hΛ hlab hsite hR hal (by omega) hhi rK hsepN hmN hunN,
    fun c0 cA m fr _ => wcSp3W_wcG hp hlo hΛ hlab hsite (ntA L.lab) hR hal (by omega) hhi
      (rS := ⟨Λ.stackPool.lo, 0⟩) rK (fun m _ => stackM_nil _ m) (by simp only [Range.Sub]; omega)
      (fun _ m' _ _ => stackM_nil _ m') (fun _ m' _ _ => stackM_nil _ m') hb hsep hhdr hmP hmH hunP hunH c0 cA m fr,
    fun _ _ _ _ _ => wcSp4W_wcG hp hlo hΛ hlab hsite (rS := rK) (ntA L.lab) hR hal (by omega) hhi hband htidW⟩

end Inst

end Spike.Lib.A64.WakePh.WcMidWG

/-- info: 'Spike.Lib.A64.Flow.WakeWc.WcMidW.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.WcMidW.and

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wcNS_clonePc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wcNS_clonePc

/-- info: 'Spike.Lib.A64.WakePh.WcMidWG.wcSp3W_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcMidWG.wcSp3W_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcMidWG.wcResW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcMidWG.wcResW_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcMidWG.stackM_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcMidWG.stackM_nil

/-- info: 'Spike.Lib.A64.WakePh.WcMidWG.wcMidW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcMidWG.wcMidW_wcG
